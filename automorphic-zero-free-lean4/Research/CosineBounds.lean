import Research.CosineResolvent
import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact rational ceilings for the normalized cosine Rayleigh test.
An elementary derivative bounds arctan uniformly by its 21st Taylor polynomial. -/
namespace ERH.CosineBounds
open Real ERH.CosineResolvent
noncomputable section

def upper (x : ℝ) : ℝ := x^1/1-x^3/3+x^5/5-x^7/7+x^9/9-x^11/11+x^13/13-x^15/15+x^17/17-x^19/19+x^21/21

theorem arctan_upper {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ upper x := by
  have D (x : ℝ) : HasDerivAt (fun t => upper t - arctan t) (x^22/(1+x^2)) x := by
    have h0 := (((hasDerivAt_id x).pow 1).div_const (1:ℝ))
    have h1 := (((hasDerivAt_id x).pow 3).div_const (3:ℝ))
    have h2 := (((hasDerivAt_id x).pow 5).div_const (5:ℝ))
    have h3 := (((hasDerivAt_id x).pow 7).div_const (7:ℝ))
    have h4 := (((hasDerivAt_id x).pow 9).div_const (9:ℝ))
    have h5 := (((hasDerivAt_id x).pow 11).div_const (11:ℝ))
    have h6 := (((hasDerivAt_id x).pow 13).div_const (13:ℝ))
    have h7 := (((hasDerivAt_id x).pow 15).div_const (15:ℝ))
    have h8 := (((hasDerivAt_id x).pow 17).div_const (17:ℝ))
    have h9 := (((hasDerivAt_id x).pow 19).div_const (19:ℝ))
    have h10 := (((hasDerivAt_id x).pow 21).div_const (21:ℝ))
    have h := ((((((((((h0.sub h1).add h2).sub h3).add h4).sub h5).add h6).sub h7).add h8).sub h9).add h10).sub (Real.hasDerivAt_arctan x)
    convert h using 1
    · rfl
    · dsimp
      field_simp
      ring
  have H := monotone_of_hasDerivAt_nonneg D (fun z => by positivity)
  have h := H hx
  simpa [upper] using h

/-- A sufficient finite arithmetic test for the admissible pole at the chosen
rational frequency. The global optimizer is unnecessary for verifying this bound. -/
theorem certify {k p : ℝ} (hk : 0 < k) (hp : 0 ≤ p)
    (h : p*(1+k^2)*(k+3.14159265358979323847/2+upper k⁻¹) ≤ k^3) :
    p ≤ load k (edge k) := by
  have h1 := arctan_upper (inv_pos.mpr hk).le
  rw [Real.arctan_inv_of_pos hk] at h1
  have h2 : π-arctan k ≤ 3.14159265358979323847/2+upper k⁻¹ := by
    linarith [Real.pi_lt_d20]
  have h3 := mul_le_mul_of_nonneg_left (add_le_add_left h2 k) (by positivity : 0 ≤ p*(1+k^2))
  have h4 : p*(1+k^2)*(k+(π-arctan k)) ≤ k^3 := by nlinarith only [h3,h]
  have h5 : 0 < 1+edge k := by linarith [edge_pos hk]
  apply (le_div_iff₀ h5).mpr
  unfold gain edge
  have hn : 0 < 1+k^2 := by positivity
  field_simp
  nlinarith

/-- Domination of the chosen pole by the exact load gives a lower bound on the
true exponential interaction energy of the compact cosine profile. -/
theorem rayleigh_lower {k p : ℝ} (hk : 0 < k) (hp : p ≤ load k (edge k)) :
    2*gain k*(∫ x in -edge k..edge k, profile k (edge k) x^2) ≤
      (∫ x in -edge k..edge k, profile k (edge k) x*resolvent k (edge k) x) -
        p*(∫ x in -edge k..edge k, profile k (edge k) x)^2 := by
  let S := edge k
  let M := ∫ x in -S..S, profile k S x
  let A := ∫ x in -S..S, profile k S x^2
  have hcont : Continuous (fun x => profile k S x) := by unfold profile; fun_prop
  have hden : (∫ x in -S..S, profile k S x*resolvent k S x) =
      2*gain k*A + (load k S*M)*M := by
    calc
      _ = ∫ x in -S..S, ((2*gain k)*(profile k S x)^2 + (load k S*M)*profile k S x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by dsimp [S]; linarith [edge_pos hk] : -S ≤ S)] at hx
        have h := rayleigh_density hk x hx
        change resolvent k S x - load k S*M = 2*gain k*profile k S x at h
        dsimp only
        rw [sub_eq_iff_eq_add.mp h]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change 2*gain k*A ≤ (∫ x in -S..S, profile k S x*resolvent k S x) - p*M^2
  rw [hden]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg M)]

theorem quartic :
    (10521/22436:ℝ) ≤ load (24031249/10000000) (edge (24031249/10000000)) ∧
    (101085917/110587044:ℝ)*(1+(24031249/10000000)^2) < 6192932/1000000 := by
  constructor
  · apply certify (by norm_num) (by norm_num)
    norm_num [upper]
  · norm_num

theorem octic :
    (470377/1000000:ℝ) ≤ load (241209645/100000000) (edge (241209645/100000000)) ∧
    (85398805176211663/94275997200000000:ℝ)*(1+(241209645/100000000)^2) < 6176195/1000000 := by
  constructor
  · apply certify (by norm_num) (by norm_num)
    norm_num [upper]
  · norm_num

theorem degree_twenty :
    (473580/1000000:ℝ) ≤ load (24321594/10000000) (edge (24321594/10000000)) ∧
    (219852918901/246450000000:ℝ)*(1+(24321594/10000000)^2) < 6169084/1000000 := by
  constructor
  · apply certify (by norm_num) (by norm_num)
    norm_num [upper]
  · norm_num

end
end ERH.CosineBounds
