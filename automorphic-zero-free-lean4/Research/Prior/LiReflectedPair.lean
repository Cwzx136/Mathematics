import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Reflected-pair estimates for the real part of a Li coefficient.
The final theorem assumes the strip, horizontal reflection, summability, and the finite-height verification. The geometric estimates are proved below. -/
namespace LiReflectedPair
open Real Set

/-- The product `cosh x * cos x` decreases strictly on the first half-period. -/
theorem edge_strictAnti : StrictAntiOn (fun x : ℝ => cosh x * cos x) (Icc 0 π) := by
  let q : ℝ → ℝ := fun x => sinh x * cos x - cosh x * sin x
  have dq (x : ℝ) : HasDerivAt q (-2 * sinh x * sin x) x := by
    convert (((hasDerivAt_sinh x).mul (hasDerivAt_cos x)).sub
      ((hasDerivAt_cosh x).mul (hasDerivAt_sin x))) using 1; first | rfl | ring
  have dg (x : ℝ) : HasDerivAt (fun t : ℝ => cosh t * cos t) (q x) x := by
    convert ((hasDerivAt_cosh x).mul (hasDerivAt_cos x)) using 1; first | rfl | (dsimp [q]; ring)
  have qar : StrictAntiOn q (Icc 0 π) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 π) (fun x _ => (dq x).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    rw [(dq x).deriv]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (sinh_pos_iff.mpr hx.1))
      (sin_pos_of_pos_of_lt_pi hx.1 hx.2)
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 π) (fun x _ => (dg x).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  rw [(dg x).deriv]
  have h := qar (show (0 : ℝ) ∈ Icc 0 π from ⟨le_rfl, pi_pos.le⟩) ⟨hx.1.le, hx.2.le⟩ hx.1
  simpa [q] using h

/-- For a phase `x` on the first half-period, the real product is below one even
when the signed log-modulus is as large in absolute value as the phase. -/
theorem edge {x v : ℝ} (hx : 0 < x) (hπ : x ≤ π) (hv : |v| ≤ x) :
    cosh v * cos x < 1 := by
  by_cases hc : 0 ≤ cos x
  · have hle : cosh v ≤ cosh x := cosh_le_cosh.mpr (by simpa [abs_of_pos hx] using hv)
    have hs := edge_strictAnti (show (0 : ℝ) ∈ Icc 0 π from ⟨le_rfl, pi_pos.le⟩) ⟨hx.le,hπ⟩ hx
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hc) (by simpa using hs)
  · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (cosh_pos v).le (le_of_not_ge hc)) zero_lt_one

/-- The two endpoint gaps control the entire open period. -/
theorem circle {x v : ℝ} (hx : 0 < x) (hp : x < 2 * π)
    (hleft : |v| ≤ x) (hright : |v| ≤ 2 * π - x) : cosh v * cos x < 1 := by
  by_cases h : x ≤ π
  · exact edge hx h hleft
  · simpa only [cos_two_pi_sub] using
      (edge (sub_pos.mpr hp) (by linarith : 2 * π - x ≤ π) hright)

/-- The paper's linear cutoff, for either sign of the log modulus. In fact every
individual averaged pair beyond the verified strip has strictly positive contribution. -/
theorem high_pair {m T g θ u : ℝ} (hT : 1 ≤ T) (hg : T ≤ g) (hm : 0 < m)
    (hcap : m ≤ 2 * π * T - π) (hlo : g / (1 + g^2) ≤ θ)
    (hhi : θ ≤ 1 / g) (hu : |u| ≤ 1 / (2*g^2)) :
    0 < 1 - cosh (m*u) * cos (m*θ) := by
  have hg1 : 1 ≤ g := hT.trans hg
  have gpos : 0 < g := lt_of_lt_of_le zero_lt_one hg1
  have dpos : 0 < 2*g^2 := by positivity
  have ypos : 0 < 1+g^2 := by positivity
  have lbound : 1/(2*g^2) ≤ g/(1+g^2) := by
    apply (div_le_div_iff₀ dpos ypos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hg1) (sq_nonneg g),
      mul_nonneg (sub_nonneg.mpr hg1) (show 0 ≤ g+1 by linarith)]
  have ht : 0 < θ := (div_pos gpos ypos).trans_le hlo
  have hmg : m ≤ 2*π*g-π := by
    nlinarith [mul_nonneg pi_pos.le (sub_nonneg.mpr hg)]
  have hsum : m/g + m/(2*g^2) < 2*π := by
    have hp := mul_le_mul_of_nonneg_right hmg (show 0 ≤ 2*g+1 by linarith)
    field_simp
    nlinarith [pi_pos]
  have habs : |m*u| ≤ m/(2*g^2) := by
    rw [abs_mul, abs_of_pos hm]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hu hm.le
  have hθ : m*θ ≤ m/g := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hhi hm.le
  have hl : |m*u| ≤ m*θ := by
    rw [abs_mul, abs_of_pos hm]
    exact mul_le_mul_of_nonneg_left (hu.trans (lbound.trans hlo)) hm.le
  have hp : m*θ < 2*π := by linarith [abs_nonneg (m*u)]
  have hr : |m*u| ≤ 2*π-m*θ := by linarith
  exact sub_pos.mpr (circle (mul_pos hm ht) hp hl hr)

/-- The elementary angular contribution of a real segment of length `s` at height `g`. -/
theorem slice_bounds {g s : ℝ} (hg : 0 < g) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    g*s/(1+g^2) ≤ arctan (s/g) ∧ arctan (s/g) ≤ s/g := by
  rcases eq_or_lt_of_le hs with he | hsp
  · subst s; simp
  have hx : 0 < s/g := div_pos hsp hg
  obtain ⟨c, hc, hd⟩ := exists_deriv_eq_slope arctan hx continuous_arctan.continuousOn
    differentiable_arctan.differentiableOn
  rw [(hasDerivAt_arctan c).deriv, arctan_zero, sub_zero, sub_zero] at hd
  have ceq : arctan (s/g) = (1/(1+c^2))*(s/g) := ((eq_div_iff hx.ne').mp hd).symm
  rw [ceq]
  have hcg : c*g ≤ 1 := le_trans ((lt_div_iff₀ hg).mp hc.2).le hs1
  have hcg0 : 0 ≤ c*g := mul_nonneg hc.1.le hg.le
  have hsquared : (c*g)^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hcg) (show 0 ≤ 1+c*g by linarith)]
  have lower : g^2/(1+g^2) ≤ 1/(1+c^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have upper : 1/(1+c^2) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by nlinarith [sq_nonneg c])
  constructor
  · calc
      g*s/(1+g^2) = (g^2/(1+g^2))*(s/g) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right lower hx.le
  · simpa using mul_le_mul_of_nonneg_right upper hx.le

/-- The bounds on the phase of an actual point in the closed critical strip. -/
theorem phase_bounds {g β : ℝ} (hg : 0 < g) (hb : 0 ≤ β) (hb' : β ≤ 1) :
    g/(1+g^2) ≤ arctan (β/g) + arctan ((1-β)/g) ∧
    arctan (β/g) + arctan ((1-β)/g) ≤ 1/g := by
  have p := slice_bounds hg hb hb'
  have q := slice_bounds hg (sub_nonneg.mpr hb') (show 1-β ≤ 1 by linarith)
  constructor
  · calc
      g/(1+g^2) = g*β/(1+g^2) + g*(1-β)/(1+g^2) := by ring
      _ ≤ _ := add_le_add p.1 q.1
  · calc
      _ ≤ β/g + (1-β)/g := add_le_add p.2 q.2
      _ = _ := by ring

/-- The logarithmic modulus bound in strip coordinates, proved from monotonicity of log. -/
theorem modulus_bound {g β : ℝ} (hg : 0 < g) (hb : 0 ≤ β) (hb' : β ≤ 1) :
    |(log (g^2+(1-β)^2)-log (g^2+β^2))/2| ≤ 1/(2*g^2) := by
  have g2 : 0 < g^2 := sq_pos_of_pos hg
  have L (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
      log (g^2) ≤ log (g^2+x^2) ∧ log (g^2+x^2) ≤ log (g^2+1) := by
    constructor
    · apply log_le_log g2; linarith [sq_nonneg x]
    · apply log_le_log (by positivity)
      nlinarith [mul_nonneg (sub_nonneg.mpr hx') (show 0 ≤ 1+x by linarith)]
  have p := L β hb hb'
  have q := L (1-β) (sub_nonneg.mpr hb') (by linarith)
  have cap : log (g^2+1)-log (g^2) ≤ 1/g^2 := by
    rw [←log_div (by positivity) g2.ne']
    calc
      _ ≤ (g^2+1)/g^2-1 := log_le_sub_one_of_pos (div_pos (by positivity) g2)
      _ = _ := by field_simp; ring
  rw [abs_le]
  constructor <;> rw [show 1/(2*g^2) = (1/g^2)/2 by ring] <;> linarith

/-- The geometric part of the Li zero test, with no assumptions on a modulus or phase.
Here `β` is the real part, `g` the absolute value of the ordinate, and `m` the index. -/
theorem strip_pair {m T g β : ℝ} (hT : 1 ≤ T) (hg : T ≤ g) (hm : 0 < m)
    (hcap : m ≤ 2*π*T-π) (hb : 0 ≤ β) (hb' : β ≤ 1) :
    0 < 1 - cosh (m*((log (g^2+(1-β)^2)-log (g^2+β^2))/2)) *
      cos (m*(arctan (β/g) + arctan ((1-β)/g))) := by
  have gpos : 0 < g := lt_of_lt_of_le zero_lt_one (hT.trans hg)
  exact high_pair hT hg hm hcap (phase_bounds gpos hb hb').1 (phase_bounds gpos hb hb').2
    (modulus_bound gpos hb hb')

private noncomputable def component (g s : ℝ) : ℂ := ⟨log (g^2+s^2)/2, arctan (s/g)⟩

private theorem exp_component (g s : ℝ) (hg : 0 < g) :
    Complex.exp (component g s) = (⟨g,s⟩ : ℂ) := by
  have hgs : 0 < g^2+s^2 := by positivity
  have hsqrt : 0 < √(g^2+s^2) := sqrt_pos.mpr hgs
  have he : exp (log (g^2+s^2)/2) = √(g^2+s^2) := by rw [exp_half, exp_log hgs]
  have hr : √(1+(s/g)^2) = √(g^2+s^2)/g := by
    rw [show 1+(s/g)^2 = (g^2+s^2)/g^2 by field_simp, sqrt_div hgs.le, sqrt_sq hg.le]
  apply Complex.ext
  · rw [Complex.exp_re]; change exp (log (g^2+s^2)/2) * cos (arctan (s/g)) = g
    rw [he, cos_arctan, hr]; field_simp
  · rw [Complex.exp_im]; change exp (log (g^2+s^2)/2) * sin (arctan (s/g)) = s
    rw [he, sin_arctan, hr]; field_simp

/-- The exponential representation for the actual complex Li factor. -/
private theorem complex_factor (β g : ℝ) (hg : 0 < g) :
    Complex.exp (component g (1-β) - component g (-β)) = 1-1/(⟨β,g⟩:ℂ) := by
  rw [Complex.exp_sub, exp_component _ _ hg, exp_component _ _ hg]
  have h1 : (⟨g,-β⟩:ℂ) ≠ 0 := fun h => hg.ne' (congrArg Complex.re h)
  have h2 : (⟨β,g⟩:ℂ) ≠ 0 := fun h => hg.ne' (congrArg Complex.im h)
  field_simp
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem factor_power_re (n : ℕ) (β g : ℝ) (hg : 0 < g) :
    ((1-1/(⟨β,g⟩:ℂ))^n).re = exp (n*((log (g^2+(1-β)^2)-log (g^2+β^2))/2)) *
      cos (n*(arctan (β/g) + arctan ((1-β)/g))) := by
  rw [←complex_factor β g hg, ←Complex.exp_nat_mul, Complex.exp_re]
  have he : (((n : ℂ)*(component g (1-β) - component g (-β))).re) =
      n*((log (g^2+(1-β)^2)-log (g^2+β^2))/2) := by
    simp [component, Complex.mul_re]; left; ring
  have hi : (((n : ℂ)*(component g (1-β) - component g (-β))).im) =
      n*(arctan (β/g) + arctan ((1-β)/g)) := by
    simp [component, Complex.mul_im, neg_div, arctan_neg]; left; ring
  rw [he, hi]

/-- Positivity of the sum of the original complex Li summands for a strip point
and its horizontal reflection. Multiplicities and an infinite zero sum are separate. -/
theorem complex_reflected_pair {n : ℕ} {T g β : ℝ} (hT : 1 ≤ T) (hg : T ≤ g)
    (hn : 0 < (n : ℝ)) (hcap : (n:ℝ) ≤ 2*π*T-π) (hb : 0 ≤ β) (hb' : β ≤ 1) :
    0 < ((1-(1-1/(⟨β,g⟩:ℂ))^n) + (1-(1-1/(⟨1-β,g⟩:ℂ))^n)).re := by
  have gpos : 0 < g := lt_of_lt_of_le zero_lt_one (hT.trans hg)
  have H := strip_pair hT hg hn hcap hb hb'
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, factor_power_re _ _ _ gpos,
    sub_sub_cancel] at *
  rw [show log (g^2+β^2) - log (g^2+(1-β)^2) = -(log (g^2+(1-β)^2) - log (g^2+β^2)) by ring,
      neg_div, mul_neg, add_comm (arctan ((1-β)/g)) (arctan (β/g))]
  rw [cosh_eq] at H
  linarith

/-- The two original Li summands at a point and its horizontal reflection. -/
noncomputable def pairValue (n : ℕ) (β g : ℝ) : ℝ :=
  ((1-(1-1/(⟨β,g⟩:ℂ))^n) + (1-(1-1/(⟨1-β,g⟩:ℂ))^n)).re

private theorem conjLi (n : ℕ) (β g : ℝ) :
    ((1-1/(⟨β,-g⟩:ℂ))^n).re = ((1-1/(⟨β,g⟩:ℂ))^n).re := by
  have hh (z : ℂ) : ((starRingEnd ℂ) z).re = z.re := rfl
  have hz : (starRingEnd ℂ) (⟨β,g⟩:ℂ) = (⟨β,-g⟩:ℂ) := rfl
  simpa only [map_pow, map_sub, map_div₀, map_one, hz] using hh ((1-1/(⟨β,g⟩:ℂ))^n)

theorem pair_even (n : ℕ) (β g : ℝ) : pairValue n β (-g) = pairValue n β g := by
  simp only [pairValue, Complex.add_re, Complex.sub_re, Complex.one_re, conjLi]

/-- Critical-line contributions are nonnegative, including a zero at the central point. -/
theorem line_nonneg (n : ℕ) (g : ℝ) : 0 ≤ pairValue n (1/2) g := by
  let z : ℂ := ⟨1/2,g⟩
  have h0 : z ≠ 0 := by intro h; have h' := congrArg Complex.re h; norm_num [z] at h'
  have hnorm : ‖z-1‖ = ‖z‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply,z]
    ring
  have unit : ‖1-1/z‖ = 1 := by
    rw [show 1-1/z=(z-1)/z by field_simp, norm_div, hnorm, div_self (norm_ne_zero_iff.mpr h0)]
  have re_le := Complex.re_le_norm ((1-1/z)^n)
  rw [norm_pow, unit, one_pow] at re_le
  simp only [pairValue, Complex.add_re, Complex.sub_re, Complex.one_re, show 1-(1/2:ℝ)=1/2 by norm_num]
  change 0 ≤ 1-((1-1/z)^n).re + (1-((1-1/z)^n).re)
  linarith

/-- For a summable real zero statistic, if the divisor is on the critical line to
height T and contains a higher zero, the full sum of the reflected terms is positive. -/
theorem positive_sum {ι : Type*} (β γ : ι → ℝ) {n : ℕ} {T : ℝ}
    (hT : 1 ≤ T) (hn : 0 < (n:ℝ)) (hcap : (n:ℝ) ≤ 2*π*T-π)
    (strip : ∀ i, 0 ≤ β i ∧ β i ≤ 1)
    (verified : ∀ i, |γ i| ≤ T → β i = 1/2)
    (higher : ∃ i, T < |γ i|) (summ : Summable (fun i => pairValue n (β i) (γ i))) :
    0 < ∑' i : ι, pairValue n (β i) (γ i) := by
  have absolute (i : ι) : pairValue n (β i) |γ i| = pairValue n (β i) (γ i) := by
    rcases le_or_gt 0 (γ i) with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, pair_even]
  have high (i : ι) (h : T ≤ |γ i|) : 0 < pairValue n (β i) (γ i) := by
    rw [←absolute i]
    exact complex_reflected_pair hT h hn hcap (strip i).1 (strip i).2
  obtain ⟨i, hi⟩ := higher
  apply summ.tsum_pos _ i (high i hi.le)
  intro j
  rcases le_or_gt |γ j| T with hj|hj
  · rw [verified j hj]; exact line_nonneg n (γ j)
  · exact (high j hj.le).le

/-- One original real Li summand at a zero with real part `β` and signed ordinate `γ`. -/
noncomputable def liTerm (n : ℕ) (β γ : ℝ) : ℝ := (1-(1-1/(⟨β,γ⟩:ℂ))^n).re

/-- The full linear-prefix transfer for an abstract zero divisor. Indexing with
multiplicity, `reflect` supplies the horizontal functional-equation permutation.
The resulting sum consists of single real Li summands, each counted once. -/
theorem li_positive {ι : Type*} (β γ : ι → ℝ) (reflect : ι ≃ ι) {n : ℕ} {T : ℝ}
    (hT : 1 ≤ T) (hn : 0 < (n:ℝ)) (hcap : (n:ℝ) ≤ 2*π*T-π)
    (strip : ∀ i, 0 ≤ β i ∧ β i ≤ 1)
    (ref_re : ∀ i, β (reflect i) = 1-β i) (ref_im : ∀ i, γ (reflect i) = γ i)
    (verified : ∀ i, |γ i| ≤ T → β i = 1/2) (higher : ∃ i, T < |γ i|)
    (summ : Summable (fun i => liTerm n (β i) (γ i))) :
    0 < ∑' i : ι, liTerm n (β i) (γ i) := by
  let f : ι → ℝ := fun i => liTerm n (β i) (γ i)
  have hfr : Summable (fun i => f (reflect i)) := reflect.summable_iff.mpr summ
  have hs : Summable f := summ
  have hident (i : ι) : pairValue n (β i) (γ i) = f i + f (reflect i) := by
    simp only [f, ref_re, ref_im, pairValue, liTerm, Complex.add_re]
  have hpaired : Summable (fun i => pairValue n (β i) (γ i)) := by
    simpa only [hident] using hs.add hfr
  have hpos := positive_sum β γ hT hn hcap strip verified higher hpaired
  simp only [hident] at hpos
  rw [hs.tsum_add hfr, reflect.tsum_eq f] at hpos
  change 0 < ∑' i, f i
  linarith

/-- Exact polar identity for a horizontal pair, including either sign of the ordinate. -/
theorem pair_polar (n : ℕ) (β g : ℝ) (hg : 0 < |g|) :
    pairValue n β g / 2 = 1-cosh (n*((log (|g|^2+(1-β)^2)-log (|g|^2+β^2))/2)) *
      cos (n*(arctan (β/|g|) + arctan ((1-β)/|g|))) := by
  have ev : pairValue n β g = pairValue n β |g| := by
    rcases le_or_gt 0 g with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h,pair_even]
  rw [ev]
  simp only [pairValue,Complex.add_re,Complex.sub_re,Complex.one_re,
    factor_power_re _ _ _ hg,sub_sub_cancel]
  rw [show log (|g|^2+β^2) - log (|g|^2+(1-β)^2) = -(log (|g|^2+(1-β)^2) - log (|g|^2+β^2)) by ring,
      neg_div,mul_neg,add_comm (arctan ((1-β)/|g|)) (arctan (β/|g|)),cosh_eq]
  ring

#print axioms edge_strictAnti
#print axioms high_pair
#print axioms phase_bounds
#print axioms modulus_bound
#print axioms strip_pair
#print axioms complex_reflected_pair
#print axioms positive_sum
#print axioms li_positive
#print axioms pair_polar

end LiReflectedPair

