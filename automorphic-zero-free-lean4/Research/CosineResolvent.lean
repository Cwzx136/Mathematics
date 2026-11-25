import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-! A compact cosine profile for the positive-definite vertical averaging test.
The resolvent is its actual interval integral against the exponential kernel. -/

namespace ERH.CosineResolvent
noncomputable section
open Real Set
open scoped Interval

def edge (k : ℝ) : ℝ := (π-arctan k)/k
def gain (k : ℝ) : ℝ := 1/(1+k^2)
def load (k S : ℝ) : ℝ := (1-gain k)/(1+S)
def profile (k S x : ℝ) : ℝ := cos (k*x)-cos (k*S)

def resolvent (k S x : ℝ) : ℝ :=
  ∫ y in -S..S, exp (-|x-y|)*profile k S y

private def primitiveL (k c y : ℝ) : ℝ :=
  exp y * ((cos (k*y)+k*sin (k*y))/(1+k^2)-c)
private def primitiveR (k c y : ℝ) : ℝ :=
  exp (-y) * ((-cos (k*y)+k*sin (k*y))/(1+k^2)+c)

private theorem derivL (k c x : ℝ) : HasDerivAt (primitiveL k c)
    (exp x*(cos (k*x)-c)) x := by
  unfold primitiveL
  have hk := (hasDerivAt_id x).const_mul k
  have h := (Real.hasDerivAt_exp x).mul
    ((((hk.cos).add ((hk.sin).const_mul k)).div_const (1+k^2)).sub_const c)
  convert h using 1 <;> dsimp <;> try congr 1
  all_goals field_simp; ring

private theorem derivR (k c x : ℝ) : HasDerivAt (primitiveR k c)
    (exp (-x)*(cos (k*x)-c)) x := by
  unfold primitiveR
  have hk := (hasDerivAt_id x).const_mul k
  have h := (((hasDerivAt_id x).neg).exp).mul
    (((((hk.cos).neg).add ((hk.sin).const_mul k)).div_const (1+k^2)).add_const c)
  convert h using 1 <;> dsimp <;> try congr 1
  all_goals field_simp; ring

theorem endpoint {k : ℝ} (hk : 0 < k) :
    sin (k*edge k) = -k*cos (k*edge k) := by
  have hks : k*edge k = π-arctan k := by unfold edge; field_simp
  rw [hks, sin_pi_sub, cos_pi_sub, sin_arctan, cos_arctan]
  ring

theorem edge_pos {k : ℝ} (hk : 0 < k) : 0 < edge k := by
  apply div_pos _ hk
  linarith [arctan_lt_pi_div_two k, pi_pos]

theorem profile_nonneg {k x : ℝ} (hk : 0 < k) (hx : |x| ≤ edge k) :
    0 ≤ profile k (edge k) x := by
  have hks : k*edge k = π-arctan k := by unfold edge; field_simp
  have hpi : k*edge k ≤ π := by rw [hks]; linarith [arctan_pos.mpr hk]
  have hxx : |k*x| ≤ k*edge k := by rw [abs_mul, abs_of_pos hk]; gcongr
  have hcos := Real.strictAntiOn_cos.antitoneOn
    (show |k*x| ∈ Icc (0:ℝ) π from ⟨abs_nonneg _,hxx.trans hpi⟩)
    (show k*edge k ∈ Icc (0:ℝ) π from ⟨mul_nonneg hk.le (edge_pos hk).le,hpi⟩) hxx
  apply sub_nonneg.mpr
  rwa [Real.cos_abs] at hcos

theorem profile_mass {k S : ℝ} (hk : 0 < k)
    (hedge : sin (k*S) = -k*cos (k*S)) :
    (∫ y in -S..S, profile k S y) = -2*cos (k*S)*(1+S) := by
  have h : ∀ x ∈ uIcc (-S) S,
      HasDerivAt (fun y => sin (k*y)/k-cos (k*S)*y) (profile k S x) x := by
    intro x _
    have hh := ((((hasDerivAt_id x).const_mul k).sin).div_const k).sub
      ((hasDerivAt_id x).const_mul (cos (k*S)))
    convert hh using 1 <;> first | rfl | simp [profile, hk.ne']
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by unfold profile; exact Continuous.intervalIntegrable (by fun_prop) _ _),
    mul_neg, sin_neg, hedge]
  field_simp
  ring

/-- The closed form for the convolution on the support, including its endpoints. -/
theorem resolvent_on_support {k S x : ℝ} (hx : x ∈ Icc (-S) S)
    (hedge : sin (k*S) = -k*cos (k*S)) :
    resolvent k S x = 2*gain k*profile k S x+2*(gain k-1)*cos (k*S) := by
  let c := cos (k*S)
  have hden : 1+k^2 ≠ 0 := by positivity
  have hl : primitiveL k c (-S)=0 := by
    unfold primitiveL c
    rw [mul_neg, cos_neg, sin_neg, hedge]
    field_simp
    ring
  have hr : primitiveR k c S=0 := by
    unfold primitiveR c
    rw [hedge]
    field_simp
    ring
  have hli : (∫ y in -S..x, exp y * profile k S y) = primitiveL k c x := by
    rw [← sub_zero (primitiveL k c x), ← hl]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · exact fun y _ => derivL k c y
    · apply Continuous.intervalIntegrable; unfold profile; fun_prop
  have hri : (∫ y in x..S, exp (-y) * profile k S y) = -primitiveR k c x := by
    rw [← zero_sub (primitiveR k c x), ← hr]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · exact fun y _ => derivR k c y
    · apply Continuous.intervalIntegrable; unfold profile; fun_prop
  have hcont : Continuous (fun y => exp (-|x-y|)*profile k S y) := by
    unfold profile; fun_prop
  unfold resolvent
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-S) x) (hcont.intervalIntegrable x S)]
  have eqL : (∫ y in -S..x, exp (-|x-y|)*profile k S y) =
      exp (-x)* (∫ y in -S..x, exp y*profile k S y) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx.1] at hy
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr hy.2), neg_sub, sub_eq_neg_add, Real.exp_add]
    ring
  have eqR : (∫ y in x..S, exp (-|x-y|)*profile k S y) =
      exp x* (∫ y in x..S, exp (-y)*profile k S y) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx.2] at hy
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr hy.1), neg_neg, sub_eq_add_neg, Real.exp_add]
    ring
  rw [eqL,eqR,hli,hri]
  unfold primitiveL primitiveR gain profile c
  rw [Real.exp_neg]
  field_simp
  ring

theorem rayleigh_density {k : ℝ} (hk : 0 < k) (x : ℝ)
    (hx : x ∈ Icc (-edge k) (edge k)) :
    resolvent k (edge k) x - load k (edge k)*(∫ y in -edge k..edge k, profile k (edge k) y)
      = 2*gain k*profile k (edge k) x := by
  rw [resolvent_on_support hx (endpoint hk), profile_mass hk (endpoint hk)]
  unfold load
  have hn : 0 < 1+edge k := by linarith [edge_pos hk]
  field_simp
  ring

/-- The numerator of the normalized Rayleigh quotient, as an integral over
the support. The exponential convolution and the mass are the real integrals
from the variational argument. -/
theorem rayleigh_integral {k : ℝ} (hk : 0 < k) :
    (∫ x in -edge k..edge k, profile k (edge k) x *
        (resolvent k (edge k) x - load k (edge k)*(∫ y in -edge k..edge k, profile k (edge k) y)))
      = 2*gain k*(∫ x in -edge k..edge k, profile k (edge k) x^2) := by
  conv_rhs => rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by linarith [edge_pos hk] : -edge k ≤ edge k)] at hx
  dsimp only
  rw [rayleigh_density hk x hx]
  ring

end
end ERH.CosineResolvent
