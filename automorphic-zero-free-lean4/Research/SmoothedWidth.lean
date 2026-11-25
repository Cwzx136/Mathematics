import Research.CompactBump
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A common physical frequency translation and the passage to a zero-free width.
The analytic estimate is quantified explicitly over all evaluation heights. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace ERH.SmoothedWidth
open ERH.Bump

def response (b p v w : ℝ) : ℝ :=
  b * ∫ x in (0:ℝ)..1, h x*(Real.exp (-(b*x*(v+w)))-p*Real.exp (-(b*x*v)))

theorem response_continuous (b p w : ℝ) : Continuous (fun v => response b p v w) := by
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  dsimp [Function.uncurry,h]
  fun_prop

theorem response_decreases (b p v : ℝ) {w w' : ℝ} (hb : 0 ≤ b) (hw : w ≤ w') :
    response b p v w' ≤ response b p v w := by
  apply mul_le_mul_of_nonneg_left _ hb
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply Continuous.intervalIntegrable
    unfold h
    fun_prop
  · apply Continuous.intervalIntegrable
    unfold h
    fun_prop
  · intro x hx
    apply mul_le_mul_of_nonneg_left _ (h_nonneg hx)
    apply sub_le_sub_right
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left (add_le_add_right hw v) (mul_nonneg hb hx.1))

theorem response_at_zero (b p : ℝ) :
    response b p 0 1 = b*(∫ x in (0:ℝ)..1, h x*(Real.exp (-(b*x))-p)) := by
  simp [response]

/-- Given an averaged disk estimate with vanishing error, exclude every zero with
scaled distance at most one once the logarithmic height is sufficiently large. -/
theorem exclusion (Z : ℝ → ℝ → Prop) {b p a G : ℝ} (hb : 0 ≤ b) (ha : 0 < a)
    (margin : a*G < response b p 0 1)
    (estimate : ∀ v : ℝ, 0 < v → ∀ e : ℝ, 0 < e →
       ∃ H : ℝ, ∀ L ≥ H, ∀ β, Z L β → L*(1-β) ≤ a →
        response b p v (L*(1-β)/a) ≤ a*G+e) :
    ∃ H : ℝ, ∀ L ≥ H, ∀ β, Z L β → a < L*(1-β) := by
  have ev : ∀ᶠ v in nhds (0:ℝ), a*G < response b p v 1 :=
    (response_continuous b p 1).continuousAt.eventually_const_lt margin
  have ev' : ∀ᶠ v in nhdsWithin (0:ℝ) (Ioi 0), a*G < response b p v 1 :=
    ev.filter_mono nhdsWithin_le_nhds
  have ep : ∀ᶠ v in nhdsWithin (0:ℝ) (Ioi 0), 0 < v := self_mem_nhdsWithin
  obtain ⟨v,hv,hm⟩ := (ep.and ev').exists
  let e := (response b p v 1-a*G)/2
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨H,hH⟩ := estimate v hv e he
  refine ⟨H,?_⟩
  intro L hL β hz
  by_contra! hf
  have hw : L*(1-β)/a ≤ 1 := (div_le_iff₀ ha).2 (by simpa using hf)
  have mono := response_decreases b p v hb hw
  have bound := hH L hL β hz hf
  dsimp [e] at bound
  linarith

theorem rational_exclusion (Z : ℝ → ℝ → Prop) {b p a G : ℝ} (hb : 0 ≤ b) (ha : 0 < a)
    (margin : a*G < b*(momentPolynomial b-(315/796)*p))
    (estimate : ∀ v : ℝ, 0 < v → ∀ e : ℝ, 0 < e →
       ∃ H : ℝ, ∀ L ≥ H, ∀ β, Z L β → L*(1-β) ≤ a →
        response b p v (L*(1-β)/a) ≤ a*G+e) :
    ∃ H : ℝ, ∀ L ≥ H, ∀ β, Z L β → a < L*(1-β) := by
  apply exclusion Z hb ha _ estimate
  rw [response_at_zero]
  exact margin.trans_le (general_gain_lower b p hb)

#print axioms rational_exclusion
end ERH.SmoothedWidth
