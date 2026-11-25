import Research.TiltedGain
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! From the signed Hadamard comparison to a zero strip for a complex function.
The budget is the inequality with the tilted Laplace kernel prior to rounding. -/
noncomputable section
namespace ERH.TiltedWidth
open ERH.Bump ERH.SmoothedWidth ERH.TiltedGain

def Budget (F : ℂ → ℂ) (b p G d W : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ H : ℝ, ∀ β t : ℝ, Real.log |t| ≥ H →
    0 < β → β < 1 → F ⟨β,t⟩ = 0 → Real.log |t| * (1-β) ≤ W →
     response b p (-(d/W)) (Real.log |t| * (1-β)/W) ≤ W*G+e

theorem boundary_value (b p r : ℝ) : response b p (-r) 1 = tilted b p r := by
  unfold response tilted
  apply congrArg (fun v : ℝ => b*v)
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [show b*x*(-r+1) = b*(1-r)*x by ring,show -(b*x*(-r)) = b*r*x by ring]

/-- Any strict gain against the actual integral transfers to both edges. -/
theorem transfer (F : ℂ → ℂ) {b p G d W : ℝ} (hb : 0 ≤ b) (hW : 0 < W)
    (margin : W*G < tilted b p (d/W)) (estimate : Budget F b p G d W)
    (reflect : ∀ β t : ℝ, 0 < β → β < 1 → F ⟨β,t⟩ = 0 → F ⟨1-β,t⟩ = 0) :
    ∃ H : ℝ, ∀ β t : ℝ, H ≤ Real.log |t| → 0 < β → β < 1 → F ⟨β,t⟩ = 0 →
        W < Real.log |t| * min β (1-β) := by
  let e := (tilted b p (d/W)-W*G)/2
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨H,hH⟩ := estimate e he
  have right (β t : ℝ) (ht : H ≤ Real.log |t|) (h0 : 0 < β) (h1 : β < 1)
      (hz : F ⟨β,t⟩ = 0) : W < Real.log |t| * (1-β) := by
    by_contra! hnear
    have hscaled : Real.log |t| * (1-β)/W ≤ 1 := (div_le_iff₀ hW).2 (by simpa using hnear)
    have mono := response_decreases b p (-(d/W)) hb hscaled
    rw [boundary_value] at mono
    have bound := hH β t ht h0 h1 hz hnear
    dsimp [e] at bound
    linarith
  refine ⟨H,?_⟩
  intro β t ht h0 h1 hz
  have a := right β t ht h0 h1 hz
  have b' := right (1-β) t ht (by linarith) (by linarith) (reflect β t h0 h1 hz)
  rw [show 1-(1-β) = β by ring] at b'
  exact (le_total β (1-β)).elim (fun h => by rwa [min_eq_left h]) (fun h => by rwa [min_eq_right h])

/-- The premise is an inequality of rational functions for rational parameter data. -/
theorem rational_transfer (F : ℂ → ℂ) {b p G d W : ℝ} (hb : 0 < b) (hp : 0 ≤ p)
    (hW : 0 < W) (hr : 0 ≤ d/W) (hr' : d/W < 1) (hc : b*(d/W) ≤ 5/6)
    (margin : W*G < b*(momentPolynomial (b*(1-d/W))-p*upperMoment (b*(d/W))))
    (estimate : Budget F b p G d W)
    (reflect : ∀ β t : ℝ, 0 < β → β < 1 → F ⟨β,t⟩ = 0 → F ⟨1-β,t⟩ = 0) :
    ∃ H : ℝ, ∀ β t : ℝ, H ≤ Real.log |t| → 0 < β → β < 1 → F ⟨β,t⟩ = 0 →
        W < Real.log |t| * min β (1-β) :=
  transfer F hb.le hW (margin.trans_le (lower b p (d/W) hb hp hr hr' hc)) estimate reflect

#print axioms rational_transfer
end ERH.TiltedWidth
