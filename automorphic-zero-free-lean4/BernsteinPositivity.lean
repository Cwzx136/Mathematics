import BernsteinData
import Mathlib.Analysis.Real.Sqrt

/-! An exact integer certificate for the 15-term elliptic amplifier. -/
namespace EllipticBernstein

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- Exact recursive closed computation. Kernel reduction verifies every subdivision. -/
theorem interior_checked : cert 18 true interiorNet = true := by
  decide +kernel

theorem interior_positive : positiveOn interiorNet :=
  cert_sound 18 true interiorNet interior_checked

theorem exterior_positive : positiveOn exteriorNet :=
  good_positive exteriorNet exterior_good

/-- The numerator of the original amplifier is at least 2
on the full real trace range and the full cosine interval. -/
theorem amplifier_lower (x y : ℝ) (hy0 : -1 ≤ y) (hy1 : y ≤ 1) :
    2 ≤ amplifier x y := by
  have ext (z t : ℝ) (hz : 1 ≤ z) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
      2 ≤ amplifier z t := by
    have h := exterior_positive (z-1) 1 (t+1) (1-t)
      (by linarith) (by norm_num) (by linarith) (by linarith)
    rw [exterior_identity] at h
    linarith
  by_cases hx0 : -1 ≤ x
  · by_cases hx1 : x ≤ 1
    · have h := interior_positive (x+1) (1-x) (y+1) (1-y)
        (by linarith) (by linarith) (by linarith) (by linarith)
      rw [interior_identity] at h
      linarith
    · exact ext x y (by linarith) hy0 hy1
  · have h := ext (-x) (-y) (by linarith) (by linarith) (by linarith)
    simpa only [amplifier_reflect] using h

/-- The positive kernel remaining after removing two units of static pole weight. -/
theorem reduced_amplifier_nonneg (x y : ℝ) (hy0 : -1 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ (amplifier x y - 2)/1000000 := by
  exact div_nonneg (sub_nonneg.mpr (amplifier_lower x y hy0 hy1)) (by norm_num)

#print axioms amplifier_lower
end EllipticBernstein
