import Degree20Positivity
import Degree20Identity
import Degree20Reflection

namespace EllipticBernstein.SmoothDegree20

theorem lower_half_nonnegative (x y : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 0)
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1) : 0 ≤ polynomial x y := by
  have pl : Degree20.positiveOn (Degree20.splitXL interior) := hpL
  have h := pl (x+1) (-x) (y+1) (1-y)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [Degree20.splitXL_value, show (x+1)+2*(-x)=1-x by ring, interior_identity] at h
  linarith

theorem interior_nonnegative (x y : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1) : 0 ≤ polynomial x y := by
  by_cases hx : x ≤ 0
  · exact lower_half_nonnegative _ _ hx0 hx hy0 hy1
  · have h := lower_half_nonnegative (-x) (-y) (by linarith) (by linarith) (by linarith) (by linarith)
    simpa only [reflection] using h

theorem normalized_fourier_nonnegative (x θ : ℝ) (lo : -1 ≤ x) (hi : x ≤ 1) :
    0 ≤ (evalFourier x θ posTable - evalFourier x θ negTable)/1000000 := by
  simp only [fourier_eq]
  exact div_nonneg (interior_nonnegative x _ lo hi (Real.neg_one_le_cos _) (Real.cos_le_one _)) (by norm_num)

#print axioms normalized_fourier_nonnegative
#print axioms ratio_lt
end EllipticBernstein.SmoothDegree20
