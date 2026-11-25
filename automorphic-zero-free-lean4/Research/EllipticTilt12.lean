import Research.Tilt12Positivity
import Research.Tilt12Identity
import Research.Tilt12Reflection

namespace EllipticBernstein.Tilt12
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

theorem lower_half_nonnegative (x y : ℝ) (lo : -1 ≤ x) (hi : x ≤ 0)
    (yl : -1 ≤ y) (yu : y ≤ 1) : 0 ≤ polynomial x y := by
  have pl : Degree12.positiveOn (Degree12.splitXL interior) := hpL
  have h := pl (x+1) (-x) (y+1) (1-y)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [Degree12.splitXL_value, show (x+1)+2*(-x)=1-x by ring, interior_identity] at h
  linarith

theorem interior_nonnegative (x y : ℝ) (lo : -1 ≤ x) (hi : x ≤ 1)
    (yl : -1 ≤ y) (yu : y ≤ 1) : 0 ≤ polynomial x y := by
  by_cases hs : x≤0
  · exact lower_half_nonnegative x y lo hs yl yu
  · have h := lower_half_nonnegative (-x) (-y) (by linarith) (by linarith) (by linarith) (by linarith)
    simpa only [reflection] using h

theorem normalized_fourier_nonnegative (x θ : ℝ) (lo : -1 ≤ x) (hi : x ≤ 1) :
    0 ≤ (evalFourier x θ posTable-evalFourier x θ negTable)/1000000 := by
  simp only [fourier_eq]
  exact div_nonneg (interior_nonnegative x _ lo hi (Real.neg_one_le_cos _) (Real.cos_le_one _)) (by norm_num)

/-- Every negative coefficient is static or belongs to a scalar function. -/
theorem negative_support {l j c : ℕ} (h : (l,j,c) ∈ negTable) : l=0 ∨ j=0 := by
  have hi := List.all_eq_true.mp negative_terms_are_free (l,j,c) h
  simpa using hi

/-- At each nonzero frequency only symmetric powers of index at most two are charged. -/
theorem moving_support {l j c : ℕ} (h : (l,j,c) ∈ posTable) (hl : l≠0) : j≤2 := by
  have hi := List.all_eq_true.mp moving_power_restriction (l,j,c) h
  simpa [hl] using hi

#print axioms normalized_fourier_nonnegative
#print axioms interior_nonnegative
end EllipticBernstein.Tilt12
