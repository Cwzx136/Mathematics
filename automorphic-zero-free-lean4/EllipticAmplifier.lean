import BernsteinPositivity

namespace EllipticBernstein
noncomputable def reducedPole : ℝ := 462242/1000000
noncomputable def shiftedHalfDegree : ℝ := 2284863/1000000

/-- Rational rounding for the calibrated zero-exclusion constant. This theorem is
pure real arithmetic; passing from its coefficient to zeros uses analytic inputs. -/
theorem reduced_constant :
    (1 - 1 / Real.sqrt 5) * shiftedHalfDegree / (1 - Real.sqrt reducedPole)^2
      < 1232544/100000 := by
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have h5 : Real.sqrt 5 ≤ (223606798/100000000 : ℝ) := by
    apply (Real.sqrt_le_left (by norm_num)).2
    norm_num
  have hκ : (44721359/100000000 : ℝ) ≤ 1 / Real.sqrt 5 := by
    apply (le_div_iff₀ hs).2
    linarith
  have hp : Real.sqrt reducedPole ≤ (67988382/100000000 : ℝ) := by
    apply (Real.sqrt_le_left (by norm_num)).2
    norm_num [reducedPole]
  have hp' : 0 < 1 - Real.sqrt reducedPole := by linarith
  apply (div_lt_iff₀ (sq_pos_of_pos hp')).2
  have hsq : (1-(67988382/100000000:ℝ))^2 ≤ (1-Real.sqrt reducedPole)^2 := by
    apply (sq_le_sq₀ (by norm_num) hp'.le).2
    linarith
  calc
    (1 - 1 / Real.sqrt 5) * shiftedHalfDegree ≤
      (1-(44721359/100000000:ℝ)) * shiftedHalfDegree :=
        mul_le_mul_of_nonneg_right (by linarith) (by norm_num [shiftedHalfDegree])
    _ < (1232544/100000:ℝ) * (1-67988382/100000000)^2 := by norm_num [shiftedHalfDegree]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by norm_num)

#print axioms amplifier_lower
#print axioms reduced_amplifier_nonneg
#print axioms reduced_constant
end EllipticBernstein
