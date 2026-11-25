import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-! The finite Gram identity behind the bad-prime positivity of the elliptic amplifier. -/
namespace EulerSquareGram
open scoped BigOperators

/-- A finite real Gram form is a sum of squares in the column index. -/
theorem gram_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (v : ι → κ → ℝ) :
    ∑ i, ∑ j, a i * a j * (∑ b, v i b * v j b) =
      ∑ b, (∑ i, a i * v i b)^2 := by
  classical
  symm
  have expansion (b : κ) : (∑ i, a i * v i b)^2 =
      ∑ i, ∑ j, a i*a j*(v i b*v j b) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    _ = ∑ b, ∑ i, ∑ j, a i*a j*(v i b*v j b) :=
      Finset.sum_congr rfl (fun b _ => expansion b)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]

/-- Both real and imaginary coefficient vectors of a trigonometric square can
    be evaluated against the ramified symmetric-power multiplication kernel. -/
theorem real_imag_nonnegative {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a c : ι → ℝ) (v : ι → κ → ℝ) :
    0 ≤ (∑ i, ∑ j, a i*a j*(∑ b, v i b*v j b)) +
        (∑ i, ∑ j, c i*c j*(∑ b, v i b*v j b)) := by
  rw [gram_identity, gram_identity]
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
                   (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

#print axioms gram_identity
#print axioms real_imag_nonnegative
end EulerSquareGram
