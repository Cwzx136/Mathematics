import Research.Occupation

/-! The unramified finite real Euler identities behind the moving-ordinate budgets.
Real and imaginary parts are kept separate to expose all conjugated pair terms. -/
noncomputable section
open scoped BigOperators
namespace ERH.Occupation

/-- Expanding a symmetric matrix counts each unordered pair twice. -/
theorem ordered_decomposition {k : ℕ} (f : Fin k → Fin k → ℝ)
    (symm : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) =
      (∑ i, f i i) + 2*∑ p ∈ pairs k, f p.1 p.2 := by
  have split (i j : Fin k) : f i j =
      (if i = j then f i j else 0) +
      (if i < j then f i j else 0) +
      (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have decomp := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin k))) rfl
    (fun i _ => Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin k))) rfl fun j _ => split i j)
  simp only [Finset.sum_add_distrib] at decomp
  have diag : (∑ i, ∑ j, if i = j then f i j else 0) = ∑ i, f i i := by simp
  have reverse : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [symm j i]
  have upper : (∑ p ∈ pairs k, f p.1 p.2) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    unfold pairs
    rw [Finset.sum_filter, Finset.sum_product]
  rw [diag, reverse] at decomp
  rw [upper]
  linarith

/-- The complex moving square split into its constant, target, diagonal and
unordered Rankin cross coefficients. Here R_i+i I_i is the weighted rotated trace. -/
theorem moving_square {k : ℕ} (R I : Fin k → ℝ) :
    ((1+∑ i, R i)^2+(∑ i, I i)^2)/2 =
      1/2 + (∑ i, R i) + (∑ i, ((R i)^2+(I i)^2))/2 +
      ∑ p ∈ pairs k, (R p.1*R p.2+I p.1*I p.2) := by
  have gram := ordered_decomposition (fun i j => R i*R j+I i*I j) (by intros; ring)
  have expand : (∑ i, R i)^2+(∑ i, I i)^2 = ∑ i, ∑ j, (R i*R j+I i*I j) := by
    simp only [pow_two, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [← sq] at gram
  linarith

/-- The rank-one Euler term exp(-iϕ) rotates the Satake trace A+iB.
This computes the crossed real coefficient after cancelling the two angles. -/
theorem rotated_cross (A B c s c' s' : ℝ) :
    (A*c+B*s)*(A*c'+B*s')+(B*c-A*s)*(B*c'-A*s') =
      (A^2+B^2)*(c*c'+s*s') := by ring

theorem real_phase_split (c s c' s' : ℝ) :
    c*c' = ((c*c'+s*s')+(c*c'-s*s'))/2 := by ring

/-- With a unit phase, the diagonal square has fixed component one half. -/
theorem real_phase_diagonal (c s : ℝ) (unit : c^2+s^2=1) :
    c^2 = (1+(c^2-s^2))/2 := by linarith

end ERH.Occupation
#print axioms ERH.Occupation.moving_square
#print axioms ERH.Occupation.rotated_cross
