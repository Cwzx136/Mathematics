import Research.MultiShift
import Research.StripMinimum

/-! Positivity for the complete signed comparison kernel, not only at its endpoints. -/
open Complex
noncomputable section
namespace ERH.SignedKernel
open ERH.MultiShift ERH.StripMinimum

theorem pairC_re (u : ℝ) (z : ℂ) : (pairC u z).re = pair u z.re z.im := by
  simp [pairC,pair,atom,Complex.inv_re,Complex.normSq_apply,pow_two]

def comparisonC (m : ℕ) (u : ℝ) (z : ℂ) : ℂ :=
  pairC u z - ((∑ k ∈ Finset.range m,
     (pairC (u+((2*k+1:ℕ):ℝ)) z - pairC (u+((2*k+2:ℕ):ℝ)) z))
    + (weight m:ℂ) * pairC (u+((2*m+1:ℕ):ℝ)) z)

theorem comparisonC_re (m : ℕ) (u : ℝ) (z : ℂ) :
    (comparisonC m u z).re = corrected m u z.re z.im := by
  simp only [comparisonC,corrected,linear,Complex.sub_re,Complex.add_re,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,pairC_re]

theorem good_comparison (m : ℕ) {u : ℝ} (hu : 0 < u) : Good (comparisonC m u) := by
  have pos (j : ℕ) : 0 < u + j := by positivity
  exact (good_pairC hu).sub ((Good.sum _ _ (fun k _ =>
    (good_pairC (pos (2*k+1))).sub (good_pairC (pos (2*k+2))))).add
    ((good_pairC (pos (2*m+1))).smulReal (weight m)))

/-- The full real paired kernel is nonnegative for every ordinate and every real
part in the closed critical strip. -/
theorem corrected_nonneg (m : ℕ) {u β : ℝ} (hu : 0 < u) (hβ : 0 ≤ β)
    (hβ' : β ≤ 1) (y : ℝ) : 0 ≤ corrected m u β y := by
  let z := Complex.mk β y
  have hz : z ∈ closedStrip := ⟨hβ,hβ'⟩
  have h := nonnegative_of_edges (good_comparison m hu)
     (fun w hw => by rw [comparisonC_re,hw]; exact corrected_left_nonneg m hu.le w.im)
     (fun w hw => by rw [comparisonC_re,hw]; exact corrected_right_nonneg m hu.le w.im) hz
  simpa only [comparisonC_re,z] using h

#print axioms corrected_nonneg
end ERH.SignedKernel
