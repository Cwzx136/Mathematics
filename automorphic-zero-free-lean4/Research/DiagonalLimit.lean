import Research.CosineResolvent

/-! The self-bootstrap at the liminf of the scaled zero displacement and the
pointwise Young majorant for the SU(2) auxiliary priors. -/
namespace ERH.DiagonalLimit
open Set

theorem diagonal {H : ℝ → ℝ} (hc : Continuous H) {P W G : ℝ} (hw : 0 < W)
    (cmp : ∀ a : ℝ, 0 < a → a < W →
      H ((W-a)/W)-P*H (-a/W) ≤ W*G) : H 0-P*H (-1) ≤ W*G := by
  let D := fun a : ℝ => H ((W-a)/W)-P*H (-a/W)
  have clos : IsClosed (D ⁻¹' Iic (W*G)) := by
    apply IsClosed.preimage _ isClosed_Iic
    unfold D
    fun_prop
  have hs : Ioo 0 W ⊆ D ⁻¹' Iic (W*G) := fun a ha => cmp a ha.1 ha.2
  have hend : W ∈ closure (Ioo 0 W) := by rw [closure_Ioo hw.ne]; exact ⟨hw.le,le_rfl⟩
  have hv := closure_minimal hs clos hend
  change H ((W-W)/W)-P*H (-W/W) ≤ W*G at hv
  simpa [neg_div,hw.ne'] using hv

theorem young_three_halves {u y : ℝ} (hu : 0 ≤ u) (hy : 0 ≤ y) :
    u^2*y ≤ 2*u^3/3 + y^3/3 := by
  nlinarith only [mul_nonneg (sq_nonneg (u-y)) (show 0 ≤ 2*u+y by linarith)]
end ERH.DiagonalLimit
