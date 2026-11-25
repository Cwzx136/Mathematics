import Research.SignedHadamard

/-! Summing the fixed-radius far-zero error from a two-integration-by-parts kernel bound. -/

namespace ERH.SignedHadamard

/-- Far from the tested point, a shift to the reference half-plane controls the inverse
squared denominator with an explicit constant. -/
theorem compare_inverse_squares {z z₀ : ℂ} {η D : ℝ} (hη : 0 < η)
    (hD : 0 ≤ D) (hfar : η ≤ ‖z‖) (href : 0 < ‖z₀‖) (hshift : ‖z₀-z‖ ≤ D) :
    1/‖z‖^2 ≤ (1+D/η)^2 / ‖z₀‖^2 := by
  have hz := hη.trans_le hfar
  have htriangle : ‖z₀‖ ≤ ‖z₀-z‖+‖z‖ := by
    simpa using norm_add_le (z₀-z) z
  have hr : 0 ≤ 1+D/η := by positivity
  have hx : D ≤ D/η*‖z‖ := by
    calc
      D = D/η*η := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hfar (div_nonneg hD hη.le)
  have hn : ‖z₀‖ ≤ (1+D/η)*‖z‖ := by nlinarith
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  apply (div_le_div_iff₀ (sq_pos_of_pos hz) (sq_pos_of_pos href)).mpr
  simpa [mul_pow] using h2

/-- A pointwise remainder bounded by `C/(L |z|²)` over far zeros has absolute sum
at most `C M (1+D/η)²` given the ordinary reference bound `Σ 1/|z₀|² ≤ M L`.
Indices may themselves form a subtype selecting the far zeros and their multiplicities. -/
theorem far_sum {ι : Type*} (z z₀ : ι → ℂ) (err : ι → ℝ) {η D C L M : ℝ}
    (hη : 0 < η) (hD : 0 ≤ D) (hC : 0 ≤ C) (hL : 0 < L)
    (hfar : ∀ i, η ≤ ‖z i‖) (href : ∀ i, 0 < ‖z₀ i‖)
    (hshift : ∀ i, ‖z₀ i-z i‖ ≤ D)
    (he : ∀ i, |err i| ≤ C/L * (1/‖z i‖^2))
    (hs : Summable (fun i => 1/‖z₀ i‖^2)) (hbudget : ∑' i, 1/‖z₀ i‖^2 ≤ M*L) :
    Summable (fun i => |err i|) ∧ ∑' i, |err i| ≤ C*M*(1+D/η)^2 := by
  let A := C/L * (1+D/η)^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have major (i : ι) : |err i| ≤ A * (1/‖z₀ i‖^2) := by
    apply (he i).trans
    have hc := compare_inverse_squares hη hD (hfar i) (href i) (hshift i)
    calc
      _ ≤ C/L * ((1+D/η)^2 / ‖z₀ i‖^2) := mul_le_mul_of_nonneg_left hc (div_nonneg hC hL.le)
      _ = _ := by dsimp [A]; ring
  have hmaj : Summable (fun i => A*(1/‖z₀ i‖^2)) := hs.mul_left A
  have hsum := hmaj.of_nonneg_of_le (fun i => abs_nonneg (err i)) major
  refine ⟨hsum, (hsum.tsum_le_tsum major hmaj).trans ?_⟩
  rw [tsum_mul_left]
  calc
    _ ≤ A*(M*L) := mul_le_mul_of_nonneg_left hbudget hA
    _ = _ := by dsimp [A]; field_simp

end ERH.SignedHadamard

#print axioms ERH.SignedHadamard.far_sum
