import Degree20Chebyshev

namespace EllipticBernstein.SmoothDegree20

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem flipT0 (x : ℝ) : chebT 0 (-x) = chebT 0 x := by
  rw [polyT0, polyT0] <;> ring
theorem flipT1 (x : ℝ) : chebT 1 (-x) = -chebT 1 x := by
  rw [polyT1, polyT1] <;> ring
theorem flipT2 (x : ℝ) : chebT 2 (-x) = chebT 2 x := by
  rw [polyT2, polyT2] <;> ring
theorem flipT3 (x : ℝ) : chebT 3 (-x) = -chebT 3 x := by
  rw [polyT3, polyT3] <;> ring
theorem flipT4 (x : ℝ) : chebT 4 (-x) = chebT 4 x := by
  rw [polyT4, polyT4] <;> ring
theorem flipT5 (x : ℝ) : chebT 5 (-x) = -chebT 5 x := by
  rw [polyT5, polyT5] <;> ring
theorem flipT6 (x : ℝ) : chebT 6 (-x) = chebT 6 x := by
  rw [polyT6, polyT6] <;> ring
theorem flipT8 (x : ℝ) : chebT 8 (-x) = chebT 8 x := by
  rw [polyT8, polyT8] <;> ring
theorem flipT9 (x : ℝ) : chebT 9 (-x) = -chebT 9 x := by
  rw [polyT9, polyT9] <;> ring
theorem flipT10 (x : ℝ) : chebT 10 (-x) = chebT 10 x := by
  rw [polyT10, polyT10] <;> ring
theorem flipT12 (x : ℝ) : chebT 12 (-x) = chebT 12 x := by
  rw [polyT12, polyT12] <;> ring
theorem flipT13 (x : ℝ) : chebT 13 (-x) = -chebT 13 x := by
  rw [polyT13, polyT13] <;> ring
theorem flipT14 (x : ℝ) : chebT 14 (-x) = chebT 14 x := by
  rw [polyT14, polyT14] <;> ring
theorem flipT16 (x : ℝ) : chebT 16 (-x) = chebT 16 x := by
  rw [polyT16, polyT16] <;> ring
theorem flipT18 (x : ℝ) : chebT 18 (-x) = chebT 18 x := by
  rw [polyT18, polyT18] <;> ring
theorem flipT19 (x : ℝ) : chebT 19 (-x) = -chebT 19 x := by
  rw [polyT19, polyT19] <;> ring
theorem flipT20 (x : ℝ) : chebT 20 (-x) = chebT 20 x := by
  rw [polyT20, polyT20] <;> ring
theorem flipU0 (x : ℝ) : chebU 0 (-x) = chebU 0 x := by
  rw [polyU0, polyU0] <;> ring
theorem flipU1 (x : ℝ) : chebU 1 (-x) = -chebU 1 x := by
  rw [polyU1, polyU1] <;> ring
theorem flipU2 (x : ℝ) : chebU 2 (-x) = chebU 2 x := by
  rw [polyU2, polyU2] <;> ring
theorem flipU3 (x : ℝ) : chebU 3 (-x) = -chebU 3 x := by
  rw [polyU3, polyU3] <;> ring
theorem flipU4 (x : ℝ) : chebU 4 (-x) = chebU 4 x := by
  rw [polyU4, polyU4] <;> ring
theorem flipU5 (x : ℝ) : chebU 5 (-x) = -chebU 5 x := by
  rw [polyU5, polyU5] <;> ring
theorem flipU6 (x : ℝ) : chebU 6 (-x) = chebU 6 x := by
  rw [polyU6, polyU6] <;> ring
theorem flipU8 (x : ℝ) : chebU 8 (-x) = chebU 8 x := by
  rw [polyU8, polyU8] <;> ring
theorem flipU10 (x : ℝ) : chebU 10 (-x) = chebU 10 x := by
  rw [polyU10, polyU10] <;> ring
theorem flipU12 (x : ℝ) : chebU 12 (-x) = chebU 12 x := by
  rw [polyU12, polyU12] <;> ring
theorem flipU14 (x : ℝ) : chebU 14 (-x) = chebU 14 x := by
  rw [polyU14, polyU14] <;> ring
theorem flipU16 (x : ℝ) : chebU 16 (-x) = chebU 16 x := by
  rw [polyU16, polyU16] <;> ring
theorem flipU18 (x : ℝ) : chebU 18 (-x) = chebU 18 x := by
  rw [polyU18, polyU18] <;> ring
theorem flipU20 (x : ℝ) : chebU 20 (-x) = chebU 20 x := by
  rw [polyU20, polyU20] <;> ring

theorem reflection (x y : ℝ) : polynomial (-x) (-y) = polynomial x y := by
  simp only [polynomial, evalTable, posTable, negTable, flipT0, flipT1, flipT2, flipT3, flipT4, flipT5, flipT6, flipT8, flipT9, flipT10, flipT12, flipT13, flipT14, flipT16, flipT18, flipT19, flipT20, flipU0, flipU1, flipU2, flipU3, flipU4, flipU5, flipU6, flipU8, flipU10, flipU12, flipU14, flipU16, flipU18, flipU20]
  ring
end EllipticBernstein.SmoothDegree20
