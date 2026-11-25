import Research.Tilt12Chebyshev

namespace EllipticBernstein.Tilt12
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

theorem flipT0 (x : ℝ) : chebT 0 (-x) = chebT 0 x := by
  rw [polyT0,polyT0]
  ring
theorem flipT1 (x : ℝ) : chebT 1 (-x) = -chebT 1 x := by
  rw [polyT1,polyT1]
  ring
theorem flipT2 (x : ℝ) : chebT 2 (-x) = chebT 2 x := by
  rw [polyT2,polyT2]
  ring
theorem flipT4 (x : ℝ) : chebT 4 (-x) = chebT 4 x := by
  rw [polyT4,polyT4]
  ring
theorem flipT5 (x : ℝ) : chebT 5 (-x) = -chebT 5 x := by
  rw [polyT5,polyT5]
  ring
theorem flipT6 (x : ℝ) : chebT 6 (-x) = chebT 6 x := by
  rw [polyT6,polyT6]
  ring
theorem flipT8 (x : ℝ) : chebT 8 (-x) = chebT 8 x := by
  rw [polyT8,polyT8]
  ring
theorem flipT10 (x : ℝ) : chebT 10 (-x) = chebT 10 x := by
  rw [polyT10,polyT10]
  ring
theorem flipT12 (x : ℝ) : chebT 12 (-x) = chebT 12 x := by
  rw [polyT12,polyT12]
  ring
theorem flipU0 (x : ℝ) : chebU 0 (-x) = chebU 0 x := by
  rw [polyU0,polyU0]
  ring
theorem flipU1 (x : ℝ) : chebU 1 (-x) = -chebU 1 x := by
  rw [polyU1,polyU1]
  ring
theorem flipU2 (x : ℝ) : chebU 2 (-x) = chebU 2 x := by
  rw [polyU2,polyU2]
  ring
theorem flipU4 (x : ℝ) : chebU 4 (-x) = chebU 4 x := by
  rw [polyU4,polyU4]
  ring
theorem flipU6 (x : ℝ) : chebU 6 (-x) = chebU 6 x := by
  rw [polyU6,polyU6]
  ring
theorem flipU8 (x : ℝ) : chebU 8 (-x) = chebU 8 x := by
  rw [polyU8,polyU8]
  ring
theorem flipU10 (x : ℝ) : chebU 10 (-x) = chebU 10 x := by
  rw [polyU10,polyU10]
  ring
theorem flipU12 (x : ℝ) : chebU 12 (-x) = chebU 12 x := by
  rw [polyU12,polyU12]
  ring
theorem reflection (x y : ℝ) : polynomial (-x) (-y) = polynomial x y := by
  simp only [polynomial,evalTable,posTable,negTable,flipT0,flipT1,flipT2,flipT4,flipT5,flipT6,flipT8,flipT10,flipT12,flipU0,flipU1,flipU2,flipU4,flipU6,flipU8,flipU10,flipU12]
  ring
end EllipticBernstein.Tilt12
