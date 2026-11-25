import Research.Tilt12Rows
import Research.Tilt12Columns

namespace EllipticBernstein.Tilt12
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

theorem half_identity (a b y : ℝ) : Degree12.netValue interior a b (y+1) (1-y) = 4096*(col_0 a b * chebT 0 y + col_1 a b * chebT 1 y + col_2 a b * chebT 2 y + col_4 a b * chebT 4 y + col_5 a b * chebT 5 y + col_6 a b * chebT 6 y + col_8 a b * chebT 8 y + col_10 a b * chebT 10 y + col_12 a b * chebT 12 y) := by
  simp only [Degree12.netValue,Degree12.mapC,Degree12.value,row_0,row_1,row_2,row_3,row_4,row_5,row_6,row_7,row_8,row_9,row_10,row_11,row_12,col_0,col_1,col_2,col_4,col_5,col_6,col_8,col_10,col_12]
  ring
theorem interior_identity (x y : ℝ) : Degree12.netValue interior (x+1) (1-x) (y+1) (1-y) = 16777216*polynomial x y := by
  rw [half_identity,col_id_0,col_id_1,col_id_2,col_id_4,col_id_5,col_id_6,col_id_8,col_id_10,col_id_12]
  norm_num only [polynomial,evalTable,posTable,negTable,Nat.cast_ofNat]
  ring
end EllipticBernstein.Tilt12
