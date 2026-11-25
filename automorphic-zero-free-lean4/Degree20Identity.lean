import Degree20Rows
import Degree20Columns

namespace EllipticBernstein.SmoothDegree20
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem half_identity (a b y : ℝ) : Degree20.netValue interior a b (y+1) (1-y) = 1048576*(column_0 a b * chebT 0 y + column_1 a b * chebT 1 y + column_2 a b * chebT 2 y + column_3 a b * chebT 3 y + column_4 a b * chebT 4 y + column_5 a b * chebT 5 y + column_6 a b * chebT 6 y + column_8 a b * chebT 8 y + column_9 a b * chebT 9 y + column_10 a b * chebT 10 y + column_12 a b * chebT 12 y + column_13 a b * chebT 13 y + column_14 a b * chebT 14 y + column_16 a b * chebT 16 y + column_18 a b * chebT 18 y + column_19 a b * chebT 19 y + column_20 a b * chebT 20 y) := by
  simp only [Degree20.netValue, Degree20.mapC, Degree20.value, interior_row_0, interior_row_1, interior_row_2, interior_row_3, interior_row_4, interior_row_5, interior_row_6, interior_row_7, interior_row_8, interior_row_9, interior_row_10, interior_row_11, interior_row_12, interior_row_13, interior_row_14, interior_row_15, interior_row_16, interior_row_17, interior_row_18, interior_row_19, interior_row_20, column_0, column_1, column_2, column_3, column_4, column_5, column_6, column_8, column_9, column_10, column_12, column_13, column_14, column_16, column_18, column_19, column_20]
  ring
theorem interior_identity (x y : ℝ) :
    Degree20.netValue interior (x+1) (1-x) (y+1) (1-y) = 1099511627776*polynomial x y := by
  rw [half_identity, column_id_0, column_id_1, column_id_2, column_id_3, column_id_4, column_id_5, column_id_6, column_id_8, column_id_9, column_id_10, column_id_12, column_id_13, column_id_14, column_id_16, column_id_18, column_id_19, column_id_20]
  norm_num only [polynomial, evalTable, posTable, negTable, Nat.cast_ofNat]
  ring

end EllipticBernstein.SmoothDegree20
