import Degree20Chebyshev

namespace EllipticBernstein.SmoothDegree20
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

def column_19 (a b : ℝ) : ℝ := (-142:ℝ)*(a^0*b^20) + (-2556:ℝ)*(a^1*b^19) + (-21584:ℝ)*(a^2*b^18) + (-113316:ℝ)*(a^3*b^17) + (-412794:ℝ)*(a^4*b^16) + (-1100784:ℝ)*(a^5*b^15) + (-2201568:ℝ)*(a^6*b^14) + (-3302352:ℝ)*(a^7*b^13) + (-3577548:ℝ)*(a^8*b^12) + (-2385032:ℝ)*(a^9*b^11) + (2385032:ℝ)*(a^11*b^9) + (3577548:ℝ)*(a^12*b^8) + (3302352:ℝ)*(a^13*b^7) + (2201568:ℝ)*(a^14*b^6) + (1100784:ℝ)*(a^15*b^5) + (412794:ℝ)*(a^16*b^4) + (113316:ℝ)*(a^17*b^3) + (21584:ℝ)*(a^18*b^2) + (2556:ℝ)*(a^19*b^1) + (142:ℝ)*(a^20*b^0)
theorem column_id_19 (x : ℝ) : column_19 (x+1) (1-x) = 1048576*((71:ℝ)*(chebU 1 x)) := by
  norm_num only [column_19, polyU0, polyU1, polyU2, polyU3, polyU4, polyU5, polyU6, polyU8, polyU10, polyU12, polyU14, polyU16, polyU18, polyU20]
  ring
def column_20 (a b : ℝ) : ℝ := (48:ℝ)*(a^0*b^20) + (960:ℝ)*(a^1*b^19) + (9120:ℝ)*(a^2*b^18) + (54720:ℝ)*(a^3*b^17) + (232560:ℝ)*(a^4*b^16) + (744192:ℝ)*(a^5*b^15) + (1860480:ℝ)*(a^6*b^14) + (3720960:ℝ)*(a^7*b^13) + (6046560:ℝ)*(a^8*b^12) + (8062080:ℝ)*(a^9*b^11) + (8868288:ℝ)*(a^10*b^10) + (8062080:ℝ)*(a^11*b^9) + (6046560:ℝ)*(a^12*b^8) + (3720960:ℝ)*(a^13*b^7) + (1860480:ℝ)*(a^14*b^6) + (744192:ℝ)*(a^15*b^5) + (232560:ℝ)*(a^16*b^4) + (54720:ℝ)*(a^17*b^3) + (9120:ℝ)*(a^18*b^2) + (960:ℝ)*(a^19*b^1) + (48:ℝ)*(a^20*b^0)
theorem column_id_20 (x : ℝ) : column_20 (x+1) (1-x) = 1048576*((48:ℝ)*(chebU 0 x)) := by
  norm_num only [column_20, polyU0, polyU1, polyU2, polyU3, polyU4, polyU5, polyU6, polyU8, polyU10, polyU12, polyU14, polyU16, polyU18, polyU20]
  ring
end EllipticBernstein.SmoothDegree20
