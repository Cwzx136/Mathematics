import Research.Tilt12Chebyshev

namespace EllipticBernstein.Tilt12
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

theorem row_0 (y : ℝ) : Degree12.rowValue interior.a (y+1) (1-y) = 4096*((1403087:ℝ)*(chebT 0 y) + (-2000000:ℝ)*(chebT 1 y) + (750191:ℝ)*(chebT 2 y) + (-10530:ℝ)*(chebT 4 y) + (-27956:ℝ)*(chebT 5 y) + (6639:ℝ)*(chebT 6 y) + (3121:ℝ)*(chebT 8 y) + (-130:ℝ)*(chebT 10 y) + (-10:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_1 (y : ℝ) : Degree12.rowValue interior.b (y+1) (1-y) = 4096*((12835156:ℝ)*(chebT 0 y) + (-20000000:ℝ)*(chebT 1 y) + (6705428:ℝ)*(chebT 2 y) + (-126360:ℝ)*(chebT 4 y) + (-279560:ℝ)*(chebT 5 y) + (79668:ℝ)*(chebT 6 y) + (22348:ℝ)*(chebT 8 y) + (-1560:ℝ)*(chebT 10 y) + (-120:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_2 (y : ℝ) : Degree12.rowValue interior.c (y+1) (1-y) = 4096*((84233118:ℝ)*(chebT 0 y) + (-88000000:ℝ)*(chebT 1 y) + (26543966:ℝ)*(chebT 2 y) + (-694980:ℝ)*(chebT 4 y) + (-1230064:ℝ)*(chebT 5 y) + (438174:ℝ)*(chebT 6 y) + (54946:ℝ)*(chebT 8 y) + (-8580:ℝ)*(chebT 10 y) + (-660:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_3 (y : ℝ) : Degree12.rowValue interior.d (y+1) (1-y) = 4096*((-149253884:ℝ)*(chebT 0 y) + (-220000000:ℝ)*(chebT 1 y) + (61683140:ℝ)*(chebT 2 y) + (-2316600:ℝ)*(chebT 4 y) + (-3075160:ℝ)*(chebT 5 y) + (1460580:ℝ)*(chebT 6 y) + (6940:ℝ)*(chebT 8 y) + (-28600:ℝ)*(chebT 10 y) + (-2200:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_4 (y : ℝ) : Degree12.rowValue interior.e (y+1) (1-y) = 4096*((2047275841:ℝ)*(chebT 0 y) + (-330000000:ℝ)*(chebT 1 y) + (95720865:ℝ)*(chebT 2 y) + (-5212350:ℝ)*(chebT 4 y) + (-4612740:ℝ)*(chebT 5 y) + (3286305:ℝ)*(chebT 6 y) + (-267585:ℝ)*(chebT 8 y) + (-64350:ℝ)*(chebT 10 y) + (-4950:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_5 (y : ℝ) : Degree12.rowValue interior.f (y+1) (1-y) = 4096*((-4736159320:ℝ)*(chebT 0 y) + (-264000000:ℝ)*(chebT 1 y) + (111809832:ℝ)*(chebT 2 y) + (-8339760:ℝ)*(chebT 4 y) + (-3690192:ℝ)*(chebT 5 y) + (5258088:ℝ)*(chebT 6 y) + (-700008:ℝ)*(chebT 8 y) + (-102960:ℝ)*(chebT 10 y) + (-7920:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_6 (y : ℝ) : Degree12.rowValue interior.g (y+1) (1-y) = 4096*((6272673956:ℝ)*(chebT 0 y) + (114366756:ℝ)*(chebT 2 y) + (-9729720:ℝ)*(chebT 4 y) + (6134436:ℝ)*(chebT 6 y) + (-922404:ℝ)*(chebT 8 y) + (-120120:ℝ)*(chebT 10 y) + (-9240:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_7 (y : ℝ) : Degree12.rowValue interior.h (y+1) (1-y) = 4096*((-4736159320:ℝ)*(chebT 0 y) + (264000000:ℝ)*(chebT 1 y) + (111809832:ℝ)*(chebT 2 y) + (-8339760:ℝ)*(chebT 4 y) + (3690192:ℝ)*(chebT 5 y) + (5258088:ℝ)*(chebT 6 y) + (-700008:ℝ)*(chebT 8 y) + (-102960:ℝ)*(chebT 10 y) + (-7920:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_8 (y : ℝ) : Degree12.rowValue interior.i (y+1) (1-y) = 4096*((2047275841:ℝ)*(chebT 0 y) + (330000000:ℝ)*(chebT 1 y) + (95720865:ℝ)*(chebT 2 y) + (-5212350:ℝ)*(chebT 4 y) + (4612740:ℝ)*(chebT 5 y) + (3286305:ℝ)*(chebT 6 y) + (-267585:ℝ)*(chebT 8 y) + (-64350:ℝ)*(chebT 10 y) + (-4950:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_9 (y : ℝ) : Degree12.rowValue interior.j (y+1) (1-y) = 4096*((-149253884:ℝ)*(chebT 0 y) + (220000000:ℝ)*(chebT 1 y) + (61683140:ℝ)*(chebT 2 y) + (-2316600:ℝ)*(chebT 4 y) + (3075160:ℝ)*(chebT 5 y) + (1460580:ℝ)*(chebT 6 y) + (6940:ℝ)*(chebT 8 y) + (-28600:ℝ)*(chebT 10 y) + (-2200:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_10 (y : ℝ) : Degree12.rowValue interior.k (y+1) (1-y) = 4096*((84233118:ℝ)*(chebT 0 y) + (88000000:ℝ)*(chebT 1 y) + (26543966:ℝ)*(chebT 2 y) + (-694980:ℝ)*(chebT 4 y) + (1230064:ℝ)*(chebT 5 y) + (438174:ℝ)*(chebT 6 y) + (54946:ℝ)*(chebT 8 y) + (-8580:ℝ)*(chebT 10 y) + (-660:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_11 (y : ℝ) : Degree12.rowValue interior.l (y+1) (1-y) = 4096*((12835156:ℝ)*(chebT 0 y) + (20000000:ℝ)*(chebT 1 y) + (6705428:ℝ)*(chebT 2 y) + (-126360:ℝ)*(chebT 4 y) + (279560:ℝ)*(chebT 5 y) + (79668:ℝ)*(chebT 6 y) + (22348:ℝ)*(chebT 8 y) + (-1560:ℝ)*(chebT 10 y) + (-120:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
theorem row_12 (y : ℝ) : Degree12.rowValue interior.m (y+1) (1-y) = 4096*((1403087:ℝ)*(chebT 0 y) + (2000000:ℝ)*(chebT 1 y) + (750191:ℝ)*(chebT 2 y) + (-10530:ℝ)*(chebT 4 y) + (27956:ℝ)*(chebT 5 y) + (6639:ℝ)*(chebT 6 y) + (3121:ℝ)*(chebT 8 y) + (-130:ℝ)*(chebT 10 y) + (-10:ℝ)*(chebT 12 y)) := by
  norm_num only [interior,Degree12.rowValue,Degree12.value,Degree12.mapC,polyT0,polyT1,polyT2,polyT4,polyT5,polyT6,polyT8,polyT10,polyT12,Int.cast_ofNat,Int.cast_neg]
  ring
end EllipticBernstein.Tilt12
