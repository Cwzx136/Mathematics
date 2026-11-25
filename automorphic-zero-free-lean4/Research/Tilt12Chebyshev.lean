import Research.Tilt12Table

namespace EllipticBernstein.Tilt12
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

theorem polyT0 (x : ℝ) : chebT 0 x = (1:ℝ)*(x^0) := by
  simp [chebT]
theorem polyT1 (x : ℝ) : chebT 1 x = (1:ℝ)*(x^1) := by
  simp [chebT]
theorem polyT2 (x : ℝ) : chebT 2 x = (-1:ℝ)*(x^0) + (2:ℝ)*(x^2) := by
  change 2*x*chebT 1 x-chebT 0 x=_
  rw [polyT1,polyT0]
  ring
theorem polyT3 (x : ℝ) : chebT 3 x = (-3:ℝ)*(x^1) + (4:ℝ)*(x^3) := by
  change 2*x*chebT 2 x-chebT 1 x=_
  rw [polyT2,polyT1]
  ring
theorem polyT4 (x : ℝ) : chebT 4 x = (1:ℝ)*(x^0) + (-8:ℝ)*(x^2) + (8:ℝ)*(x^4) := by
  change 2*x*chebT 3 x-chebT 2 x=_
  rw [polyT3,polyT2]
  ring
theorem polyT5 (x : ℝ) : chebT 5 x = (5:ℝ)*(x^1) + (-20:ℝ)*(x^3) + (16:ℝ)*(x^5) := by
  change 2*x*chebT 4 x-chebT 3 x=_
  rw [polyT4,polyT3]
  ring
theorem polyT6 (x : ℝ) : chebT 6 x = (-1:ℝ)*(x^0) + (18:ℝ)*(x^2) + (-48:ℝ)*(x^4) + (32:ℝ)*(x^6) := by
  change 2*x*chebT 5 x-chebT 4 x=_
  rw [polyT5,polyT4]
  ring
theorem polyT7 (x : ℝ) : chebT 7 x = (-7:ℝ)*(x^1) + (56:ℝ)*(x^3) + (-112:ℝ)*(x^5) + (64:ℝ)*(x^7) := by
  change 2*x*chebT 6 x-chebT 5 x=_
  rw [polyT6,polyT5]
  ring
theorem polyT8 (x : ℝ) : chebT 8 x = (1:ℝ)*(x^0) + (-32:ℝ)*(x^2) + (160:ℝ)*(x^4) + (-256:ℝ)*(x^6) + (128:ℝ)*(x^8) := by
  change 2*x*chebT 7 x-chebT 6 x=_
  rw [polyT7,polyT6]
  ring
theorem polyT9 (x : ℝ) : chebT 9 x = (9:ℝ)*(x^1) + (-120:ℝ)*(x^3) + (432:ℝ)*(x^5) + (-576:ℝ)*(x^7) + (256:ℝ)*(x^9) := by
  change 2*x*chebT 8 x-chebT 7 x=_
  rw [polyT8,polyT7]
  ring
theorem polyT10 (x : ℝ) : chebT 10 x = (-1:ℝ)*(x^0) + (50:ℝ)*(x^2) + (-400:ℝ)*(x^4) + (1120:ℝ)*(x^6) + (-1280:ℝ)*(x^8) + (512:ℝ)*(x^10) := by
  change 2*x*chebT 9 x-chebT 8 x=_
  rw [polyT9,polyT8]
  ring
theorem polyT11 (x : ℝ) : chebT 11 x = (-11:ℝ)*(x^1) + (220:ℝ)*(x^3) + (-1232:ℝ)*(x^5) + (2816:ℝ)*(x^7) + (-2816:ℝ)*(x^9) + (1024:ℝ)*(x^11) := by
  change 2*x*chebT 10 x-chebT 9 x=_
  rw [polyT10,polyT9]
  ring
theorem polyT12 (x : ℝ) : chebT 12 x = (1:ℝ)*(x^0) + (-72:ℝ)*(x^2) + (840:ℝ)*(x^4) + (-3584:ℝ)*(x^6) + (6912:ℝ)*(x^8) + (-6144:ℝ)*(x^10) + (2048:ℝ)*(x^12) := by
  change 2*x*chebT 11 x-chebT 10 x=_
  rw [polyT11,polyT10]
  ring
theorem polyU0 (x : ℝ) : chebU 0 x = (1:ℝ)*(x^0) := by
  simp [chebU]
theorem polyU1 (x : ℝ) : chebU 1 x = (2:ℝ)*(x^1) := by
  simp [chebU]
theorem polyU2 (x : ℝ) : chebU 2 x = (-1:ℝ)*(x^0) + (4:ℝ)*(x^2) := by
  change 2*x*chebU 1 x-chebU 0 x=_
  rw [polyU1,polyU0]
  ring
theorem polyU3 (x : ℝ) : chebU 3 x = (-4:ℝ)*(x^1) + (8:ℝ)*(x^3) := by
  change 2*x*chebU 2 x-chebU 1 x=_
  rw [polyU2,polyU1]
  ring
theorem polyU4 (x : ℝ) : chebU 4 x = (1:ℝ)*(x^0) + (-12:ℝ)*(x^2) + (16:ℝ)*(x^4) := by
  change 2*x*chebU 3 x-chebU 2 x=_
  rw [polyU3,polyU2]
  ring
theorem polyU5 (x : ℝ) : chebU 5 x = (6:ℝ)*(x^1) + (-32:ℝ)*(x^3) + (32:ℝ)*(x^5) := by
  change 2*x*chebU 4 x-chebU 3 x=_
  rw [polyU4,polyU3]
  ring
theorem polyU6 (x : ℝ) : chebU 6 x = (-1:ℝ)*(x^0) + (24:ℝ)*(x^2) + (-80:ℝ)*(x^4) + (64:ℝ)*(x^6) := by
  change 2*x*chebU 5 x-chebU 4 x=_
  rw [polyU5,polyU4]
  ring
theorem polyU7 (x : ℝ) : chebU 7 x = (-8:ℝ)*(x^1) + (80:ℝ)*(x^3) + (-192:ℝ)*(x^5) + (128:ℝ)*(x^7) := by
  change 2*x*chebU 6 x-chebU 5 x=_
  rw [polyU6,polyU5]
  ring
theorem polyU8 (x : ℝ) : chebU 8 x = (1:ℝ)*(x^0) + (-40:ℝ)*(x^2) + (240:ℝ)*(x^4) + (-448:ℝ)*(x^6) + (256:ℝ)*(x^8) := by
  change 2*x*chebU 7 x-chebU 6 x=_
  rw [polyU7,polyU6]
  ring
theorem polyU9 (x : ℝ) : chebU 9 x = (10:ℝ)*(x^1) + (-160:ℝ)*(x^3) + (672:ℝ)*(x^5) + (-1024:ℝ)*(x^7) + (512:ℝ)*(x^9) := by
  change 2*x*chebU 8 x-chebU 7 x=_
  rw [polyU8,polyU7]
  ring
theorem polyU10 (x : ℝ) : chebU 10 x = (-1:ℝ)*(x^0) + (60:ℝ)*(x^2) + (-560:ℝ)*(x^4) + (1792:ℝ)*(x^6) + (-2304:ℝ)*(x^8) + (1024:ℝ)*(x^10) := by
  change 2*x*chebU 9 x-chebU 8 x=_
  rw [polyU9,polyU8]
  ring
theorem polyU11 (x : ℝ) : chebU 11 x = (-12:ℝ)*(x^1) + (280:ℝ)*(x^3) + (-1792:ℝ)*(x^5) + (4608:ℝ)*(x^7) + (-5120:ℝ)*(x^9) + (2048:ℝ)*(x^11) := by
  change 2*x*chebU 10 x-chebU 9 x=_
  rw [polyU10,polyU9]
  ring
theorem polyU12 (x : ℝ) : chebU 12 x = (1:ℝ)*(x^0) + (-84:ℝ)*(x^2) + (1120:ℝ)*(x^4) + (-5376:ℝ)*(x^6) + (11520:ℝ)*(x^8) + (-11264:ℝ)*(x^10) + (4096:ℝ)*(x^12) := by
  change 2*x*chebU 11 x-chebU 10 x=_
  rw [polyU11,polyU10]
  ring
end EllipticBernstein.Tilt12
