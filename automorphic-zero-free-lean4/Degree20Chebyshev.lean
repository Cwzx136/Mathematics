import Degree20Table

namespace EllipticBernstein.SmoothDegree20
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem polyT0 (x : ℝ) : chebT 0 x = (1:ℝ)*(x^0) := by
  simp [chebT] <;> ring
theorem polyT1 (x : ℝ) : chebT 1 x = (1:ℝ)*(x^1) := by
  simp [chebT] <;> ring
theorem polyT2 (x : ℝ) : chebT 2 x = (-1:ℝ)*(x^0) + (2:ℝ)*(x^2) := by
  change 2*x*chebT 1 x-chebT 0 x = _
  rw [polyT1, polyT0]
  ring
theorem polyT3 (x : ℝ) : chebT 3 x = (-3:ℝ)*(x^1) + (4:ℝ)*(x^3) := by
  change 2*x*chebT 2 x-chebT 1 x = _
  rw [polyT2, polyT1]
  ring
theorem polyT4 (x : ℝ) : chebT 4 x = (1:ℝ)*(x^0) + (-8:ℝ)*(x^2) + (8:ℝ)*(x^4) := by
  change 2*x*chebT 3 x-chebT 2 x = _
  rw [polyT3, polyT2]
  ring
theorem polyT5 (x : ℝ) : chebT 5 x = (5:ℝ)*(x^1) + (-20:ℝ)*(x^3) + (16:ℝ)*(x^5) := by
  change 2*x*chebT 4 x-chebT 3 x = _
  rw [polyT4, polyT3]
  ring
theorem polyT6 (x : ℝ) : chebT 6 x = (-1:ℝ)*(x^0) + (18:ℝ)*(x^2) + (-48:ℝ)*(x^4) + (32:ℝ)*(x^6) := by
  change 2*x*chebT 5 x-chebT 4 x = _
  rw [polyT5, polyT4]
  ring
theorem polyT7 (x : ℝ) : chebT 7 x = (-7:ℝ)*(x^1) + (56:ℝ)*(x^3) + (-112:ℝ)*(x^5) + (64:ℝ)*(x^7) := by
  change 2*x*chebT 6 x-chebT 5 x = _
  rw [polyT6, polyT5]
  ring
theorem polyT8 (x : ℝ) : chebT 8 x = (1:ℝ)*(x^0) + (-32:ℝ)*(x^2) + (160:ℝ)*(x^4) + (-256:ℝ)*(x^6) + (128:ℝ)*(x^8) := by
  change 2*x*chebT 7 x-chebT 6 x = _
  rw [polyT7, polyT6]
  ring
theorem polyT9 (x : ℝ) : chebT 9 x = (9:ℝ)*(x^1) + (-120:ℝ)*(x^3) + (432:ℝ)*(x^5) + (-576:ℝ)*(x^7) + (256:ℝ)*(x^9) := by
  change 2*x*chebT 8 x-chebT 7 x = _
  rw [polyT8, polyT7]
  ring
theorem polyT10 (x : ℝ) : chebT 10 x = (-1:ℝ)*(x^0) + (50:ℝ)*(x^2) + (-400:ℝ)*(x^4) + (1120:ℝ)*(x^6) + (-1280:ℝ)*(x^8) + (512:ℝ)*(x^10) := by
  change 2*x*chebT 9 x-chebT 8 x = _
  rw [polyT9, polyT8]
  ring
theorem polyT11 (x : ℝ) : chebT 11 x = (-11:ℝ)*(x^1) + (220:ℝ)*(x^3) + (-1232:ℝ)*(x^5) + (2816:ℝ)*(x^7) + (-2816:ℝ)*(x^9) + (1024:ℝ)*(x^11) := by
  change 2*x*chebT 10 x-chebT 9 x = _
  rw [polyT10, polyT9]
  ring
theorem polyT12 (x : ℝ) : chebT 12 x = (1:ℝ)*(x^0) + (-72:ℝ)*(x^2) + (840:ℝ)*(x^4) + (-3584:ℝ)*(x^6) + (6912:ℝ)*(x^8) + (-6144:ℝ)*(x^10) + (2048:ℝ)*(x^12) := by
  change 2*x*chebT 11 x-chebT 10 x = _
  rw [polyT11, polyT10]
  ring
theorem polyT13 (x : ℝ) : chebT 13 x = (13:ℝ)*(x^1) + (-364:ℝ)*(x^3) + (2912:ℝ)*(x^5) + (-9984:ℝ)*(x^7) + (16640:ℝ)*(x^9) + (-13312:ℝ)*(x^11) + (4096:ℝ)*(x^13) := by
  change 2*x*chebT 12 x-chebT 11 x = _
  rw [polyT12, polyT11]
  ring
theorem polyT14 (x : ℝ) : chebT 14 x = (-1:ℝ)*(x^0) + (98:ℝ)*(x^2) + (-1568:ℝ)*(x^4) + (9408:ℝ)*(x^6) + (-26880:ℝ)*(x^8) + (39424:ℝ)*(x^10) + (-28672:ℝ)*(x^12) + (8192:ℝ)*(x^14) := by
  change 2*x*chebT 13 x-chebT 12 x = _
  rw [polyT13, polyT12]
  ring
theorem polyT15 (x : ℝ) : chebT 15 x = (-15:ℝ)*(x^1) + (560:ℝ)*(x^3) + (-6048:ℝ)*(x^5) + (28800:ℝ)*(x^7) + (-70400:ℝ)*(x^9) + (92160:ℝ)*(x^11) + (-61440:ℝ)*(x^13) + (16384:ℝ)*(x^15) := by
  change 2*x*chebT 14 x-chebT 13 x = _
  rw [polyT14, polyT13]
  ring
theorem polyT16 (x : ℝ) : chebT 16 x = (1:ℝ)*(x^0) + (-128:ℝ)*(x^2) + (2688:ℝ)*(x^4) + (-21504:ℝ)*(x^6) + (84480:ℝ)*(x^8) + (-180224:ℝ)*(x^10) + (212992:ℝ)*(x^12) + (-131072:ℝ)*(x^14) + (32768:ℝ)*(x^16) := by
  change 2*x*chebT 15 x-chebT 14 x = _
  rw [polyT15, polyT14]
  ring
theorem polyT17 (x : ℝ) : chebT 17 x = (17:ℝ)*(x^1) + (-816:ℝ)*(x^3) + (11424:ℝ)*(x^5) + (-71808:ℝ)*(x^7) + (239360:ℝ)*(x^9) + (-452608:ℝ)*(x^11) + (487424:ℝ)*(x^13) + (-278528:ℝ)*(x^15) + (65536:ℝ)*(x^17) := by
  change 2*x*chebT 16 x-chebT 15 x = _
  rw [polyT16, polyT15]
  ring
theorem polyT18 (x : ℝ) : chebT 18 x = (-1:ℝ)*(x^0) + (162:ℝ)*(x^2) + (-4320:ℝ)*(x^4) + (44352:ℝ)*(x^6) + (-228096:ℝ)*(x^8) + (658944:ℝ)*(x^10) + (-1118208:ℝ)*(x^12) + (1105920:ℝ)*(x^14) + (-589824:ℝ)*(x^16) + (131072:ℝ)*(x^18) := by
  change 2*x*chebT 17 x-chebT 16 x = _
  rw [polyT17, polyT16]
  ring
theorem polyT19 (x : ℝ) : chebT 19 x = (-19:ℝ)*(x^1) + (1140:ℝ)*(x^3) + (-20064:ℝ)*(x^5) + (160512:ℝ)*(x^7) + (-695552:ℝ)*(x^9) + (1770496:ℝ)*(x^11) + (-2723840:ℝ)*(x^13) + (2490368:ℝ)*(x^15) + (-1245184:ℝ)*(x^17) + (262144:ℝ)*(x^19) := by
  change 2*x*chebT 18 x-chebT 17 x = _
  rw [polyT18, polyT17]
  ring
theorem polyT20 (x : ℝ) : chebT 20 x = (1:ℝ)*(x^0) + (-200:ℝ)*(x^2) + (6600:ℝ)*(x^4) + (-84480:ℝ)*(x^6) + (549120:ℝ)*(x^8) + (-2050048:ℝ)*(x^10) + (4659200:ℝ)*(x^12) + (-6553600:ℝ)*(x^14) + (5570560:ℝ)*(x^16) + (-2621440:ℝ)*(x^18) + (524288:ℝ)*(x^20) := by
  change 2*x*chebT 19 x-chebT 18 x = _
  rw [polyT19, polyT18]
  ring
theorem polyU0 (x : ℝ) : chebU 0 x = (1:ℝ)*(x^0) := by
  simp [chebU] <;> ring
theorem polyU1 (x : ℝ) : chebU 1 x = (2:ℝ)*(x^1) := by
  simp [chebU] <;> ring
theorem polyU2 (x : ℝ) : chebU 2 x = (-1:ℝ)*(x^0) + (4:ℝ)*(x^2) := by
  change 2*x*chebU 1 x-chebU 0 x = _
  rw [polyU1, polyU0]
  ring
theorem polyU3 (x : ℝ) : chebU 3 x = (-4:ℝ)*(x^1) + (8:ℝ)*(x^3) := by
  change 2*x*chebU 2 x-chebU 1 x = _
  rw [polyU2, polyU1]
  ring
theorem polyU4 (x : ℝ) : chebU 4 x = (1:ℝ)*(x^0) + (-12:ℝ)*(x^2) + (16:ℝ)*(x^4) := by
  change 2*x*chebU 3 x-chebU 2 x = _
  rw [polyU3, polyU2]
  ring
theorem polyU5 (x : ℝ) : chebU 5 x = (6:ℝ)*(x^1) + (-32:ℝ)*(x^3) + (32:ℝ)*(x^5) := by
  change 2*x*chebU 4 x-chebU 3 x = _
  rw [polyU4, polyU3]
  ring
theorem polyU6 (x : ℝ) : chebU 6 x = (-1:ℝ)*(x^0) + (24:ℝ)*(x^2) + (-80:ℝ)*(x^4) + (64:ℝ)*(x^6) := by
  change 2*x*chebU 5 x-chebU 4 x = _
  rw [polyU5, polyU4]
  ring
theorem polyU7 (x : ℝ) : chebU 7 x = (-8:ℝ)*(x^1) + (80:ℝ)*(x^3) + (-192:ℝ)*(x^5) + (128:ℝ)*(x^7) := by
  change 2*x*chebU 6 x-chebU 5 x = _
  rw [polyU6, polyU5]
  ring
theorem polyU8 (x : ℝ) : chebU 8 x = (1:ℝ)*(x^0) + (-40:ℝ)*(x^2) + (240:ℝ)*(x^4) + (-448:ℝ)*(x^6) + (256:ℝ)*(x^8) := by
  change 2*x*chebU 7 x-chebU 6 x = _
  rw [polyU7, polyU6]
  ring
theorem polyU9 (x : ℝ) : chebU 9 x = (10:ℝ)*(x^1) + (-160:ℝ)*(x^3) + (672:ℝ)*(x^5) + (-1024:ℝ)*(x^7) + (512:ℝ)*(x^9) := by
  change 2*x*chebU 8 x-chebU 7 x = _
  rw [polyU8, polyU7]
  ring
theorem polyU10 (x : ℝ) : chebU 10 x = (-1:ℝ)*(x^0) + (60:ℝ)*(x^2) + (-560:ℝ)*(x^4) + (1792:ℝ)*(x^6) + (-2304:ℝ)*(x^8) + (1024:ℝ)*(x^10) := by
  change 2*x*chebU 9 x-chebU 8 x = _
  rw [polyU9, polyU8]
  ring
theorem polyU11 (x : ℝ) : chebU 11 x = (-12:ℝ)*(x^1) + (280:ℝ)*(x^3) + (-1792:ℝ)*(x^5) + (4608:ℝ)*(x^7) + (-5120:ℝ)*(x^9) + (2048:ℝ)*(x^11) := by
  change 2*x*chebU 10 x-chebU 9 x = _
  rw [polyU10, polyU9]
  ring
theorem polyU12 (x : ℝ) : chebU 12 x = (1:ℝ)*(x^0) + (-84:ℝ)*(x^2) + (1120:ℝ)*(x^4) + (-5376:ℝ)*(x^6) + (11520:ℝ)*(x^8) + (-11264:ℝ)*(x^10) + (4096:ℝ)*(x^12) := by
  change 2*x*chebU 11 x-chebU 10 x = _
  rw [polyU11, polyU10]
  ring
theorem polyU13 (x : ℝ) : chebU 13 x = (14:ℝ)*(x^1) + (-448:ℝ)*(x^3) + (4032:ℝ)*(x^5) + (-15360:ℝ)*(x^7) + (28160:ℝ)*(x^9) + (-24576:ℝ)*(x^11) + (8192:ℝ)*(x^13) := by
  change 2*x*chebU 12 x-chebU 11 x = _
  rw [polyU12, polyU11]
  ring
theorem polyU14 (x : ℝ) : chebU 14 x = (-1:ℝ)*(x^0) + (112:ℝ)*(x^2) + (-2016:ℝ)*(x^4) + (13440:ℝ)*(x^6) + (-42240:ℝ)*(x^8) + (67584:ℝ)*(x^10) + (-53248:ℝ)*(x^12) + (16384:ℝ)*(x^14) := by
  change 2*x*chebU 13 x-chebU 12 x = _
  rw [polyU13, polyU12]
  ring
theorem polyU15 (x : ℝ) : chebU 15 x = (-16:ℝ)*(x^1) + (672:ℝ)*(x^3) + (-8064:ℝ)*(x^5) + (42240:ℝ)*(x^7) + (-112640:ℝ)*(x^9) + (159744:ℝ)*(x^11) + (-114688:ℝ)*(x^13) + (32768:ℝ)*(x^15) := by
  change 2*x*chebU 14 x-chebU 13 x = _
  rw [polyU14, polyU13]
  ring
theorem polyU16 (x : ℝ) : chebU 16 x = (1:ℝ)*(x^0) + (-144:ℝ)*(x^2) + (3360:ℝ)*(x^4) + (-29568:ℝ)*(x^6) + (126720:ℝ)*(x^8) + (-292864:ℝ)*(x^10) + (372736:ℝ)*(x^12) + (-245760:ℝ)*(x^14) + (65536:ℝ)*(x^16) := by
  change 2*x*chebU 15 x-chebU 14 x = _
  rw [polyU15, polyU14]
  ring
theorem polyU17 (x : ℝ) : chebU 17 x = (18:ℝ)*(x^1) + (-960:ℝ)*(x^3) + (14784:ℝ)*(x^5) + (-101376:ℝ)*(x^7) + (366080:ℝ)*(x^9) + (-745472:ℝ)*(x^11) + (860160:ℝ)*(x^13) + (-524288:ℝ)*(x^15) + (131072:ℝ)*(x^17) := by
  change 2*x*chebU 16 x-chebU 15 x = _
  rw [polyU16, polyU15]
  ring
theorem polyU18 (x : ℝ) : chebU 18 x = (-1:ℝ)*(x^0) + (180:ℝ)*(x^2) + (-5280:ℝ)*(x^4) + (59136:ℝ)*(x^6) + (-329472:ℝ)*(x^8) + (1025024:ℝ)*(x^10) + (-1863680:ℝ)*(x^12) + (1966080:ℝ)*(x^14) + (-1114112:ℝ)*(x^16) + (262144:ℝ)*(x^18) := by
  change 2*x*chebU 17 x-chebU 16 x = _
  rw [polyU17, polyU16]
  ring
theorem polyU19 (x : ℝ) : chebU 19 x = (-20:ℝ)*(x^1) + (1320:ℝ)*(x^3) + (-25344:ℝ)*(x^5) + (219648:ℝ)*(x^7) + (-1025024:ℝ)*(x^9) + (2795520:ℝ)*(x^11) + (-4587520:ℝ)*(x^13) + (4456448:ℝ)*(x^15) + (-2359296:ℝ)*(x^17) + (524288:ℝ)*(x^19) := by
  change 2*x*chebU 18 x-chebU 17 x = _
  rw [polyU18, polyU17]
  ring
theorem polyU20 (x : ℝ) : chebU 20 x = (1:ℝ)*(x^0) + (-220:ℝ)*(x^2) + (7920:ℝ)*(x^4) + (-109824:ℝ)*(x^6) + (768768:ℝ)*(x^8) + (-3075072:ℝ)*(x^10) + (7454720:ℝ)*(x^12) + (-11141120:ℝ)*(x^14) + (10027008:ℝ)*(x^16) + (-4980736:ℝ)*(x^18) + (1048576:ℝ)*(x^20) := by
  change 2*x*chebU 19 x-chebU 18 x = _
  rw [polyU19, polyU18]
  ring

end EllipticBernstein.SmoothDegree20
