import BernsteinOcticCore
import EllipticWeyl

/-! An octic polynomial tuned directly for the linear smoothing gain.
The theorem about the final ratio is exact rational arithmetic. -/
namespace EllipticBernstein.SmoothOctic

open EllipticBernstein


def posTable : List Entry :=
  [(0,0,470377), (0,2,412947), (0,4,30575), (0,6,2364), (1,1,1000000), (1,3,247736), (2,0,460679), (2,2,338826), (2,6,1821), (3,1,193459), (3,3,2514), (4,0,37617), (4,8,203), (5,5,204), (6,0,2046), (6,2,888), (8,4,115)]

def negTable : List Entry :=
  [(0,8,675), (8,0,339)]

def polynomial (x y : ℝ) : ℝ := evalTable x y posTable - evalTable x y negTable
theorem negative_terms_are_free : negTable.all (fun e => decide (e.1 = 0 ∨ e.2.1 = 0)) = true := by decide +kernel

def interior : Octic.Net :=
  ⟨⟨6796002, 27628628, 45477732, 27114020, 3794312, (-4931972), 1237756, (-220404), 17718⟩, ⟨24346964, 77798232, 49513080, (-8601992), (-218639520), 25410440, 2073352, 2032296, (-254516)⟩, ⟨31649828, (-4715720), (-285624936), (-276622504), (-506848352), 120142888, (-49277976), (-20515512), 817852⟩, ⟨18773476, 68618360, 96938136, 177244440, 254671008, 740553960, 534991336, 152920456, 3800828⟩, ⟨(-23547640), (-373993440), (-745864160), (-237621280), 615749040, (-237621280), (-745864160), (-373993440), (-23547640)⟩, ⟨3800828, 152920456, 534991336, 740553960, 254671008, 177244440, 96938136, 68618360, 18773476⟩, ⟨817852, (-20515512), (-49277976), 120142888, (-506848352), (-276622504), (-285624936), (-4715720), 31649828⟩, ⟨(-254516), 2032296, 2073352, 25410440, (-218639520), (-8601992), 49513080, 77798232, 24346964⟩, ⟨17718, (-220404), 1237756, (-4931972), 3794312, 27114020, 45477732, 27628628, 6796002⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem interior_certified : Octic.cert 13 true interior = true := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem interior_identity (x y : ℝ) :
    Octic.netValue interior (x+1) (1-x) (y+1) (1-y) = 65536*polynomial x y := by
  norm_num [interior, Octic.netValue, Octic.rowValue, Octic.map9, Octic.value, polynomial, evalTable, posTable, negTable, chebU, chebT]
  ring

theorem interior_nonnegative (x y : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1) : 0 ≤ polynomial x y := by
  have hp : Octic.positiveOn interior := Octic.cert_sound 13 true _ interior_certified
  have h := hp (x+1) (1-x) (y+1) (1-y)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [interior_identity] at h
  linarith

def pole : ℚ := ((weightAt 0 0 posTable : ℚ)-weightAt 0 0 negTable) / weightAt 1 1 posTable
def slope : ℚ := (Weyl.sumCost posTable - Weyl.sumCost negTable) / weightAt 1 1 posTable
def gain : ℚ := 13/8*((95181399549361514143/344366740312739020800)-(315/796)*pole)

theorem target_and_pole : weightAt 1 1 posTable = 1000000 ∧ weightAt 1 1 negTable = 0 ∧ pole = 470377/1000000 := by decide +kernel
theorem exact_cost : slope = 85398805176211663/94275997200000000 := by decide +kernel
theorem exact_gain : gain = 50505659116627493840711/344366740312739020800000 := by decide +kernel
theorem ratio_lt : slope/gain < 617635/100000 := by decide +kernel
theorem positive_gain : 0 < gain := by decide +kernel

#print axioms interior_nonnegative
#print axioms ratio_lt
end EllipticBernstein.SmoothOctic
