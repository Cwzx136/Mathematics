import BernsteinOcticCore
import EllipticWeyl

/-! An octic local trace test with Sym² as its only moving nonscalar factor.
The theorem about the final ratio is exact rational arithmetic. -/
namespace EllipticBernstein.SquarePrior

open EllipticBernstein


def posTable : List Entry :=
  [(0,0,651818), (0,2,453334), (0,4,265488), (0,8,13385), (1,0,210217), (2,0,265069), (4,0,13916), (6,0,2978), (8,0,660), (1,2,1000000)]

def negTable : List Entry :=
  [(0,6,81161), (3,0,42747), (5,0,6009), (7,0,1527)]

def polynomial (x y : ℝ) : ℝ := evalTable x y posTable - evalTable x y negTable
theorem negative_terms_are_free : negTable.all (fun e => decide (e.1 = 0 ∨ e.2.1 = 0)) = true := by decide +kernel

def interior : Octic.Net :=
  ⟨⟨14287, 2450428, 32225464, 91801580, 187250094, 190007220, 122669696, 42607588, 6334155⟩, ⟨(-622824), (-18293536), 13164352, 21133920, 326402352, 358779040, 288718208, 110963744, 17936120⟩, ⟨11018852, (-38437488), (-144360160), (-866902064), (-733680248), (-805144144), (-299921664), (-66037008), (-4024844)⟩, ⟨(-111079768), (-1237814752), (-4688009536), (-11204382560), (-14145583536), (-12424866720), (-6343132544), (-1869013792), (-237167160)⟩, ⟨631727898, 4577352424, 15436161104, 28306867848, 34858453140, 26221262648, 12807257344, 3548353624, 434118658⟩, ⟨(-111079768), (-1237814752), (-4688009536), (-11204382560), (-14145583536), (-12424866720), (-6343132544), (-1869013792), (-237167160)⟩, ⟨11018852, (-38437488), (-144360160), (-866902064), (-733680248), (-805144144), (-299921664), (-66037008), (-4024844)⟩, ⟨(-622824), (-18293536), 13164352, 21133920, 326402352, 358779040, 288718208, 110963744, 17936120⟩, ⟨14287, 2450428, 32225464, 91801580, 187250094, 190007220, 122669696, 42607588, 6334155⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem interior_certified : Octic.cert 11 true interior = true := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem interior_identity (x y : ℝ) :
    Octic.netValue interior (x+1) (1-x) (y+1) (1-y) = 65536*polynomial x y := by
  norm_num [interior, Octic.netValue, Octic.rowValue, Octic.map9, Octic.value, polynomial, evalTable, posTable, negTable, chebU, chebT]
  ring

theorem interior_nonnegative (x y : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1) : 0 ≤ polynomial x y := by
  have hp : Octic.positiveOn interior := Octic.cert_sound 11 true _ interior_certified
  have h := hp (x+1) (1-x) (y+1) (1-y)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [interior_identity] at h
  linarith


def pole : ℚ := ((weightAt 0 0 posTable : ℚ)-weightAt 0 0 negTable)/1000000
def slope : ℚ := (Weyl.sumCost posTable-Weyl.sumCost negTable)/1000000

theorem only_square_moves :
    posTable.all (fun e => decide (e.1 = 0 ∨ e.2.1 = 0 ∨ (e.1=1 ∧ e.2.1=2))) = true := by decide +kernel
theorem coefficients : weightAt 1 2 posTable = 1000000 ∧ pole = 325909/500000 ∧ slope = 139/186 := by decide +kernel

#print axioms interior_nonnegative
#print axioms coefficients
end EllipticBernstein.SquarePrior
