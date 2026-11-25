import EllipticAmplifier

/-! The coefficient table, the Chebyshev recurrence, and the rank-one saving
in one normalization. The cost includes only frequencies and indices both nonzero. -/
namespace EllipticBernstein

def chebU : Nat → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2*x
  | n+2, x => 2*x*chebU (n+1) x - chebU n x

def chebT : Nat → ℝ → ℝ
  | 0, _ => 1
  | 1, x => x
  | n+2, x => 2*x*chebT (n+1) x - chebT n x

abbrev Entry := Nat × Nat × Nat

/-- An entry is (frequency, symmetric-power index, integer numerator). -/
def originalTable : List Entry :=
  [(0,0,462244), (0,2,444674), (0,4,47038), (0,6,1191),
   (1,1,1000000), (1,3,293292), (2,0,433762), (2,2,343537),
   (2,6,348), (3,1,179116), (3,3,1183), (4,0,33882), (4,6,31),
   (6,0,439), (6,2,110)]

def reducedTable : List Entry := (0,0,462242) :: originalTable.tail

def evalTable (x y : ℝ) : List Entry → ℝ
  | [] => 0
  | (l,j,c)::rest => c * chebU j x * chebT l y + evalTable x y rest

def weightAt (l j : Nat) : List Entry → Nat
  | [] => 0
  | (u,v,c)::rest => (if u=l ∧ v=j then c else 0) + weightAt l j rest

def twiceShiftedNumerator : List Entry → Nat
  | [] => 0
  | (l,j,c)::rest => (if l=0 ∨ j=0 then 0 else (j+1)*c) + twiceShiftedNumerator rest

theorem original_polynomial (x y : ℝ) :
    evalTable x y originalTable = amplifier x y := by
  norm_num [originalTable, evalTable, chebU, chebT, amplifier]; ring

theorem reduced_polynomial (x y : ℝ) :
    evalTable x y reducedTable = amplifier x y - 2 := by
  rw [← original_polynomial]
  simp only [reducedTable, originalTable, List.tail_cons, evalTable, chebU, chebT]
  push_cast
  ring

theorem table_nonnegative (x y : ℝ) (lo : -1 ≤ y) (hi : y ≤ 1) :
    0 ≤ evalTable x y reducedTable := by
  rw [reduced_polynomial]
  exact sub_nonneg.mpr (amplifier_lower x y lo hi)

theorem table_constants :
    weightAt 0 0 reducedTable = 462242 ∧ weightAt 1 1 reducedTable = 1000000 ∧
      twiceShiftedNumerator reducedTable = 4569726 := by decide +kernel

theorem table_width_coefficient :
    let P : ℝ := (weightAt 0 0 reducedTable : ℝ) / weightAt 1 1 reducedTable
    let G : ℝ := (twiceShiftedNumerator reducedTable : ℝ) / (2 * weightAt 1 1 reducedTable)
    (1-1/Real.sqrt 5)*G/(1-Real.sqrt P)^2 < 1232544/100000 := by
  dsimp only
  rw [table_constants.1, table_constants.2.1, table_constants.2.2]
  convert reduced_constant using 1 <;> norm_num [reducedPole, shiftedHalfDegree]

#print axioms table_nonnegative
#print axioms table_width_coefficient
end EllipticBernstein
