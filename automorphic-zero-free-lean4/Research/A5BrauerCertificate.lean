import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite character-table certificates for sign-sensitive descent over A₅ and PSL₂(7)

The four coordinates are the values on 1A, 2A, 3A, and the *mean* on 5A and 5B.
The two particular rows in `twoTermIdentity` are constant across 5A and 5B.
The classification of proper subgroups of A₅ and the finite-group
interpretation of these class data are given in the accompanying paper. The
algebra below verifies the exact certificate over ℚ for the specified table.
The second example uses the same construction with the two order-seven classes merged.
-/

open scoped BigOperators

namespace BrauerSupport

/-- A rational dual certificate for separately optimal positive and negative support costs. -/
theorem forceSupport {κ : Type*} (s : Finset κ) (a w e : κ → ℚ) (d : κ → ℕ)
    (p q : ℕ) (hw : ∑ k ∈ s, a k * w k = 1) (hx : ∑ k ∈ s, a k * e k = 0)
    (hrows : ∀ k ∈ s, q ≤ d k ∧ 0 ≤ w k ∧ (d k < p → w k = 0) ∧ 0 < e k) :
    (∃ k ∈ s, 0 < a k ∧ p ≤ d k) ∧ (∃ k ∈ s, a k < 0 ∧ q ≤ d k) := by
  have hp : ∃ k ∈ s, 0 < a k ∧ p ≤ d k := by
    by_contra no
    have hnon : ∀ k ∈ s, a k * w k ≤ 0 := by
      intro k hmem
      by_cases pos : 0 < a k
      · have small : d k < p := lt_of_not_ge (fun j => no ⟨k, hmem, pos, j⟩)
        rw [(hrows k hmem).2.2.1 small, mul_zero]
      · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt pos) (hrows k hmem).2.1
    have bad := Finset.sum_nonpos (s := s) hnon
    rw [hw] at bad
    norm_num at bad
  refine ⟨hp, ?_⟩
  by_contra no
  have hnon : ∀ k ∈ s, 0 ≤ a k := fun k hmem =>
    le_of_not_gt (fun hn => no ⟨k, hmem, hn, (hrows k hmem).1⟩)
  obtain ⟨k, hmem, hk, _⟩ := hp
  have hterm := mul_pos hk (hrows k hmem).2.2.2
  have hsum := Finset.single_le_sum (f := fun i => a i * e i)
    (fun i hi => mul_nonneg (hnon i hi) (hrows i hi).2.2.2.le) hmem
  rw [hx] at hsum
  exact (not_lt_of_ge hsum) hterm


end BrauerSupport

namespace A5BrauerCertificate

/-- Conjugacy-class information retained by the two linear tests. -/
inductive Coord | identity | two | three | fiveMean
deriving DecidableEq

/-- The possibilities for the subgroup and its linear character, up to indistinguishable
order-class sums. The notation `d10` denotes the dihedral group of order ten. -/
inductive Kind
  | one | c2 | c2twist | c3 | c3twist | c5 | c5twist
  | klein | kleinTwist | s3 | s3sign | d10 | d10sign | a4 | a4twist
deriving DecidableEq

/-- Subgroup order and sums of the linear character on elements of orders 2, 3, 5.
The identity always contributes one. -/
structure Data where
  card : ℕ
  sumTwo : ℤ
  sumThree : ℤ
  sumFive : ℤ

def data : Kind → Data
  | .one       => ⟨1,  0,  0,  0⟩
  | .c2        => ⟨2,  1,  0,  0⟩
  | .c2twist   => ⟨2, -1,  0,  0⟩
  | .c3        => ⟨3,  0,  2,  0⟩
  | .c3twist   => ⟨3,  0, -1,  0⟩
  | .c5        => ⟨5,  0,  0,  4⟩
  | .c5twist   => ⟨5,  0,  0, -1⟩
  | .klein     => ⟨4,  3,  0,  0⟩
  | .kleinTwist=> ⟨4, -1,  0,  0⟩
  | .s3        => ⟨6,  3,  2,  0⟩
  | .s3sign    => ⟨6, -3,  2,  0⟩
  | .d10       => ⟨10, 5,  0,  4⟩
  | .d10sign   => ⟨10,-5,  0,  4⟩
  | .a4        => ⟨12, 3,  8,  0⟩
  | .a4twist   => ⟨12, 3, -4,  0⟩

def index (k : Kind) : ℕ := 60 / (data k).card

abbrev Row := Coord → ℚ

def row (k : Kind) : Row
  | .identity => 60 / ((data k).card : ℚ)
  | .two      => 4 * ((data k).sumTwo : ℚ) / ((data k).card : ℚ)
  | .three    => 3 * ((data k).sumThree : ℚ) / ((data k).card : ℚ)
  | .fiveMean => 5 * ((data k).sumFive : ℚ) / (2 * ((data k).card : ℚ))

def trivial : Row := fun _ => 1

/-- Exact attainment of numerator index six and denominator index five. -/
theorem twoTermIdentity :
    row .d10 - row .a4twist = trivial ∧ index .d10 = 6 ∧ index .a4twist = 5 := by
  refine ⟨?_, rfl, rfl⟩
  funext c
  cases c <;> norm_num [row, trivial, data, Pi.sub_apply]

/-- Pair against the virtual character Ψ with class values (3,−1,0,3,3). -/
def witness : Row →ₗ[ℚ] ℚ where
  toFun f := (3 * f .identity - 15 * f .two + 72 * f .fiveMean) / 60
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' x y := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Dimension minus the multiplicity of the trivial character. -/
def excess : Row →ₗ[ℚ] ℚ where
  toFun f := f .identity -
    (f .identity + 15 * f .two + 20 * f .three + 24 * f .fiveMean) / 60
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' x y := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem witness_trivial : witness trivial = 1 := by norm_num [trivial, witness]
theorem excess_trivial : excess trivial = 0 := by norm_num [trivial, excess]

theorem row_checks (k : Kind) :
    5 ≤ index k ∧ 0 ≤ witness (row k) ∧
    (index k < 6 → witness (row k) = 0) ∧ 0 < excess (row k) := by
  cases k <;> norm_num [witness, excess, row, index, data]

/-- Every rational expression for the trivial row needs a positive term of index
at least six and a negative term of index at least five. Coefficients may be
negative and arbitrarily small, and different characters with the same row may
be combined. -/
theorem optimalSupports (s : Finset Kind) (a : Kind → ℚ) (h : ∑ k ∈ s, a k • row k = trivial) :
    (∃ k ∈ s, 0 < a k ∧ 6 ≤ index k) ∧ (∃ k ∈ s, a k < 0 ∧ 5 ≤ index k) := by
  have hw : ∑ k ∈ s, a k * witness (row k) = 1 := by
    simpa only [map_sum, map_smul, smul_eq_mul, witness_trivial] using congrArg witness h
  have hx : ∑ k ∈ s, a k * excess (row k) = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul, excess_trivial] using congrArg excess h
  exact BrauerSupport.forceSupport s a (fun k => witness (row k)) (fun k => excess (row k))
    index 6 5 hw hx (fun k _ => row_checks k)

#print axioms twoTermIdentity
#print axioms row_checks
#print axioms optimalSupports
end A5BrauerCertificate

namespace PSL27BrauerCertificate

/-- Conjugacy-class information retained by the two linear tests. -/
inductive Coord | identity | two | three | four | sevenMean
deriving DecidableEq

/-- The possibilities for the subgroup and its linear character, up to indistinguishable
order-class sums. Here `borel` denotes the Frobenius subgroup of order 21. -/
inductive Kind
  | one | c2 | c2twist | c3 | c3twist | c4 | c4odd | c4even | c7 | c7twist
  | klein | kleinTwist | s3 | s3sign | d8 | d8reflection | d8rotation
  | a4 | a4twist | borel | borelTwist | s4 | s4sign
deriving DecidableEq

/-- Subgroup order and sums of the linear character on elements of orders 2, 3, 4, 7.
The identity always contributes one. -/
structure Data where
  card : ℕ
  sumTwo : ℤ
  sumThree : ℤ
  sumFour : ℤ
  sumSeven : ℤ

def data : Kind → Data
  | .one          => ⟨1,  0,  0,  0,  0⟩
  | .c2           => ⟨2,  1,  0,  0,  0⟩
  | .c2twist      => ⟨2, -1,  0,  0,  0⟩
  | .c3           => ⟨3,  0,  2,  0,  0⟩
  | .c3twist      => ⟨3,  0, -1,  0,  0⟩
  | .c4           => ⟨4,  1,  0,  2,  0⟩
  | .c4odd        => ⟨4, -1,  0,  0,  0⟩
  | .c4even       => ⟨4,  1,  0, -2,  0⟩
  | .c7           => ⟨7,  0,  0,  0,  6⟩
  | .c7twist      => ⟨7,  0,  0,  0, -1⟩
  | .klein        => ⟨4,  3,  0,  0,  0⟩
  | .kleinTwist   => ⟨4, -1,  0,  0,  0⟩
  | .s3           => ⟨6,  3,  2,  0,  0⟩
  | .s3sign       => ⟨6, -3,  2,  0,  0⟩
  | .d8           => ⟨8,  5,  0,  2,  0⟩
  | .d8reflection => ⟨8, -3,  0,  2,  0⟩
  | .d8rotation   => ⟨8,  1,  0, -2,  0⟩
  | .a4           => ⟨12, 3,  8,  0,  0⟩
  | .a4twist      => ⟨12, 3, -4,  0,  0⟩
  | .borel        => ⟨21, 0, 14,  0,  6⟩
  | .borelTwist   => ⟨21, 0, -7,  0,  6⟩
  | .s4           => ⟨24, 9,  8,  6,  0⟩
  | .s4sign       => ⟨24,-3,  8, -6,  0⟩

def index (k : Kind) : ℕ := 168 / (data k).card

abbrev Row := Coord → ℚ

def row (k : Kind) : Row
  | .identity => 168 / ((data k).card : ℚ)
  | .two      => 8 * ((data k).sumTwo : ℚ) / ((data k).card : ℚ)
  | .three    => 3 * ((data k).sumThree : ℚ) / ((data k).card : ℚ)
  | .four     => 4 * ((data k).sumFour : ℚ) / ((data k).card : ℚ)
  | .sevenMean => 7 * ((data k).sumSeven : ℚ) / (2 * ((data k).card : ℚ))

def trivial : Row := fun _ => 1

/-- Exact attainment of numerator index eight and denominator index seven. -/
theorem twoTermIdentity :
    row .borel - row .s4sign = trivial ∧ index .borel = 8 ∧ index .s4sign = 7 := by
  refine ⟨?_, rfl, rfl⟩
  funext c
  cases c <;> norm_num [row, trivial, data, Pi.sub_apply]

/-- Pair against the virtual character Ψ with class values (9,−3,0,3,2,2). -/
def witness : Row →ₗ[ℚ] ℚ where
  toFun f := (9 * f .identity - 63 * f .two + 126 * f .four + 96 * f .sevenMean) / 168
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' x y := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Dimension minus the multiplicity of the trivial character. -/
def excess : Row →ₗ[ℚ] ℚ where
  toFun f := f .identity -
    (f .identity + 21*f .two + 56*f .three + 42*f .four + 48*f .sevenMean) / 168
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' x y := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem witness_trivial : witness trivial = 1 := by norm_num [trivial, witness]
theorem excess_trivial : excess trivial = 0 := by norm_num [trivial, excess]

theorem row_checks (k : Kind) :
    7 ≤ index k ∧ 0 ≤ witness (row k) ∧
    (index k < 8 → witness (row k) = 0) ∧ 0 < excess (row k) := by
  cases k <;> norm_num [witness, excess, row, index, data]

/-- Every rational expression for the trivial row needs a positive term of index
at least eight and a negative term of index at least seven. Coefficients may be
negative and arbitrarily small, and different characters with the same row may
be combined. -/
theorem optimalSupports (s : Finset Kind) (a : Kind → ℚ) (h : ∑ k ∈ s, a k • row k = trivial) :
    (∃ k ∈ s, 0 < a k ∧ 8 ≤ index k) ∧ (∃ k ∈ s, a k < 0 ∧ 7 ≤ index k) := by
  have hw : ∑ k ∈ s, a k * witness (row k) = 1 := by
    simpa only [map_sum, map_smul, smul_eq_mul, witness_trivial] using congrArg witness h
  have hx : ∑ k ∈ s, a k * excess (row k) = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul, excess_trivial] using congrArg excess h
  exact BrauerSupport.forceSupport s a (fun k => witness (row k)) (fun k => excess (row k))
    index 8 7 hw hx (fun k _ => row_checks k)

#print axioms twoTermIdentity
#print axioms row_checks
#print axioms optimalSupports
end PSL27BrauerCertificate
