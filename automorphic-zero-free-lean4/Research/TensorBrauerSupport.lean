import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

/-! Numerical part of the tensorized signed-Brauer optimality theorem.
The representation-theoretic input is isolated below as a bound on the
dimension of an induced linear character containing a tensor constituent. -/

open scoped BigOperators

namespace TensorBrauerSupport

variable {ι κ : Type*}

/-- A positive total pairing against a nonnegative witness forces an active
positive coefficient. Applying the lemma to `-coeff` yields the negative case. -/
theorem positiveTerm (s : Finset κ) (coeff w : κ → ℚ)
    (hpos : 0 < ∑ t ∈ s, coeff t * w t) (hn : ∀ t ∈ s, 0 ≤ w t) :
    ∃ t ∈ s, 0 < coeff t ∧ 0 < w t := by
  by_contra no
  apply (not_le_of_gt hpos)
  apply Finset.sum_nonpos
  intro t ht
  by_cases hc : 0 < coeff t
  · have hw : w t ≤ 0 := le_of_not_gt (fun h => no ⟨t, ht, hc, h⟩)
    exact mul_nonpos_of_nonneg_of_nonpos hc.le hw
  · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hc) (hn t ht)

/-- If `dᵢ=[Gᵢ:Hᵢ]`, `vᵢ=dim Vᵢ`, and `h=[∏ Hᵢ:H]`, then
the index of a detected monomial term is at least the product of the single-factor costs. -/
theorem tensorIndex (I : Finset ι) (a d v : ι → ℕ) (h : ℕ)
    (localCost : ∀ i ∈ I, a i ≤ d i * v i) (constituentDimension : (∏ i ∈ I, v i) ≤ h) :
    (∏ i ∈ I, a i) ≤ (∏ i ∈ I, d i) * h := by
  calc
    ∏ i ∈ I, a i ≤ ∏ i ∈ I, (d i * v i) := Finset.prod_le_prod localCost
    _ = (∏ i ∈ I, d i) * (∏ i ∈ I, v i) := Finset.prod_mul_distrib
    _ ≤ (∏ i ∈ I, d i) * h := Nat.mul_le_mul_left _ constituentDimension

/-- The lower bound from a tensor witness whose total pairing has either sign.
A negative test uses `-coeff`, preserving the same positive constituent dimensions. -/
theorem forceTensorIndex (s : Finset κ) (I : Finset ι) (a : ι → ℕ)
    (coeff w : κ → ℚ) (d v : κ → ι → ℕ) (h : κ → ℕ)
    (hpos : 0 < ∑ t ∈ s, coeff t * w t) (hn : ∀ t ∈ s, 0 ≤ w t)
    (restriction : ∀ t ∈ s, 0 < w t →
       (∀ i ∈ I, a i ≤ d t i * v t i) ∧ (∏ i ∈ I, v t i) ≤ h t) :
    ∃ t ∈ s, 0 < coeff t ∧ (∏ i ∈ I, a i) ≤ (∏ i ∈ I, d t i) * h t := by
  obtain ⟨t, ht, hc, hw⟩ := positiveTerm s coeff w hpos hn
  obtain ⟨hl, hd⟩ := restriction t ht hw
  exact ⟨t, ht, hc, tensorIndex I a (d t) (v t) (h t) hl hd⟩

/-- The index of a term with negative coordinates in `J`. -/
def cost [DecidableEq ι] (I J : Finset ι) (a b : ι → ℕ) : ℕ :=
  ∏ i ∈ I, if i ∈ J then b i else a i

theorem numeratorCost [DecidableEq ι] (I J : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ I, b i ≤ a i) : cost I J a b ≤ ∏ i ∈ I, a i := by
  apply Finset.prod_le_prod
  intro i hi
  by_cases hJ : i ∈ J <;> simp [hJ, h i hi]

/-- With at least one negative coordinate, the index is no larger than the
maximum attained by one negative coordinate. -/
theorem denominatorCost [DecidableEq ι] (I J : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ I, b i ≤ a i) (hsub : J ⊆ I) (hne : J.Nonempty) :
    cost I J a b ≤ I.sup (fun j => cost I {j} a b) := by
  obtain ⟨j,hj⟩ := hne
  refine le_trans ?_ (Finset.le_sup (f := fun i => cost I {i} a b) (hsub hj))
  apply Finset.prod_le_prod
  intro i hi
  by_cases hij : i = j
  · subst i
    simp [hj]
  · by_cases hb : i ∈ J <;> simp [hb, hij, h i hi]

#print axioms positiveTerm
#print axioms tensorIndex
#print axioms forceTensorIndex
#print axioms numeratorCost
#print axioms denominatorCost

end TensorBrauerSupport
