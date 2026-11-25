import Research.Resonance
import Research.MultiShift

/-! Retaining targets off ordinate in the actual finite multi-shift kernel. -/
namespace MirrorResonance
open ERH.MultiShift EdgeDisks

private theorem atom_bounds {b : ℝ} (hb : 1 ≤ b) (y : ℝ) :
    0 ≤ atom b y ∧ atom b y ≤ 1 := by
  have hp : 0 < b := by linarith
  unfold atom
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity)).2
    nlinarith only [sq_nonneg y, mul_nonneg hp.le (sub_nonneg.mpr hb)]

private theorem shifted_pair_bounds {u β : ℝ} (hu : 0 ≤ u)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) (y : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ pair (u+j) β y ∧ pair (u+j) β y ≤ 2 := by
  have h1 : (1:ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨x,hx⟩ := atom_bounds (b:=1+(u+j)-β) (by linarith) y
  obtain ⟨z,hz⟩ := atom_bounds (b:=u+j+β) (by linarith) y
  unfold pair
  constructor <;> linarith

/-- The loss is uniform in the ordinate difference y, including signed ordinates. -/
theorem off_axis_target (m : ℕ) {u β : ℝ} (hu : 0 < u)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) (y : ℝ) :
    atom (1+u-β) y-(2*(m:ℝ)+1) ≤ corrected m u β y := by
  let F (j : ℕ) := pair (u+j) β y
  have bounds {j : ℕ} (h : 1 ≤ j) : 0 ≤ F j ∧ F j ≤ 2 :=
    shifted_pair_bounds hu.le hβ hβ' y h
  have hs : ∑ k ∈ Finset.range m, (F (2*k+1)-F (2*k+2)) ≤
      ∑ _k ∈ Finset.range m, (2:ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    linarith only [(bounds (j:=2*k+1) (by omega)).2,
       (bounds (j:=2*k+2) (by omega)).1]
  have hsum : ∑ k ∈ Finset.range m, (F (2*k+1)-F (2*k+2)) ≤ 2*(m:ℝ) := by
    simpa [mul_comm] using hs
  have hterm : weight m * F (2*m+1) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (bounds (j:=2*m+1) (by omega)).2
      (weight_pos m).le
    linarith only [h,weight_lt_half m]
  have hr : 0 ≤ atom (u+β) y := by
    have ht : 0 < u+β := by linarith
    unfold atom
    positivity
  change atom (1+u-β) y - (2*(m:ℝ)+1) ≤
    (atom (1+u-β) y + atom (u+β) y) -
    (∑ k ∈ Finset.range m, (F (2*k+1)-F (2*k+2)) + weight m * F (2*m+1))
  linarith only [hr,hsum,hterm]

theorem rescaled_target (m : ℕ) {v L x : ℝ} (hv : 0 < v) (hL : 0 < L)
    (hx : 0 ≤ x) (hxL : x ≤ L) (y : ℝ) :
    L*poisson v x y-(2*(m:ℝ)+1) ≤ corrected m (v/L) (1-x/L) (y/L) := by
  have h₁ : 0 ≤ 1-x/L := by
    have := (div_le_iff₀ hL).2 (show x ≤ 1*L by linarith)
    linarith
  have h₂ : 1-x/L ≤ 1 := by have := div_nonneg hx hL.le; linarith
  have h := off_axis_target m (div_pos hv hL) h₁ h₂ (y/L)
  have eq : 1+v/L-(1-x/L) = (v+x)/L := by ring
  rw [eq] at h
  have scale := Resonance.kernel_rescale (v:=v) (x:=x) hL (by linarith) y
  change atom ((v+x)/L) (y/L) = _ at scale
  rwa [scale] at h

/-- The exact multiplier for the formal odd-terminal m=20 construction
is already less than the rational comparator used in the rectangle theorem. -/
theorem twenty_cost : 1-weight 20 ≤ (41:ℝ)/81 := by
  norm_num [weight,endpoint]

/-- A two-component upper bound for the corrected actual kernels is incompatible
with simultaneous nearby original and symmetric-square zeros. -/
theorem raw_forty_step_exclusion {L x₁ x₂ y : ℝ}
    (hL : 8192 ≤ L) (hx₁ : 0 ≤ x₁) (hx₁' : x₁ ≤ 3/16)
    (hx₂ : 0 ≤ x₂) (hx₂' : x₂ ≤ 3/16) (hy : |y| ≤ 1/8)
    (budget : corrected 20 ((9/32)/L) (1-x₁/L) (0/L) +
      Resonance.weight*corrected 20 ((9/32)/L) (1-x₂/L) (y/L) ≤
      L*(Resonance.pole/(9/32)+(1-weight 20)*Resonance.degreeCost+1/128)) : False := by
  have hp : 0 < L := by linarith
  have t₁ := rescaled_target 20 (by norm_num : (0:ℝ)<9/32) hp hx₁ (by linarith) 0
  have t₂ := rescaled_target 20 (by norm_num : (0:ℝ)<9/32) hp hx₂ (by linarith) y
  have h₂ := mul_le_mul_of_nonneg_left t₂ (by norm_num [Resonance.weight] : 0 ≤ Resonance.weight)
  have gap := mul_lt_mul_of_pos_left (Resonance.forty_step_resonance_gap hx₁ hx₁' hx₂ hx₂' hy) hp
  have hcost := mul_le_mul_of_nonneg_right twenty_cost
    (by norm_num [Resonance.degreeCost] : 0 ≤ Resonance.degreeCost)
  have hcostL := mul_le_mul_of_nonneg_left hcost hp.le
  norm_num [Resonance.weight] at t₁ h₂ gap budget
  linarith only [hL,t₁,h₂,gap,budget,hcostL]

#print axioms off_axis_target
#print axioms rescaled_target
#print axioms raw_forty_step_exclusion
end MirrorResonance
