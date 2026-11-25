import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Alternating finite abscissa shifts for the real paired Poisson kernels.
Here σ=1+u and β is the unitary real part of the zero. -/
noncomputable section
namespace ERH.MultiShift

open Filter
open scoped BigOperators Topology

def atom (b y : ℝ) : ℝ := b / (b ^ 2 + y ^ 2)

def pair (u β y : ℝ) : ℝ := atom (1 + u - β) y + atom (u + β) y

def endpoint (m : ℕ) : ℝ := 2 * (m : ℝ) + 1

def weight (m : ℕ) : ℝ := endpoint m / (2 * endpoint m + 1)

def linear (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, (f (2 * k + 1) - f (2 * k + 2)) +
    weight m * f (2 * m + 1)

def corrected (m : ℕ) (u β y : ℝ) : ℝ :=
  pair u β y - linear m (fun j => pair (u + j) β y)

theorem endpoint_pos (m : ℕ) : 0 < endpoint m := by unfold endpoint; positivity

theorem weight_pos (m : ℕ) : 0 < weight m := by
  unfold weight; have := endpoint_pos m; positivity

theorem weight_lt_half (m : ℕ) : weight m < 1/2 := by
  have hp := endpoint_pos m
  unfold weight
  apply (div_lt_iff₀ (by positivity : 0 < 2 * endpoint m + 1)).2
  linarith

theorem linear_const (m : ℕ) (c : ℝ) : linear m (fun _ => c) = weight m * c := by
  simp [linear]

theorem pair_left (u y : ℝ) : pair u 0 y = atom u y + atom (u + 1) y := by
  simp only [pair, sub_zero, add_zero]; rw [add_comm 1 u, add_comm]

theorem pair_right (u y : ℝ) : pair u 1 y = pair u 0 y := by
  rw [pair_left]; unfold pair; rw [show 1 + u - 1 = u by ring]

private theorem telescope (m : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range m, ((f (2*k+1) + f (2*k+2)) -
      (f (2*k+2) + f (2*k+3))) = f 1 - f (2*m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show 2*(m+1)+1 = 2*m+3 by omega]
    ring

theorem boundary_identity (m : ℕ) (u y : ℝ) :
    corrected m u 0 y = atom u y + (1 - weight m) * atom (u + endpoint m) y -
      weight m * atom (u + endpoint m + 1) y := by
  let f (j : ℕ) : ℝ := atom (u + j) y
  have shift (j : ℕ) : pair (u + j) 0 y = f j + f (j+1) := by
    rw [pair_left]; simp [f, add_assoc]
  have H : ∑ k ∈ Finset.range m,
      (pair (u + ↑(2*k+1)) 0 y - pair (u + ↑(2*k+2)) 0 y) =
      f 1 - f (2*m+1) := by
    simpa only [shift, Nat.add_assoc, Nat.reduceAdd] using telescope m f
  unfold corrected linear
  rw [H]
  dsimp only
  rw [shift, pair_left]
  simp only [f, endpoint, Nat.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring_nf

theorem boundary_identity_right (m : ℕ) (u y : ℝ) :
    corrected m u 1 y = corrected m u 0 y := by
  simp only [corrected, pair_right]

private theorem consecutive (m : ℕ) {u : ℝ} (hu : 0 ≤ u) (y : ℝ) :
    weight m * atom (u + endpoint m + 1) y ≤
      (1 - weight m) * atom (u + endpoint m) y := by
  let a := endpoint m
  let b := u + a
  have ha : 0 < a := endpoint_pos m
  have hb : 0 < b := by dsimp [b]; linarith
  have hab : a ≤ b := by dsimp [b]; linarith
  have ha1 : 0 < 2*a+1 := by positivity
  have d1 : 0 < b^2+y^2 := by positivity
  have d2 : 0 < (b+1)^2+y^2 := by positivity
  change a/(2*a+1) * ((b+1)/((b+1)^2+y^2)) ≤
      (1-a/(2*a+1)) * (b/(b^2+y^2))
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg y),
    mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg b),
    mul_nonneg ha.le (sq_nonneg b), mul_nonneg hb.le (sq_nonneg b),
    mul_nonneg ha.le hb.le]

theorem corrected_left_nonneg (m : ℕ) {u : ℝ} (hu : 0 ≤ u) (y : ℝ) :
    0 ≤ corrected m u 0 y := by
  rw [boundary_identity]
  have ha : 0 ≤ atom u y := by unfold atom; positivity
  linarith [consecutive m hu y]

theorem corrected_right_nonneg (m : ℕ) {u : ℝ} (hu : 0 ≤ u) (y : ℝ) :
    0 ≤ corrected m u 1 y := by
  rw [boundary_identity_right]; exact corrected_left_nonneg m hu y


theorem half_gap (m : ℕ) : 1 / 2 - weight m = 1 / (8 * (m : ℝ) + 6) := by
  have hd : 0 < 8 * (m : ℝ) + 6 := by positivity
  unfold weight endpoint
  field_simp
  ring

theorem weight_tendsto : Tendsto weight atTop (𝓝 (1/2 : ℝ)) := by
  have hz : Tendsto (fun m : ℕ => 1 / (8 * (m : ℝ) + 6)) atTop (𝓝 (0 : ℝ)) := by
    have hmono : ∀ m : ℕ, (m : ℝ) ≤ 8 * (m : ℝ) + 6 := by
      intro m
      have hm : 0 ≤ (m : ℝ) := by positivity
      linarith
    have hi : Tendsto (fun m : ℕ => 8 * (m : ℝ) + 6) atTop atTop :=
      tendsto_atTop_mono hmono tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop hi
  convert (tendsto_const_nhds (x := (1/2 : ℝ))).sub hz using 1
  · funext m; linarith [half_gap m]
  · norm_num

private theorem euler_telescope (m : ℕ) (x : ℝ) :
    (1+x) * ∑ k ∈ Finset.range m, (x^(2*k+1) - x^(2*k+2)) =
      x-x^(2*m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    rw [show 2*(m+1)+1 = (2*m+1)+2 by omega,
      show 2*m+2 = (2*m+1)+1 by omega, pow_add, pow_succ]
    ring

theorem euler_identity (m : ℕ) (x : ℝ) :
    (1+x) * (1 - linear m (fun j => x^j)) =
      1 + (1-(1+x)*weight m)*x^(2*m+1) := by
  unfold linear
  dsimp only
  rw [mul_sub, mul_add, euler_telescope]
  ring

theorem euler_weight_pos (m : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    0 < 1 - linear m (fun j => x^j) := by
  have h : (1+x)*weight m ≤ 1 := by
    calc (1+x)*weight m ≤ 2*weight m := mul_le_mul_of_nonneg_right (by linarith) (weight_pos m).le
         _ ≤ 1 := by linarith [weight_lt_half m]
  have hnon : 0 ≤ (1-(1+x)*weight m)*x^(2*m+1) := by positivity
  by_contra! hbad
  have hbad' := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1+x by linarith) hbad
  linarith [euler_identity m x]


private theorem atom_at_zero {b : ℝ} (hb : 0 < b) : atom b 0 = 1/b := by
  unfold atom
  simp only [zero_pow (by decide : 2 ≠ 0), add_zero]
  field_simp

private theorem shifted_pair_bounds {u β : ℝ} (hu : 0 ≤ u) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    {j : ℕ} (hj : 1 ≤ j) : 0 ≤ pair (u+j) β 0 ∧ pair (u+j) β 0 ≤ 2 := by
  have hj' : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have h1 : 1 ≤ 1 + (u+j) - β := by linarith
  have h2 : 1 ≤ (u+j) + β := by linarith
  have h1p : 0 < 1 + (u+j) - β := by linarith
  have h2p : 0 < (u+j) + β := by linarith
  rw [pair, atom_at_zero h1p, atom_at_zero h2p]
  constructor
  · positivity
  · have e1 : 1 / (1 + (u+↑j) - β) ≤ 1 := (div_le_iff₀ h1p).2 (by linarith)
    have e2 : 1 / (u+↑j+β) ≤ 1 := (div_le_iff₀ h2p).2 (by linarith)
    linarith

/-- The single target pole is retained at its own ordinate, with a fixed additive loss.
The bound is uniform up to either edge and suffices after division by the height logarithm. -/
theorem target (m : ℕ) {u β : ℝ} (hu : 0 < u) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    1/(1+u-β) - (2*(m : ℝ)+1) ≤ corrected m u β 0 := by
  let F (j : ℕ) : ℝ := pair (u+j) β 0
  have bounds {j : ℕ} (h : 1 ≤ j) : 0 ≤ F j ∧ F j ≤ 2 :=
    shifted_pair_bounds hu.le hβ hβ' h
  have hs : ∑ k ∈ Finset.range m, (F (2*k+1) - F (2*k+2)) ≤
      ∑ _k ∈ Finset.range m, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    linarith [(bounds (j := 2*k+1) (by omega)).2, (bounds (j := 2*k+2) (by omega)).1]
  have hsum : ∑ k ∈ Finset.range m, (F (2*k+1) - F (2*k+2)) ≤ 2*(m : ℝ) := by
    simpa [mul_comm] using hs
  have hfinal : weight m * F (2*m+1) ≤ 1 := by
    calc weight m * F (2*m+1) ≤ weight m * 2 :=
           mul_le_mul_of_nonneg_left (bounds (j := 2*m+1) (by omega)).2 (weight_pos m).le
         _ ≤ 1 := by linarith [weight_lt_half m]
  have hlin : linear m F ≤ 2*(m : ℝ)+1 := by unfold linear; linarith
  have h1 : 0 < 1+u-β := by linarith
  have h2 : 0 ≤ atom (u+β) 0 := by unfold atom; positivity
  change _ ≤ pair u β 0 - linear m F
  rw [pair, atom_at_zero h1]
  linarith

end ERH.MultiShift
