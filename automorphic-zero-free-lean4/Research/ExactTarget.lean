import Research.MultiShift

/-! Exact on-axis target retention for the alternating abscissa comparison.
This removes the additive target loss when calibrating explicit finite heights. -/
namespace ExactTarget
open ERH.MultiShift

noncomputable def deficit (a p : ℝ) :=
  (1/a+1/(a+1)) * (p/(a*(a+1)+p))

private theorem atom_zero {a : ℝ} (ha : 0 < a) : atom a 0 = 1/a := by
  unfold atom
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero]
  field_simp

theorem deficit_formula {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    pair a 1 0-pair a b 0 = deficit a (b*(1-b)) := by
  have hA : 0 < a+1 := by linarith
  have hB : 0 < a+b := by linarith
  have hC : 0 < 1+a-b := by linarith
  have hp : 0 ≤ b*(1-b) := mul_nonneg hb (sub_nonneg.mpr hb')
  have hprod : 0 < a*(a+1)+b*(1-b) := by positivity
  rw [pair_right,pair_left,pair,atom_zero ha,atom_zero hA,atom_zero hB,atom_zero hC]
  unfold deficit
  field_simp
  ring

theorem deficit_antitone {a b p : ℝ} (ha : 0<a) (hab : a≤b) (hp : 0≤p) :
    deficit b p ≤ deficit a p := by
  have hb : 0<b := ha.trans_le hab
  have dA : 0<a*(a+1)+p := by positivity
  have dB : 0<b*(b+1)+p := by positivity
  have q : a*(a+1) ≤ b*(b+1) := mul_le_mul hab (by linarith) (by linarith) hb.le
  have d : p/(b*(b+1)+p) ≤ p/(a*(a+1)+p) := by
    apply (div_le_div_iff₀ dB dA).2
    exact mul_le_mul_of_nonneg_left (by linarith) hp
  unfold deficit
  apply mul_le_mul (add_le_add (one_div_le_one_div_of_le ha hab)
    (one_div_le_one_div_of_le (by linarith) (by linarith))) d (by positivity) (by positivity)

theorem comparison_maximized_at_boundary (m : ℕ) {u b : ℝ} (hu : 0<u)
    (hb : 0≤b) (hb' : b≤1) :
    linear m (fun j => pair (u+j) b 0) ≤ linear m (fun j => pair (u+j) 1 0) := by
  let p := b*(1-b)
  have hp : 0≤p := mul_nonneg hb (sub_nonneg.mpr hb')
  have form (j : ℕ) : pair (u+j) 1 0-pair (u+j) b 0 = deficit (u+j) p :=
    deficit_formula (by positivity) hb hb'
  have step (k : ℕ) : deficit (u+(2*k+2:ℕ)) p ≤ deficit (u+(2*k+1:ℕ)) p := by
    apply deficit_antitone (by positivity) _ hp
    push_cast
    linarith
  have term (k : ℕ) :
      pair (u+(2*k+1:ℕ)) b 0-pair (u+(2*k+2:ℕ)) b 0 ≤
      pair (u+(2*k+1:ℕ)) 1 0-pair (u+(2*k+2:ℕ)) 1 0 := by
    linarith only [form (2*k+1),form (2*k+2),step k]
  have last : pair (u+(2*m+1:ℕ)) b 0 ≤ pair (u+(2*m+1:ℕ)) 1 0 := by
    have hz : 0 ≤ deficit (u+(2*m+1:ℕ)) p := by unfold deficit; positivity
    linarith only [hz,form (2*m+1)]
  unfold linear
  apply add_le_add (Finset.sum_le_sum (fun k _ => term k))
  exact mul_le_mul_of_nonneg_left last (weight_pos m).le

/-- Every right component is fully retained at its own ordinate. -/
theorem corrected_exact (m : ℕ) {u b : ℝ} (hu : 0<u) (hb : 0≤b) (hb' : b≤1) :
    1/(1+u-b) ≤ corrected m u b 0 := by
  have hend := boundary_identity m u 0
  have hE : 0<u+endpoint m := by linarith [endpoint_pos m]
  have hplus : 0<u+endpoint m+1 := by linarith
  rw [corrected,pair_left,atom_zero hu,atom_zero (by linarith : 0<u+1),
    atom_zero hE,atom_zero hplus] at hend
  have hw : weight m ≤ 1-weight m := by linarith [weight_lt_half m]
  have last : weight m * (1/(u+endpoint m+1)) ≤ (1-weight m) * (1/(u+endpoint m)) := by
    apply mul_le_mul hw (one_div_le_one_div_of_le hE (by linarith)) (by positivity) (by linarith [weight_lt_half m])
  have lc : linear m (fun j => pair (u+j) 1 0) = linear m (fun j => pair (u+j) 0 0) := by
    simp only [pair_right]
  have bound := comparison_maximized_at_boundary m hu hb hb'
  rw [lc] at bound
  have hbpos : 0<u+b := by linarith
  have cmp := one_div_le_one_div_of_le hbpos (show u+b ≤ u+1 by linarith)
  rw [corrected,pair,atom_zero (by linarith : 0<1+u-b),atom_zero hbpos]
  linarith only [hend,last,bound,cmp]

#print axioms deficit_formula
#print axioms comparison_maximized_at_boundary
#print axioms corrected_exact
end ExactTarget
