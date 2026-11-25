import Research.HadamardBudget
import Research.EdgeDisks

noncomputable section
namespace ERH.WidthTransfer
open ERH.MultiShift ERH.HadamardBudget Filter

/-- A finite-margin exclusion with the exact limiting half multiplier. The predicate
`Z L β` describes a zero at logarithmic absolute height L. An analytic comparison
with o(1) error at every fixed number of shifts is the only analytic hypothesis here. -/
theorem half_cost_width (Z : ℝ → ℝ → Prop) {p G a : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hG : 0 < G) (ha : 0 ≤ a)
    (ha' : a < (1-p)^2/(G/2))
    (strip : ∀ L β, Z L β → β ≤ 1)
    (budget : ∀ m : ℕ, ∀ v : ℝ, 0 < v → ∀ e : ℝ, 0 < e →
      ∃ H : ℝ, ∀ L ≥ H, ∀ β, Z L β →
      1/(v+L*(1-β)) ≤ p^2/v+(1-weight m)*G+e) :
    ∃ H : ℝ, ∀ L ≥ H, ∀ β, Z L β → a < L*(1-β) := by
  let C := G/2
  let v := p*(1-p)/C
  have hC : 0 < C := by dsimp [C]; positivity
  have hv : 0 < v := div_pos (mul_pos hp (sub_pos.mpr hp1)) hC
  have hpc : 0 < p^2/v+C := by positivity
  have hasmall : a < (1-p)^2/C := ha'
  have hprod : (v+a)*(p^2/v+C)<1 := by
    calc
      _ < (v+(1-p)^2/C)*(p^2/v+C) := mul_lt_mul_of_pos_right (by linarith) hpc
      _ = 1 := by simpa [v] using (EdgeDisks.general_barrier hp hp1 hC)
  have hs : p^2/v+C < 1/(v+a) :=
    (lt_div_iff₀ (show 0 < v+a by linarith)).2 (by linarith [mul_comm (v+a) (p^2/v+C)])
  have hlim : Tendsto (fun m => p^2/v+(1-weight m)*G) atTop
      (nhds (p^2/v+(1-(1/2:ℝ))*G)) :=
    tendsto_const_nhds.add ((tendsto_const_nhds.sub weight_tendsto).mul_const G)
  have hstrict : p^2/v+(1-(1/2:ℝ))*G < 1/(v+a) := by
    rw [show (1-(1/2:ℝ))*G = C by dsimp [C]; ring]
    exact hs
  obtain ⟨m,hm⟩ := (hlim.eventually_lt_const hstrict).exists
  let eps := (1/(v+a) - (p^2/v+(1-weight m)*G))/2
  have he : 0 < eps := by dsimp [eps]; linarith
  obtain ⟨H,hH⟩ := budget m v hv eps he
  refine ⟨max 0 H, ?_⟩
  intro L hL β hz
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have hLe : H ≤ L := (le_max_right _ _).trans hL
  have hslope := hH L hLe β hz
  have hden : 0 < v+L*(1-β) := by
    have hpos := mul_nonneg hL0 (sub_nonneg.mpr (strip L β hz))
    linarith
  by_contra! hn
  have hi := one_div_le_one_div_of_le hden (show v+L*(1-β) ≤ v+a by linarith)
  dsimp [eps] at hslope
  linarith

/-- Convert the finite-Hadamard estimate to the scaled hypothesis of the
preceding theorem. The finite target loss is absorbed once the height is large. -/
theorem normalize_finite_bound {B β L v e : ℝ} {m : ℕ}
    (hL : 0 < L) (hv : 0 < v) (hβ : β ≤ 1)
    (hbig : 2*(m:ℝ)+1 ≤ e*L)
    (h : 1/(1+v/L-β) ≤ B*L+(2*(m:ℝ)+1)) :
    1/(v+L*(1-β)) ≤ B+e := by
  have hden : 0 < v+L*(1-β) := by
    have := mul_nonneg hL.le (sub_nonneg.mpr hβ)
    linarith
  have hden' : 0 < 1+v/L-β := by linarith [div_pos hv hL]
  have aux : 1/(1+v/L-β) = L*(1/(v+L*(1-β))) := by
    have rewriteDen : 1+v/L-β = (v+L*(1-β))/L := by field_simp; ring
    rw [rewriteDen, one_div_div, one_div, div_eq_mul_inv]
  rw [aux] at h
  exact (mul_le_mul_iff_right₀ hL).mp (by nlinarith)

/-- A generic exact rounding lemma for a quoted pole P and moving cost G.
The decimal cutoffs subsequently used in the paper are proved by rational inequalities. -/
theorem sqrt_rounding {P G s C : ℝ} (hP : 0 ≤ P) (hs : 0 ≤ s) (hs1 : s < 1)
    (hroot : P ≤ s^2) (hG : 0 < G) (hcost : G < C*(1-s)^2) :
    G/(1-Real.sqrt P)^2 < C := by
  have hle : Real.sqrt P ≤ s := (Real.sqrt_le_iff).2 ⟨hs,hroot⟩
  have hpos : 0 < (1-Real.sqrt P)^2 := by
    have h' : 0 < 1-Real.sqrt P := by linarith
    positivity
  have hC : 0 < C := by by_contra! hh; nlinarith [mul_nonpos_of_nonpos_of_nonneg hh (sq_nonneg (1-s))]
  apply (div_lt_iff₀ hpos).2
  apply hcost.trans_le
  apply mul_le_mul_of_nonneg_left _ hC.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ 2-s-Real.sqrt P by linarith)]

#print axioms half_cost_width
end ERH.WidthTransfer
