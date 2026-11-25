import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter Complex
open scoped Topology
noncomputable section
namespace ERH.StripMinimum

abbrev closedStrip := Complex.re ⁻¹' Set.Icc (0 : ℝ) 1
abbrev openStrip := Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1

def Good (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f closedStrip ∧ ∃ B : ℝ, ∀ z ∈ closedStrip, ‖f z‖ ≤ B

theorem Good.add {f g : ℂ → ℂ} (hf : Good f) (hg : Good g) :
    Good (fun z => f z+g z) := by
  obtain ⟨df,b,hb⟩ := hf
  obtain ⟨dg,c,hc⟩ := hg
  exact ⟨df.add dg, b+c, fun z hz => le_trans (norm_add_le _ _) (add_le_add (hb z hz) (hc z hz))⟩

theorem Good.neg {f : ℂ → ℂ} (hf : Good f) : Good (fun z => -f z) := by
  obtain ⟨df,b,hb⟩ := hf
  exact ⟨df.neg,b,fun z hz => by simpa using hb z hz⟩

theorem Good.sub {f g : ℂ → ℂ} (hf : Good f) (hg : Good g) :
    Good (fun z => f z-g z) := by simpa [sub_eq_add_neg] using hf.add hg.neg

theorem Good.smulReal {f : ℂ → ℂ} (hf : Good f) (c : ℝ) :
    Good (fun z => (c : ℂ)*f z) := by
  obtain ⟨df,b,hb⟩ := hf
  exact ⟨(differentiableOn_const _).mul df, ‖(c:ℂ)‖*b,fun z hz =>
    (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hb z hz) (norm_nonneg _))⟩

theorem Good.sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (hf : ∀ i ∈ s, Good (f i)) :
    Good (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact ⟨differentiableOn_const _, 0, by simp⟩
  | @insert i s hi ih =>
    simpa [Finset.sum_insert, hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Bounded holomorphic functions with nonnegative real part on both edges
have nonnegative real part throughout. The vertical strip version of the
Phragmén--Lindelöf theorem is invoked at growth exponent zero. -/
theorem nonnegative_of_edges {f : ℂ → ℂ} (hf : Good f)
    (left : ∀ z : ℂ, z.re=0 → 0 ≤ (f z).re)
    (right : ∀ z : ℂ, z.re=1 → 0 ≤ (f z).re)
    {z : ℂ} (hz : z ∈ closedStrip) : 0 ≤ (f z).re := by
  obtain ⟨df,b,hb⟩ := hf
  have subset : openStrip ⊆ closedStrip := fun z h => ⟨h.1.le,h.2.le⟩
  have cl : closure openStrip ⊆ closedStrip :=
    closure_minimal subset (isClosed_Icc.preimage Complex.continuous_re)
  let g := fun z => Complex.exp (-f z)
  have dg : DiffContOnCl ℂ g openStrip :=
    (Complex.differentiable_exp.comp_differentiableOn (df.neg.mono cl)).diffContOnCl
  have bound : ∀ z ∈ openStrip, ‖g z‖ ≤ Real.exp b := by
    intro w hw
    rw [show ‖g w‖ = Real.exp (-(f w).re) by simp [g,Complex.norm_exp]]
    apply Real.exp_le_exp.mpr
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (hb w (subset hw)))
  have hle : ‖g z‖ ≤ (1:ℝ) := by
    apply PhragmenLindelof.vertical_strip dg _ _ _ hz.1 hz.2
    · refine ⟨0, by simpa using Real.pi_pos, 0, ?_⟩
      apply Asymptotics.IsBigO.of_bound (Real.exp b)
      apply Filter.Eventually.filter_mono inf_le_right
      exact Filter.eventually_principal.mpr (fun w hw => by simpa using bound w hw)
    · intro w hw
      simpa [g, Complex.norm_exp] using left w hw
    · intro w hw
      simpa [g, Complex.norm_exp] using right w hw
  simpa [g, Complex.norm_exp] using hle

/-- A complex lift whose real part is the usual reflection-pair Poisson kernel. -/
def pairC (u : ℝ) (z : ℂ) := ((1+u:ℝ)-z)⁻¹ + ((u:ℂ)+z)⁻¹

private theorem good_inv_real {f : ℂ → ℂ} {u : ℝ} (hu : 0 < u)
    (df : DifferentiableOn ℂ f closedStrip) (lb : ∀ z ∈ closedStrip, u ≤ (f z).re) :
    Good (fun z => (f z)⁻¹) := by
  have hnorm (z : ℂ) (hz : z ∈ closedStrip) : u ≤ ‖f z‖ :=
    (lb z hz).trans (Complex.re_le_norm _)
  constructor
  · apply df.inv
    intro z hz he
    simpa [he,not_le.mpr hu] using hnorm z hz
  · refine ⟨1/u,fun z hz => ?_⟩
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hu (hnorm z hz)

theorem good_pairC {u : ℝ} (hu : 0 < u) : Good (pairC u) := by
  unfold pairC
  apply Good.add
  · apply good_inv_real hu ((differentiableOn_const _).sub differentiableOn_id)
    intro z hz
    change u ≤ (((1+u:ℝ):ℂ)-z).re
    simp only [sub_re, ofReal_re]
    linarith [hz.2]
  · apply good_inv_real hu ((differentiableOn_const _).add differentiableOn_id)
    intro z hz
    change u ≤ ((u:ℂ)+z).re
    simp only [add_re, ofReal_re]
    linarith [hz.1]

end ERH.StripMinimum
