import Research.SmoothedWidth
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The concrete zero-strip inference for a complex function. F stands for the
continued unitary L-function, not the sum of its Dirichlet series to the left of
absolute convergence. The analytic estimate and the zero reflection are parameters. -/
noncomputable section
namespace ERH.EllipticWidth
open ERH.Bump ERH.SmoothedWidth

def pole : ℝ := 473580/1000000
def cost : ℝ := 219852918901/246450000000
def width : ℝ := 1/(616918/100000)

/-- A uniform averaged disk inequality only at candidate zeros within the proposed
edge. L is log absolute height; e may be arbitrarily small after v is fixed. -/
def AveragedEstimate (F : ℂ → ℂ) : Prop :=
  ∀ v : ℝ, 0 < v → ∀ e : ℝ, 0 < e → ∃ H : ℝ, ∀ β t : ℝ,
    Real.log |t| ≥ H → 0 < β → β < 1 → F ⟨β,t⟩ = 0 →
    Real.log |t| *(1-β) ≤ width →
    response B pole v (Real.log |t| *(1-β)/width) ≤ width*cost+e

theorem gain_margin : width*cost < B*(momentPolynomial B-(315/796)*pole) := by
  norm_num [width,cost,B,pole,momentPolynomial]

theorem eventual_strip (F : ℂ → ℂ) (estimate : AveragedEstimate F)
    (reflect : ∀ β t : ℝ, 0 < β → β < 1 → F ⟨β,t⟩ = 0 → F ⟨1-β,t⟩ = 0) :
    ∃ H : ℝ, ∀ β t : ℝ, H ≤ Real.log |t| → 0 < β → β < 1 → F ⟨β,t⟩ = 0 →
      width < Real.log |t| * min β (1-β) := by
  let Z (L β : ℝ) := ∃ t : ℝ, L = Real.log |t| ∧ 0 < β ∧ β < 1 ∧ F ⟨β,t⟩ = 0
  have budget : ∀ v : ℝ, 0 < v → ∀ e : ℝ, 0 < e →
      ∃ H : ℝ, ∀ L ≥ H, ∀ β, Z L β → L*(1-β) ≤ width →
       response B pole v (L*(1-β)/width) ≤ width*cost+e := by
    intro v hv e he
    obtain ⟨H,hH⟩ := estimate v hv e he
    refine ⟨H,?_⟩
    rintro L hL β ⟨t,rfl,h0,h1,hz⟩ hnear
    exact hH β t hL h0 h1 hz hnear
  obtain ⟨H,hH⟩ := rational_exclusion Z (by norm_num [B] : 0 ≤ B)
    (by norm_num [width] : 0 < width) gain_margin budget
  refine ⟨max 0 H,?_⟩
  intro β t ht h0 h1 hz
  have hL := (le_max_right 0 H).trans ht
  have hh := hH _ hL β ⟨t,rfl,h0,h1,hz⟩
  have hr := hH _ hL (1-β) ⟨t,rfl,by linarith,by linarith,reflect β t h0 h1 hz⟩
  rw [show 1-(1-β) = β by ring] at hr
  exact (le_total β (1-β)).elim (fun h => by rwa [min_eq_left h]) (fun h => by rwa [min_eq_right h])

#print axioms eventual_strip
end ERH.EllipticWidth
