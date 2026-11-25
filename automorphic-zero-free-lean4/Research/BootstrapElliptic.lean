import Research.TiltedWidth
import Research.EllipticTilt12
import Research.SquarePriorGain

/-! Endpoint for the slope 5.7693. The last theorem accepts separate centered
bounds for the four moving logarithmic derivatives, the scalar/static terms,
and prime-sum positivity. -/
noncomputable section
open MeasureTheory Set
namespace ERH.BootstrapElliptic
open ERH.Bump ERH.SmoothedWidth ERH.TiltedGain ERH.TiltedWidth

def b : ℝ := 101/100
def d : ℝ := 4239/50000
def W : ℝ := 10000/57693
def p : ℝ := 152703/250000
def G : ℝ := 41475929/93000000

def lap (z : ℝ) := b*(∫ x in (0:ℝ)..1, h x*Real.exp (-(b*x*z)))

theorem response_split (r w : ℝ) :
    response b p (-r) w = lap (w-r)-p*lap (-r) := by
  have A : Continuous (fun x => h x*Real.exp (-(b*x*(w-r)))) := by unfold h; fun_prop
  have C : Continuous (fun x => p*(h x*Real.exp (-(b*x*(-r))))) := by unfold h; fun_prop
  unfold response lap
  rw [show b*(∫ x in (0:ℝ)..1, h x*Real.exp (-(b*x*(w-r)))) -
        p*(b*(∫ x in (0:ℝ)..1, h x*Real.exp (-(b*x*(-r))))) =
        b*((∫ x in (0:ℝ)..1, h x*Real.exp (-(b*x*(w-r)))) -
          p*(∫ x in (0:ℝ)..1, h x*Real.exp (-(b*x*(-r))))) by ring]
  apply congrArg (fun v : ℝ => b*v)
  rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_sub
       (A.intervalIntegrable _ _) (C.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [show -r+w = w-r by ring]
  ring

/-- Each quantity is normalized by W/log |t|. The target's mixed coefficient is
exactly one. Convergence and the analytic estimates on the actual L-functions
enter in these explicit, individually checkable hypotheses. -/
def FactorEstimates (F : ℂ → ℂ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ H : ℝ, ∀ β t : ℝ, H ≤ Real.log |t| →
    0 < β → β < 1 → F ⟨β,t⟩ = 0 → Real.log |t| * (1-β) ≤ W →
    ∃ s a11 a51 a22 a82 : ℝ,
      -η ≤ s+a11+(13978/1000000)*a51+(143554/1000000)*a22+(944/1000000)*a82 ∧
      s ≤ p*lap (-d/W)+η ∧
      a11 ≤ W/3+η-lap (Real.log |t| * (1-β)/W-d/W) ∧
      a51 ≤ W/3+η ∧ a22 ≤ W*(139/186)+η ∧ a82 ≤ W*(139/186)+η

theorem from_factor_estimates {F : ℂ → ℂ} (he : FactorEstimates F) :
    Budget F b p G d W := by
  intro e he'
  obtain ⟨H,hH⟩ := he (e/5) (by linarith)
  refine ⟨H,?_⟩
  intro β t ht h0 h1 hz hnear
  obtain ⟨s,A,B,C,D,hs,hs',hA,hB,hC,hD⟩ := hH β t ht h0 h1 hz hnear
  rw [response_split,neg_div] at *
  dsimp [G] at *
  linarith

theorem rounding :
    W*G + 77/100000000 < b*(momentPolynomial (b*(1-d/W))-p*upperMoment (b*(d/W))) := by
  norm_num [W,G,b,d,p,momentPolynomial,upperMoment]

theorem table_constants :
    (EllipticBernstein.Tilt12.pole:ℝ)=p ∧ (EllipticBernstein.Tilt12.slope:ℝ)=G := by
  constructor
  · rw [EllipticBernstein.Tilt12.target_and_pole.2.2]; norm_num [p]
  · rw [EllipticBernstein.Tilt12.exact_cost]; norm_num [G]

theorem eventual_strip (F : ℂ → ℂ) (he : FactorEstimates F)
    (reflect : ∀ β t : ℝ, 0 < β → β < 1 → F ⟨β,t⟩ = 0 → F ⟨1-β,t⟩ = 0) :
    ∃ H : ℝ, ∀ β t : ℝ, H ≤ Real.log |t| → 0 < β → β < 1 → F ⟨β,t⟩ = 0 →
      10000/57693 < Real.log |t| * min β (1-β) := by
  have m : W*G < b*(momentPolynomial (b*(1-d/W))-p*upperMoment (b*(d/W))) :=
    (show W*G < W*G+77/100000000 by linarith).trans rounding
  exact rational_transfer (b:=b) (p:=p) (d:=d) (G:=G) (W:=W) F (by norm_num [b]) (by norm_num [p]) (by norm_num [W])
   (by norm_num [d,W]) (by norm_num [d,W]) (by norm_num [b,d,W])
   m (from_factor_estimates he) reflect

#print axioms eventual_strip
#print axioms table_constants
end ERH.BootstrapElliptic
