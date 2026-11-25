import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! The horizontal derivative of the Poisson extension at the center, the
nonnegative projected kernels of the zeros, and the exact half-circle weight
in the subconvex logarithmic-derivative inequality. -/

noncomputable section
namespace ERH.PoissonJensenCore
open Complex Filter InnerProductSpace MeasureTheory Metric Set
open scoped Topology Interval

/-- The Fourier coefficient corresponding to the horizontal derivative.
The expression uses complex-valued integration before its real part is taken. -/
def firstCoefficient (R : ℝ) (H : ℂ → ℝ) : ℝ :=
   (Real.circleAverage (fun ζ : ℂ => (2 * ζ / (ζ - 0)^2) • (H ζ : ℂ)) 0 R).re

/-- Differentiate the actual Poisson formula, without assuming a boundary derivative formula. -/
theorem harmonic_horizontal {H : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hH : HarmonicOnNhd H (closedBall 0 R)) (hI : CircleIntegrable H 0 R) :
    HasDerivAt (fun x : ℝ => H x) (firstCoefficient R H) 0 := by
  have hIC : CircleIntegrable (fun z : ℂ => (H z : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hI ⊢
    exact Complex.ofRealCLM.integrable_comp hI
  have h0 : (0 : ℂ) ∉ sphere (0 : ℂ) |R| := by
    simp [abs_of_pos hR, ne_of_lt hR]
  have h := hasDerivAt_circleAverage_herglotzRieszKernel_smul hIC h0
  have h' := h.real_of_complex
  apply h'.congr_of_eventuallyEq
  have hh : ∀ᶠ x : ℝ in 𝓝 0, (x : ℂ) ∈ ball (0 : ℂ) R :=
    Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (ball_mem_nhds (0 : ℂ) hR)
  filter_upwards [hh] with x hx
  have hn : (x : ℂ) ∉ sphere (0 : ℂ) |R| := by
    rw [abs_of_pos hR]
    intro hs
    exact (ne_of_lt (mem_ball.mp hx)) (mem_sphere.mp hs)
  exact (re_circleAverage_herglotzRieszKernel_smul hI hn).trans
    (hH.circleAverage_re_herglotzRieszKernel_smul hx) |>.symm

/-- Real part of the derivative at the center of a Blaschke factor's logarithm,
in coordinates x+iy = center minus zero. -/
def projected (R x y : ℝ) : ℝ := x * (1/(x^2+y^2)-1/R^2)

theorem projected_nonneg {R x y : ℝ} (_hR : 0 < R) (hx : 0 ≤ x)
    (hn : 0 < x^2+y^2) (hd : x^2+y^2 ≤ R^2) : 0 ≤ projected R x y := by
  unfold projected
  exact mul_nonneg hx (sub_nonneg.mpr (one_div_le_one_div_of_le hn hd))

theorem projected_target {R x : ℝ} (hx : 0 < x) :
    projected R x 0 = 1/x - x/R^2 := by
  unfold projected
  simp only [zero_pow (by decide : 2 ≠ 0), add_zero]
  field_simp

/-- In a horizontal derivative of a Poisson integral, a linear convexity or subconvexity
bound on the left-hand semicircle has precisely this coefficient. -/
theorem left_semicircle_mass :
    (∫ θ : ℝ in (Real.pi / 2)..(Real.pi + Real.pi / 2), Real.cos θ^2) = Real.pi/2 := by
  rw [integral_cos_sq]
  simp [Real.cos_add, Real.sin_add]


/-- The dyadic Jensen budget as an angular integral over one turn.
The two hypotheses are pointwise upper estimates for the signed boundary
integrand on the right and left semicircles, respectively. -/
theorem angular_budget {D K E : ℝ} (hD : 0 < D) (_hK : 0 ≤ K)
    (_hE : 0 ≤ E) {f : ℝ → ℝ} (hc : Continuous f)
    (right : ∀ θ ∈ Icc (-(Real.pi/2)) (Real.pi/2), f θ ≤ E)
    (left : ∀ θ ∈ Icc (Real.pi/2) (Real.pi+Real.pi/2),
      f θ ≤ 2*D*K*(Real.cos θ)^2+E) :
    (∫ θ in (-(Real.pi/2))..(Real.pi+Real.pi/2), f θ) / (Real.pi*D)
      ≤ K + 2*E/D := by
  have hp := Real.pi_pos
  have h₁ : -(Real.pi/2) ≤ Real.pi/2 := by linarith
  have h₂ : Real.pi/2 ≤ Real.pi+Real.pi/2 := by linarith
  have hr := intervalIntegral.integral_mono_on h₁ (hc.intervalIntegrable (μ := volume) _ _)
    (intervalIntegrable_const (c := E)) right
  have il : Continuous (fun θ : ℝ => 2*D*K*(Real.cos θ)^2+E) := by fun_prop
  have hl := intervalIntegral.integral_mono_on h₂ (hc.intervalIntegrable (μ := volume) _ _) (il.intervalIntegrable (μ := volume) _ _) left
  have ht := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-(Real.pi/2)) (Real.pi/2))
    (hc.intervalIntegrable (μ := volume) (Real.pi/2) (Real.pi+Real.pi/2))
  rw [intervalIntegral.integral_const] at hr
  have hcont : Continuous (fun θ : ℝ => 2*D*K*(Real.cos θ)^2) := by fun_prop
  rw [intervalIntegral.integral_add (hcont.intervalIntegrable (μ := volume) _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, left_semicircle_mass,
    intervalIntegral.integral_const] at hl
  apply (div_le_iff₀ (mul_pos hp hD)).2
  simp only [smul_eq_mul] at hl hr
  have id : (K + 2*E/D) * (Real.pi*D) = K*(Real.pi*D)+2*E*Real.pi := by
    field_simp
  rw [id]
  linarith

/-- Error caused by projecting a target pole to the disk boundary. -/
theorem selected_disk {ι : Type*} (S : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ S)
    (x y : ι → ℝ) {R C L E : ℝ} (hR : 0 < R)
    (hX : ∀ i ∈ S, 0 ≤ x i) (hD : ∀ i ∈ S, 0 < x i ^ 2 + y i ^ 2)
    (hin : ∀ i ∈ S, x i ^ 2 + y i ^ 2 ≤ R^2)
    (h0 : y i₀ = 0) (hx : 0 < x i₀)
    (hJ : (∑ i ∈ S, projected R (x i) (y i)) ≤ C*L+E) :
    1/(x i₀) ≤ C*L+E + x i₀/R^2 := by
  have hs := Finset.single_le_sum (fun i hi => projected_nonneg hR (hX i hi)
    (hD i hi) (hin i hi)) hi₀
  rw [h0, projected_target hx] at hs
  linarith


/-- A Blaschke factor in a disk centered at zero. -/
def diskFactor (R : ℝ) (w z : ℂ) : ℂ :=
  (R:ℂ)*(z-w)/((R:ℂ)^2-(star w)*z)

theorem diskFactor_logDeriv {R : ℝ} {w : ℂ} (hR : 0 < R) (hw : w ≠ 0) :
    logDeriv (diskFactor R w) 0 = -(1/w) + (star w)/(R:ℂ)^2 := by
  have hrc : (R:ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have h1 := ((hasDerivAt_id (0:ℂ)).sub_const w).const_mul (R:ℂ)
  have h2 := ((hasDerivAt_id (0:ℂ)).const_mul (star w)).const_sub ((R:ℂ)^2)
  have h := h1.div h2 (by simp [hrc])
  unfold logDeriv
  change deriv (fun z : ℂ => (R:ℂ)*(z-w)/((R:ℂ)^2-star w*z)) 0 / _ = _
  rw [show deriv (fun z : ℂ => (R:ℂ)*(z-w)/((R:ℂ)^2-star w*z)) 0 = _ from h.deriv]
  simp only [diskFactor, id_eq, zero_sub, mul_one, mul_zero, sub_zero]
  field_simp
  ring

/-- Quotient by the disk factors adds these exact local terms. -/
theorem factor_budget {ι : Type*} (S : Finset ι) (zeros : ι → ℂ) {R : ℝ} (hR : 0 < R)
    (hw : ∀ i ∈ S, zeros i ≠ 0) :
    logDeriv (∏ i ∈ S, diskFactor R (zeros i)) 0 =
       ∑ i ∈ S, (-(1/(zeros i)) + (star (zeros i))/(R:ℂ)^2) := by
  have hrc : (R:ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    exact diskFactor_logDeriv hR (hw i hi)
  · intro i hi
    simp [diskFactor, hrc, hw i hi]
  · intro i hi
    unfold diskFactor
    fun_prop (disch := simp [hrc])

end ERH.PoissonJensenCore
