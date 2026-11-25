import Research.PoissonJensenCore
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
namespace ERH.PoissonJensenCore
open Complex InnerProductSpace MeasureTheory Metric Set
open scoped Topology

theorem diskFactor_norm {R : ℝ} {z w : ℂ} (hR : 0 < R) (hz : ‖z‖ = R)
    (hw : ‖w‖ < R) : ‖diskFactor R w z‖ = 1 := by
  have hid : Complex.normSq ((R:ℂ)^2 - star w*z) -
      Complex.normSq ((R:ℂ)*(z-w)) =
      (R^2-Complex.normSq z)*(R^2-Complex.normSq w) := by
    simp [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  have hnorm : ‖(R:ℂ)^2-star w*z‖ = ‖(R:ℂ)*(z-w)‖ := by
    simp only [Complex.normSq_eq_norm_sq, hz, sub_self, zero_mul, sub_eq_zero] at hid
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hid
  have hne : z ≠ w := by intro he; rw [he] at hz; linarith
  have hR' : (R:ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hn : ‖(R:ℂ)*(z-w)‖ ≠ 0 := norm_ne_zero_iff.mpr (mul_ne_zero hR' (sub_ne_zero.mpr hne))
  unfold diskFactor
  rw [norm_div, hnorm, div_self hn]

def factored {ι : Type*} (S : Finset ι) (w : ι → ℂ) (R : ℝ) (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (G z) * ∏ i ∈ S, diskFactor R (w i) z

theorem factored_boundary {ι : Type*} (S : Finset ι) (w : ι → ℂ) {R : ℝ}
    (hR : 0 < R) (hw : ∀ i ∈ S, ‖w i‖ < R) (G : ℂ → ℂ) {z : ℂ} (hz : ‖z‖ = R) :
    Real.log ‖factored S w R G z‖ = (G z).re := by
  have hi : (∏ i ∈ S, ‖diskFactor R (w i) z‖) = 1 :=
    Finset.prod_eq_one (fun i hii => diskFactor_norm hR hz (hw i hii))
  simp [factored,norm_prod,hi,Complex.norm_exp]

/-- Differentiated Poisson--Jensen for a function in finite disk factorization.
Zeros may be repeated by the index map. The only analytic hypothesis concerns
the holomorphic logarithm of the nonvanishing factor on a neighborhood of the disk. -/
theorem factored_poisson_jensen {ι : Type*} (S : Finset ι) (w : ι → ℂ) {R : ℝ}
    (hR : 0 < R) (hw : ∀ i ∈ S, ‖w i‖ < R) (hw₀ : ∀ i ∈ S, w i ≠ 0)
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G (closedBall 0 R)) :
    (logDeriv (factored S w R G) 0).re =
      firstCoefficient R (fun z => Real.log ‖factored S w R G z‖) +
      (∑ i ∈ S, (-(1/w i) + star (w i)/(R:ℂ)^2)).re := by
  let H : ℂ → ℝ := fun z => (G z).re
  have hh : HarmonicOnNhd H (closedBall 0 R) := fun z hz => (hG z hz).harmonicAt_re
  have hi : CircleIntegrable H 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact (Complex.continuous_re.comp_continuousOn hG.continuousOn).mono sphere_subset_closedBall
  have ha := harmonic_horizontal hR hh hi
  have hd : DifferentiableAt ℂ G 0 := (hG 0 (by simpa using hR.le)).differentiableAt
  have hb : HasDerivAt (fun x : ℝ => H x) (deriv G 0).re 0 := hd.hasDerivAt.real_of_complex
  have hcoef : firstCoefficient R H =
      firstCoefficient R (fun z => Real.log ‖factored S w R G z‖) := by
    unfold firstCoefficient
    congr 1
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hz' : ‖z‖ = R := by
      simpa [mem_sphere, dist_zero_right, abs_of_pos hR] using hz
    dsimp only
    rw [factored_boundary S w hR hw G hz']
  have hr : (R:ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  let b : ℂ → ℂ := ∏ i ∈ S, diskFactor R (w i)
  have hprd : b 0 ≠ 0 := by
    simp only [b, Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => by simp [diskFactor,hr,hw₀ i hi])
  have hdisk : ∀ i ∈ S, DifferentiableAt ℂ (diskFactor R (w i)) 0 := by
    intro i _
    unfold diskFactor
    fun_prop (disch := simp [hr])
  have hb' : DifferentiableAt ℂ b 0 := DifferentiableAt.finsetProd hdisk
  have heq : factored S w R G = (fun z => Complex.exp (G z)) * b := by
    funext z
    simp [b,factored]
  have hexp : logDeriv (fun z => Complex.exp (G z)) 0 = deriv G 0 := by
    change deriv (fun z => Complex.exp (G z)) 0 / Complex.exp (G 0) = _
    rw [hd.hasDerivAt.cexp.deriv]
    field_simp
  rw [heq, logDeriv_mul (f := fun z => Complex.exp (G z)) 0 (Complex.exp_ne_zero _) hprd hd.cexp hb', hexp]
  change (deriv G 0 + logDeriv (∏ i ∈ S, diskFactor R (w i)) 0).re = _
  rw [factor_budget S w hR hw₀, Complex.add_re, hb.unique ha, hcoef, heq]

/-- The boundary Fourier coefficient as the normalized cosine integral on the
same period used by the two semicircles in the growth budget. -/
theorem firstCoefficient_cos {R : ℝ} (hR : 0 < R) {H : ℂ → ℝ}
    (hH : ContinuousOn H (sphere 0 R)) :
    firstCoefficient R H = (∫ θ : ℝ in (-(Real.pi/2))..(Real.pi+Real.pi/2),
      Real.cos θ * H (circleMap 0 R θ)) / (Real.pi*R) := by
  let F : ℂ → ℂ := fun z => (2*z/(z-0)^2) • (H z:ℂ)
  have hne : ∀ z ∈ sphere (0:ℂ) R, z ≠ 0 := by
    intro z hz he
    subst z
    exact hR.ne (by simpa [mem_sphere] using hz)
  have hden : ∀ z ∈ sphere (0:ℂ) R, (z-0)^2 ≠ 0 := by
    intro z hz
    simpa using hne z hz
  have hF : ContinuousOn F (sphere 0 R) := by
    unfold F
    apply ContinuousOn.mul
    swap
    · exact Complex.continuous_ofReal.comp_continuousOn hH
    exact ((continuous_const.mul continuous_id).continuousOn).div
      ((continuous_id.sub continuous_const).pow 2).continuousOn hden
  change Complex.reCLM (Real.circleAverage F 0 R) = _
  rw [← Complex.reCLM.circleAverage_comp_comm (hF.circleIntegrable hR.le)]
  let h : ℝ → ℝ := fun θ => Real.cos θ * H (circleMap 0 R θ)
  have heval (θ : ℝ) : (Complex.reCLM ∘ F) (circleMap 0 R θ) = (2/R)*h θ := by
    let z := circleMap 0 R θ
    have hz : z ≠ 0 := by simp [z,hR.ne']
    have he : (2:ℂ)*z/(z-0)^2 = 2*z⁻¹ := by simp [field]
    change (((2:ℂ)*z/(z-0)^2)*(H z:ℂ)).re = _
    rw [he]
    simp [Complex.mul_re, z,circleMap_zero_inv,circleMap_zero_re,h]
    ring
  have hp : Function.Periodic h (2*Real.pi) := by
    intro θ
    simp [h,periodic_circleMap 0 R θ]
  have hrot := hp.intervalIntegral_add_eq 0 (-(Real.pi/2))
  rw [zero_add,show -(Real.pi/2)+2*Real.pi=Real.pi+Real.pi/2 by ring] at hrot
  rw [Real.circleAverage_def]
  simp_rw [heval]
  rw [intervalIntegral.integral_const_mul, hrot, smul_eq_mul]
  change _ = (∫ θ : ℝ in (-(Real.pi/2))..(Real.pi+Real.pi/2), h θ)/(Real.pi*R)
  ring

end ERH.PoissonJensenCore
