import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Tactic

/-! Pointwise and spectral positivity of real autocorrelation windows. -/

open MeasureTheory FourierTransform
open SchwartzMap
open scoped Convolution ComplexConjugate ContDiff
namespace ERH.SpectralWindow

/-- The physical autocorrelation, without normalization. -/
noncomputable def autocorrelation (g : ℝ → ℝ) : ℝ → ℝ :=
  g ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun y => g (-y))

theorem autocorrelation_apply (g : ℝ → ℝ) (x : ℝ) :
    autocorrelation g x = ∫ y, g y * g (y - x) := by
  simp [autocorrelation, convolution_def]

theorem autocorrelation_zero (g : ℝ → ℝ) :
    autocorrelation g 0 = ∫ y, g y ^ 2 := by
  simp [autocorrelation_apply, pow_two]

theorem autocorrelation_nonneg {g : ℝ → ℝ} (hg : ∀ y, 0 ≤ g y) (x : ℝ) :
    0 ≤ autocorrelation g x := by
  rw [autocorrelation_apply]
  exact integral_nonneg (fun y => mul_nonneg (hg _) (hg _))

/-- A real input turns physical reflection into complex conjugation in frequency. -/
theorem fourier_reflection (g : ℝ → ℝ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (g (-x) : ℂ)) ξ = conj (𝓕 (fun x : ℝ => (g x : ℂ)) ξ) := by
  let f := fun x : ℝ => (g x : ℂ)
  change 𝓕 (fun x => f (-x)) ξ = conj (𝓕 f ξ)
  rw [← Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq_fourier_neg,
    Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  congr 1
  funext x
  simp [f, smul_eq_mul, ← Complex.exp_conj, map_ofNat]

theorem complex_autocorrelation (g : ℝ → ℝ) :
    (fun x : ℝ => (autocorrelation g x : ℂ)) =
      (fun x : ℝ => (g x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (fun x : ℝ => (g (-x) : ℂ)) := by
  funext x
  simp only [autocorrelation_apply, convolution_def, ContinuousLinearMap.mul_apply',
    neg_sub, ← Complex.ofReal_mul, integral_complex_ofReal]

theorem fourier_autocorrelation {g : ℝ → ℝ} (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (autocorrelation g x : ℂ)) ξ =
      (‖𝓕 (fun x : ℝ => (g x : ℂ)) ξ‖ ^ 2 : ℝ) := by
  have hf : Integrable (fun x : ℝ => (g x : ℂ)) := hg.ofReal
  have hneg : Integrable (fun x : ℝ => (g (-x) : ℂ)) := hf.comp_neg
  rw [complex_autocorrelation, Real.fourier_mul_convolution_eq hf hneg, fourier_reflection,
    Complex.mul_conj', Complex.ofReal_pow]

/-- The classical integral Fourier transform agrees a.e. with the unitary transform of an
`L¹ ∩ L²` function.  Pairing against compactly supported smooth tests avoids a representative
choice at individual frequencies. -/
theorem classical_fourier_memLp {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    MemLp (𝓕 f) 2 := by
  let F : Lp (α := ℝ) ℂ 2 := h₂.toLp f
  have hcont : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ h₁
  have heq : (fun x => (𝓕 F) x) =ᵐ[volume] 𝓕 f := by
    apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
      hcont.locallyIntegrable
    intro q hq hqc
    have hqc' : HasCompactSupport (Complex.ofRealCLM ∘ q) := hqc.comp_left rfl
    have hqs : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ q) := by fun_prop
    let Q := hqc'.toSchwartzMap hqs
    have hd := congrArg (fun D : 𝓢'(ℝ, ℂ) => D Q) (Lp.fourier_toTemperedDistribution_eq F)
    change Lp.toTemperedDistribution F (𝓕 Q) = Lp.toTemperedDistribution (𝓕 F) Q at hd
    rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at hd
    have hpair : (∫ x, (𝓕 Q) x • f x) = ∫ x, Q x • (𝓕 f) x := by
      simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
        Real.continuous_fourierChar continuous_inner Q.integrable h₁
    calc
      _ = ∫ x, Q x • (𝓕 F) x := by simp [Q]
      _ = ∫ x, (𝓕 Q) x • F x := hd.symm
      _ = ∫ x, (𝓕 Q) x • f x := by
        apply integral_congr_ae
        filter_upwards [h₂.coeFn_toLp] with x hx
        rw [show F x = f x from hx]
      _ = ∫ x, Q x • (𝓕 f) x := hpair
      _ = _ := by simp [Q]
  exact (Lp.memLp _).ae_eq heq

/-- Cyclic-frequency spectral density.  Angular frequency `λ` corresponds to `2πξ`. -/
noncomputable def density (g : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ‖𝓕 (fun x : ℝ => (g x : ℂ)) ξ‖ ^ 2

theorem density_nonneg (g : ℝ → ℝ) (ξ : ℝ) : 0 ≤ density g ξ := sq_nonneg _

theorem density_integrable {g : ℝ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g) :
    Integrable (density g) := by
  let f : ℝ → ℂ := fun x => (g x : ℂ)
  have hfc : Continuous f := Complex.continuous_ofReal.comp hc
  have hfs : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hF := classical_fourier_memLp (hfc.integrable_of_hasCompactSupport hfs)
    (hfc.memLp_of_hasCompactSupport hfs)
  exact (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF

theorem autocorrelation_inversion {g : ℝ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    (x : ℝ) : (∫ ξ, density g ξ * Real.cos (2 * Real.pi * ξ * x)) =
      autocorrelation g x := by
  let C : ℝ → ℂ := fun u => (autocorrelation g u : ℂ)
  let D : ℝ → ℂ := fun u => (density g u : ℂ)
  have hi : Integrable g := hc.integrable_of_hasCompactSupport hs
  have hneg : HasCompactSupport (fun u => g (-u)) := hs.comp_homeomorph (Homeomorph.neg ℝ)
  have hcc : Continuous (autocorrelation g) :=
    hneg.continuous_convolution_right _ hc.locallyIntegrable (hc.comp continuous_neg)
  have hci : Integrable C := (hi.integrable_convolution _ hi.comp_neg).ofReal
  have hdi := density_integrable hc hs
  have hDC : D = 𝓕 C := funext (fun ξ => (fourier_autocorrelation hi ξ).symm)
  have hinv : 𝓕 D (-x) = C x := by
    rw [hDC, ← Real.fourierInv_eq_fourier_neg]
    exact hci.fourierInv_fourier_eq (hDC ▸ hdi.ofReal)
      (Complex.continuous_ofReal.comp hcc).continuousAt
  have hfint : Integrable (fun ξ : ℝ =>
      Complex.exp ((2 * Real.pi * (ξ : ℂ) * x) * Complex.I) * D ξ) := by
    apply hdi.mono'
    · apply AEStronglyMeasurable.mul _ hdi.ofReal.aestronglyMeasurable
      exact (show Continuous (fun ξ : ℝ =>
        Complex.exp ((2 * Real.pi * (ξ : ℂ) * x) * Complex.I)) from by fun_prop).aestronglyMeasurable
    · filter_upwards with ξ
      simp [D, Complex.norm_exp, Real.norm_of_nonneg (density_nonneg g ξ)]
  rw [Real.fourier_real_eq_integral_exp_smul] at hinv
  have hr := congrArg Complex.re hinv
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, neg_mul,
    mul_neg, neg_neg, smul_eq_mul] at hr
  have hre := (integral_re hfint).trans hr
  simpa [D, C, RCLike.re_eq_complex_re, Complex.mul_re, Complex.exp_re, Complex.mul_im, mul_comm, mul_left_comm,
    mul_assoc] using hre

/-- The probability law is expressed as a pushforward so that the exposed variable has
angular-frequency units. -/
noncomputable def angularLaw (g : ℝ → ℝ) : Measure ℝ :=
  (volume.withDensity (fun ξ => ENNReal.ofReal (density g ξ / autocorrelation g 0))).map
    (fun ξ : ℝ => 2 * Real.pi * ξ)

theorem angularLaw_probability {g : ℝ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    (hm : 0 < autocorrelation g 0) : IsProbabilityMeasure (angularLaw g) := by
  let m := autocorrelation g 0
  have hD := density_integrable hc hs
  have hmass : (∫ ξ, density g ξ) = m := by
    simpa [m] using autocorrelation_inversion hc hs 0
  have htotal : (∫ ξ, density g ξ / m) = 1 := by rw [integral_div, hmass, div_self hm.ne']
  have hp : IsProbabilityMeasure (volume.withDensity
      (fun ξ => ENNReal.ofReal (density g ξ / m))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hD.div_const m)
        (.of_forall (fun ξ => div_nonneg (density_nonneg g ξ) hm.le)), htotal]
    simp
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 hp

theorem angularLaw_cosine {g : ℝ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    (hm : 0 < autocorrelation g 0) (x : ℝ) :
    (∫ z, Real.cos (z * x) ∂angularLaw g) = autocorrelation g x / autocorrelation g 0 := by
  let m := autocorrelation g 0
  have hD := density_integrable hc hs
  unfold angularLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((hD.div_const m).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (.of_forall (fun _ => ENNReal.ofReal_lt_top)) _]
  change (∫ ξ, (ENNReal.ofReal (density g ξ / m)).toReal * Real.cos (2 * Real.pi * ξ * x)) = _
  have hz (ξ : ℝ) : (ENNReal.ofReal (density g ξ / m)).toReal = density g ξ / m :=
    ENNReal.toReal_ofReal (div_nonneg (density_nonneg g ξ) hm.le)
  simp only [hz, div_mul_eq_mul_div, integral_div, autocorrelation_inversion hc hs, m]


end ERH.SpectralWindow

#print axioms ERH.SpectralWindow.fourier_autocorrelation

#print axioms ERH.SpectralWindow.autocorrelation_inversion
#print axioms ERH.SpectralWindow.angularLaw_probability
#print axioms ERH.SpectralWindow.angularLaw_cosine
