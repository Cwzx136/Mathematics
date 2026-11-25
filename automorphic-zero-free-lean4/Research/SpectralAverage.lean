import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! The spectral-shift average of the original pole kernel is exactly the
Laplace transform of the nonnegative Euler weight. No arithmetic, or assumptions
about a characteristic-function formula, are needed in this identity. -/

noncomputable section
namespace ERH.SpectralAverage
open Complex MeasureTheory Set

def cosineTransform (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ v : ℝ, Real.cos (v*x) ∂μ

theorem laplace_cos {a : ℝ} (ha : 0 < a) (v : ℝ) :
    (∫ x : ℝ in Ioi (0 : ℝ), Real.exp (-a*x)*Real.cos (v*x)) = a/(a^2+v^2) := by
  let c : ℂ := ⟨-a,v⟩
  have hc : c.re < 0 := by simpa [c] using ha
  have H := integral_exp_mul_complex_Ioi hc 0
  have HI := integrableOn_exp_mul_complex_Ioi hc 0
  have inner (x : ℝ) : (Complex.exp (c * (x:ℂ))).re = Real.exp (-a*x)*Real.cos (v*x) := by
    simp [Complex.exp_re, c, Complex.mul_re, Complex.mul_im]
  simp_rw [← inner]
  change (∫ x : ℝ in Ioi (0:ℝ), RCLike.re (Complex.exp (c*x))) = _
  rw [integral_re HI, H, RCLike.re_to_complex]
  simp [c, Complex.div_re, Complex.normSq_apply, sq]

/-- Fubini is justified for every finite measure by domination by exp(-a x).
The arithmetic application samples an even probability whose cosine transform is nonnegative. -/
theorem averaged_pole (μ : Measure ℝ) [IsFiniteMeasure μ] {a : ℝ} (ha : 0 < a) :
    (∫ v : ℝ, a/(a^2+v^2) ∂μ) =
      ∫ x : ℝ in Ioi (0 : ℝ), Real.exp (-a*x) * cosineTransform μ x := by
  let f (v x : ℝ) : ℝ := Real.exp (-a*x) * Real.cos (v*x)
  have H0 : IntegrableOn (fun x : ℝ => Real.exp (-a*x)) (Ioi (0:ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) _
  have HI : Integrable (Function.uncurry f) (μ.prod (volume.restrict (Ioi 0))) := by
    apply (H0.comp_snd μ).mono'
    · apply Continuous.aestronglyMeasurable
      unfold f Function.uncurry
      fun_prop
    · filter_upwards with z
      simp only [Function.uncurry, f, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have hs := integral_integral_swap HI
  simp only [f, ← laplace_cos ha] at *
  unfold cosineTransform
  simpa only [integral_const_mul] using hs

end ERH.SpectralAverage
