import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! Positive frequency averaging and the cosine Laplace transform of the Poisson kernel. -/

open MeasureTheory Set
namespace ERH.AveragedKernel

/-- Angular-frequency convention, with no factor of `2π`. -/
noncomputable def cosineTransform (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ z, Real.cos (z * x) ∂μ

/-- The elementary transform evaluated using an absolutely convergent complex integral. -/
theorem laplace_cos {t : ℝ} (ht : 0 < t) (z : ℝ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * Real.cos (z * x)) = t / (t ^ 2 + z ^ 2) := by
  let a : ℂ := ⟨-t, z⟩
  have ha : a.re < 0 := neg_lt_zero.mpr ht
  have hre (x : ℝ) :
      (Complex.exp (a * (x : ℂ))).re = Real.exp (-t * x) * Real.cos (z * x) := by
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, a]
  calc
    _ = ∫ x in Ioi (0 : ℝ), RCLike.re (Complex.exp (a * x)) := by
      simp only [RCLike.re_eq_complex_re, hre]
    _ = (∫ x in Ioi (0 : ℝ), Complex.exp (a * x)).re :=
      integral_re (integrableOn_exp_mul_complex_Ioi ha 0)
    _ = _ := by
      rw [integral_exp_mul_complex_Ioi ha]
      simp [Complex.div_re, Complex.normSq_apply, a, pow_two]

/-- Fubini for a finite frequency measure.  In particular, this includes every probability
law, irrespective of symmetry, absolute continuity, or the existence of moments. -/
theorem poisson_average (μ : Measure ℝ) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) :
    (∫ z, t / (t ^ 2 + z ^ 2) ∂μ) =
      ∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * cosineTransform μ x := by
  have hdom : Integrable (fun p : ℝ × ℝ => Real.exp (-t * p.1))
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ht) 0).comp_fst μ
  have habs : Integrable (Function.uncurry
      (fun x z : ℝ => Real.exp (-t * x) * Real.cos (z * x)))
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
    apply hdom.mono'
    · exact (show Continuous (Function.uncurry
          (fun x z : ℝ => Real.exp (-t * x) * Real.cos (z * x))) from by
            unfold Function.uncurry
            fun_prop).aestronglyMeasurable
    · filter_upwards with p
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (abs_le.mpr
        ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  calc
    _ = ∫ z, (∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * Real.cos (z * x)) ∂μ := by
      simp_rw [laplace_cos ht]
    _ = ∫ x in Ioi (0 : ℝ), ∫ z, Real.exp (-t * x) * Real.cos (z * x) ∂μ :=
      (integral_integral_swap habs).symm
    _ = _ := by simp_rw [cosineTransform, integral_const_mul]

/-- A positive frequency average retains the sign of every omitted Poisson kernel. -/
theorem shifted_poisson_nonneg (μ : Measure ℝ) (t y s : ℝ) (ht : 0 ≤ t) :
    0 ≤ ∫ z, t / (t ^ 2 + (y + s * z) ^ 2) ∂μ :=
  integral_nonneg (fun _ => div_nonneg ht (add_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- Symmetric positive averaging of an absolutely convergent Euler cosine series.
The frequency law itself need not be symmetric. -/
theorem average_euler {ι : Type*} [Countable ι] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (weight phase freq : ι → ℝ) (hw : Summable (fun i => |weight i|)) :
    (∫ z, (∑' i, weight i * ((Real.cos (phase i + z * freq i) +
      Real.cos (phase i - z * freq i)) / 2)) ∂μ) =
      ∑' i, (weight i * Real.cos (phase i)) * cosineTransform μ (freq i) := by
  let F : ι → ℝ → ℝ := fun i z => (weight i * Real.cos (phase i)) * Real.cos (z * freq i)
  have htrig (i : ι) (z : ℝ) : weight i * ((Real.cos (phase i + z * freq i) +
      Real.cos (phase i - z * freq i)) / 2) = F i z := by
    rw [Real.cos_add, Real.cos_sub]
    dsimp [F]
    ring
  have hb (i : ι) (z : ℝ) : ‖F i z‖ ≤ |weight i| := by
    simp only [F, Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (|weight i| * 1) * 1 := by
        gcongr <;> exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      _ = _ := by ring
  have hi (i : ι) : Integrable (F i) μ :=
    (integrable_const |weight i|).mono'
      ((show Continuous (F i) from by dsimp [F]; fun_prop).aestronglyMeasurable)
      (.of_forall (hb i))
  have hsum : Summable (fun i => ∫ z, ‖F i z‖ ∂μ) := by
    apply hw.of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
    intro i
    simpa using integral_mono (hi i).norm (integrable_const |weight i|) (hb i)
  simp_rw [htrig]
  rw [← integral_tsum_of_summable_integral_norm hi hsum]
  simp_rw [F, cosineTransform, integral_const_mul]

/-- Pointwise nonnegative Euler coefficients retain their sign under a nonnegative window. -/
theorem weighted_tsum_nonneg {ι : Type*} (weight freq : ι → ℝ)
    (h : ℝ → ℝ) (hw : ∀ i, 0 ≤ weight i) (hh : ∀ x, 0 ≤ h x) :
    0 ≤ ∑' i, weight i * h (freq i) :=
  tsum_nonneg (fun i => mul_nonneg (hw i) (hh _))

end ERH.AveragedKernel

#print axioms ERH.AveragedKernel.laplace_cos
#print axioms ERH.AveragedKernel.poisson_average
#print axioms ERH.AveragedKernel.shifted_poisson_nonneg

#print axioms ERH.AveragedKernel.average_euler
