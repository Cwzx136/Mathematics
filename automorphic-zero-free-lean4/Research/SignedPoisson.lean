import Research.AveragedKernel
import Research.SignedHadamard
import Research.TiltedWindow

/-! The exact zero-side Laplace kernel after averaging with a signed frequency law. -/

open MeasureTheory Set
namespace ERH.SignedHadamard

private theorem cosine_shift_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (y a x : ℝ) :
    Integrable (fun z : ℝ => Real.cos ((y+a*z)*x)) μ :=
  (integrable_const (1:ℝ)).mono' (by fun_prop) (.of_forall (fun z => by
    simpa using abs_le.mpr ⟨Real.neg_one_le_cos ((y+a*z)*x),Real.cos_le_one _⟩))

private theorem K_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] {v : ℝ} (hv : 0 < v)
    (y a : ℝ) : Integrable (fun z : ℝ => v/(v^2+(y+a*z)^2)) μ := by
  have hc : Continuous (fun z : ℝ => v/(v^2+(y+a*z)^2)) :=
    continuous_const.div (by fun_prop) (fun z => by positivity)
  apply (integrable_const (1/v)).mono' hc.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ v/v^2 := div_le_div_of_nonneg_left hv.le (by positivity) (le_add_of_nonneg_right (sq_nonneg _))
    _ = _ := by field_simp

private theorem positive_kernel (μ : Measure ℝ) [IsFiniteMeasure μ] {v : ℝ} (hv : 0 < v)
    (y a : ℝ) :
    (∫ z, v/(v^2+(y+a*z)^2) ∂μ) =
      ∫ x in Ioi (0:ℝ), Real.exp (-v*x) * (∫ z, Real.cos ((y+a*z)*x) ∂μ) := by
  have h := ERH.AveragedKernel.poisson_average (μ.map (fun z : ℝ => y+a*z)) hv
  unfold ERH.AveragedKernel.cosineTransform at h
  have hc : Continuous (fun z : ℝ => v/(v^2+z^2)) :=
    continuous_const.div (by fun_prop) (fun z => by positivity)
  rw [integral_map (by fun_prop) hc.aestronglyMeasurable] at h
  have ht (x : ℝ) : (∫ z, Real.cos (z*x) ∂(μ.map (fun u => y+a*u))) =
      ∫ z, Real.cos ((y+a*z)*x) ∂μ := integral_map (by fun_prop) (by fun_prop)
  simpa only [ht] using h

private theorem damped_transform_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] {v : ℝ}
    (hv : 0 < v) (y a : ℝ) : IntegrableOn
    (fun x : ℝ => Real.exp (-v*x) * (∫ z, Real.cos ((y+a*z)*x) ∂μ)) (Ioi 0) := by
  have hm : StronglyMeasurable (fun x : ℝ => ∫ z, Real.cos ((y+a*z)*x) ∂μ) :=
    (show Continuous (fun p : ℝ×ℝ => Real.cos ((y+a*p.2)*p.1)) from by fun_prop).stronglyMeasurable.integral_prod_right'
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hv) 0).mul_const (μ.real univ)).mono'
    ((show Continuous (fun x : ℝ => Real.exp (-v*x)) from by fun_prop).aestronglyMeasurable.mul
      hm.aestronglyMeasurable)
  filter_upwards with x
  simp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply (norm_integral_le_integral_norm _).trans
  simpa using integral_mono (cosine_shift_integrable μ y a x).norm (integrable_const (1:ℝ))
    (fun z => (abs_le.mpr ⟨Real.neg_one_le_cos ((y+a*z)*x),Real.cos_le_one _⟩))

/-- Real affine frequency shifts commute with the Poisson--Laplace identity for every
finite signed measure, with no positivity and no moment hypothesis on its signed density. -/
theorem signed_poisson (ν : SignedMeasure ℝ) {v : ℝ} (hv : 0 < v) (y a : ℝ) :
    average ν (fun z => v/(v^2+(y+a*z)^2)) =
      ∫ x in Ioi (0:ℝ), Real.exp (-v*x) * average ν (fun z => Real.cos ((y+a*z)*x)) := by
  let μ := ν.toJordanDecomposition.posPart
  let κ := ν.toJordanDecomposition.negPart
  rw [average_jordan _ _ (K_integrable _ hv y a)]
  have hcos (x : ℝ) := average_jordan ν _ (cosine_shift_integrable ν.totalVariation y a x)
  simp_rw [hcos, mul_sub]
  rw [integral_sub (damped_transform_integrable μ hv y a) (damped_transform_integrable κ hv y a),
    positive_kernel _ hv y a, positive_kernel _ hv y a]

/-- With a reflection-invariant signed law the sine term cancels. The remaining
cosine transform can have either sign. -/
theorem even_signed_poisson (ν : SignedMeasure ℝ) (evenν : ν.map (fun z : ℝ => -z) = ν)
    {v : ℝ} (hv : 0 < v) (y a : ℝ) :
    average ν (fun z => v/(v^2+(y+a*z)^2)) =
      ∫ x in Ioi (0:ℝ), Real.exp (-v*x) * (Real.cos (y*x) *
        average ν (fun z => Real.cos (z*(a*x)))) := by
  rw [signed_poisson ν hv y a]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  congr 1
  let F := fun z : ℝ => Real.cos ((y+a*z)*x)
  let G := fun z : ℝ => Real.cos ((y+a*(-z))*x)
  have heq : average ν F = average ν G := by
    change (∫ᵛ z, F z ∂<•ν) = ∫ᵛ z, F (-z) ∂<•ν
    conv_lhs => rw [← evenν]
    exact (MeasurableEquiv.neg ℝ).measurableEmbedding.integral_map_vectorMeasure
  have hF : ν.Integrable F := by
    rw [VectorMeasure.Integrable, ← ν.totalVariation_eq_variation]
    apply cosine_shift_integrable
  have hG : ν.Integrable G := by
    rw [VectorMeasure.Integrable, ← ν.totalVariation_eq_variation]
    simpa [G] using cosine_shift_integrable ν.totalVariation y (-a) x
  have htrig (z : ℝ) : F z + G z = (2*Real.cos (y*x))*Real.cos (z*(a*x)) := by
    simp only [F, G, mul_neg, ← sub_eq_add_neg, add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    rw [show a*z*x=z*(a*x) by ring]
    ring
  have hd : 2 * average ν F = (2*Real.cos (y*x)) * average ν (fun z => Real.cos (z*(a*x))) := by
    calc
      2 * average ν F = average ν F + average ν G := by rw [← heq]; ring
      _ = average ν (fun z => F z+G z) := (VectorMeasure.integral_fun_add hF hG).symm
      _ = average ν (fun z => (2*Real.cos (y*x))*Real.cos (z*(a*x))) := by simp only [htrig]
      _ = _ := VectorMeasure.integral_fun_smul ν _ _ _
  change average ν F = _
  linarith

/-- The actual signed-shift Poisson average of every retained zero is nonnegative when
the signed law realizes the tilted characteristic function and the prior strip covers that zero. -/
theorem retained_zero_nonneg (ν : SignedMeasure ℝ) (evenν : ν.map (fun z : ℝ => -z) = ν)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (W y u a w : ℝ) (hv : 0 < u+w) (prior : a ≤ w)
    (integrableWindow : IntegrableOn (fun x => Real.cos (y*x)*ERH.AveragedKernel.cosineTransform μ (W*x))
      (Ioi (0:ℝ)))
    (spectrum : ∀ x, 0 < x → average ν (fun z => Real.cos (z*x)) =
      Real.exp ((u+a)*x)*ERH.AveragedKernel.cosineTransform μ (W*x)) :
    0 ≤ average ν (fun z => (u+w)/((u+w)^2+(y+z)^2)) := by
  have hp := even_signed_poisson ν evenν hv y 1
  simp only [one_mul] at hp
  rw [hp]
  have he : (∫ x in Ioi (0:ℝ), Real.exp (-(u+w)*x) *
      (Real.cos (y*x)*average ν (fun z => Real.cos (z*x)))) =
      ∫ x in Ioi (0:ℝ), Real.exp ((u+a)*x)*ERH.AveragedKernel.cosineTransform μ (W*x) *
        Real.exp (-(u+w)*x)*Real.cos (y*x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [spectrum x hx]
    ring
  rw [he]
  exact ERH.TiltedWindow.tilted_response_nonneg μ W y u a w integrableWindow prior

end ERH.SignedHadamard

#print axioms ERH.SignedHadamard.signed_poisson

#print axioms ERH.SignedHadamard.even_signed_poisson

#print axioms ERH.SignedHadamard.retained_zero_nonneg
