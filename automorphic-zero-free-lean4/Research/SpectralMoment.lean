import Research.BumpSpectral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! The exact second moment of the explicit angular law and the integrability needed for tails. -/

open MeasureTheory Set Filter
open scoped Topology
namespace ERH.Bump
open ERH.AveragedKernel

private noncomputable def momentTest (t z : ℝ) := z^2 * Real.sinc (z*t/2)^2

private theorem momentTest_nonneg (t z : ℝ) : 0 ≤ momentTest t z := by
  unfold momentTest
  positivity

private theorem momentTest_eq {t : ℝ} (ht : 0 < t) (z : ℝ) :
    momentTest t z = (2/t^2) * (1-Real.cos (z*t)) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [momentTest]
  have hu : z*t/2 ≠ 0 := by positivity
  rw [momentTest, Real.sinc_of_ne_zero hu, div_pow, Real.sin_sq_eq_half_sub]
  rw [show 2*(z*t/2) = z*t by ring]
  field_simp

private theorem momentTest_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) :
    Integrable (momentTest t) μ ∧
    (∫ z, momentTest t z ∂μ) = 2/t^2 * (1-cosineTransform μ t) := by
  have hi : Integrable (fun z : ℝ => Real.cos (z*t)) μ :=
    (integrable_const (1:ℝ)).mono' (by fun_prop)
      (.of_forall (fun z => by simpa using (abs_le.mpr
        ⟨Real.neg_one_le_cos (z*t), Real.cos_le_one _⟩)))
  have he := funext (momentTest_eq ht)
  rw [he]
  refine ⟨((integrable_const (1:ℝ)).sub hi).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub (integrable_const _) hi]
  simp [cosineTransform]

private noncomputable def curv (v : ℝ) : ℝ :=
  (50*v^7-540*v^5+2898*v^3-3150*v^2-840*v+1980)/199

private theorem curvature_limit {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t => 2/t^2 * (1-cosineTransform (spectralLaw b) t))
      (𝓝[>] (0 : ℝ)) (𝓝 (1980/(199*b^2))) := by
  have hc : Continuous (fun t : ℝ => curv (t/b) / b^2) := by unfold curv; fun_prop
  have hh : Tendsto (fun t : ℝ => curv (t/b) / b^2) (𝓝[>] (0 : ℝ)) (𝓝 (curv (0/b) / b^2)) :=
    (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hc0 : curv (0/b) / b^2 = 1980/(199*b^2) := by simp [curv]; ring
  rw [← hc0]
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds]
    with t (ht : 0 < t) (hb' : t < b)
  rw [spectralLaw_cosine_explicit hb ht.le, indicator_of_mem (show t ∈ Icc 0 b from ⟨ht.le,hb'.le⟩)]
  unfold h curv
  field_simp
  ring

/-- A probability whose cosine transform has finite quadratic curvature at zero
has finite second moment equal to that curvature. -/
theorem secondMoment_of_cosine_curvature (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : ℝ}
    (hcurv : Tendsto (fun t => 2/t^2 * (1-cosineTransform μ t))
      (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    Integrable (fun z : ℝ => z^2) μ ∧ (∫ z : ℝ, z^2 ∂μ) = A := by
  let F := fun t z : ℝ => ENNReal.ofReal (momentTest t z)
  have hpoint (z : ℝ) : Tendsto (fun t => momentTest t z) (𝓝[>] (0 : ℝ)) (𝓝 (z^2)) := by
    have hcont : Continuous (fun t => momentTest t z) := by unfold momentTest; fun_prop
    simpa [momentTest] using (hcont.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t => ∫⁻ z, F t z ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal A)) := by
    apply (ENNReal.tendsto_ofReal hcurv).congr'
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hi := momentTest_integral μ ht
    rw [← hi.2, ofReal_integral_eq_lintegral_ofReal hi.1 (.of_forall (momentTest_nonneg t))]
  have hfat := lintegral_liminf_le (u := 𝓝[>] (0 : ℝ)) (μ := μ)
    (f := F) (fun t => by unfold F momentTest; fun_prop)
  have hf0 (z : ℝ) : liminf (fun t => F t z) (𝓝[>] (0:ℝ)) = ENNReal.ofReal (z^2) :=
    (ENNReal.tendsto_ofReal (hpoint z)).liminf_eq
  simp_rw [hf0, hlim.liminf_eq] at hfat
  have hsq : Integrable (fun z : ℝ => z^2) μ :=
    ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (.of_forall fun z : ℝ => sq_nonneg z)).mpr
      (hfat.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hsq, ?_⟩
  have hd : Tendsto (fun t => ∫ z, momentTest t z ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z, z^2 ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z : ℝ => z^2)
      (.of_forall (fun t => by unfold momentTest; fun_prop)) ?_ hsq (.of_forall hpoint)
    filter_upwards with t
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (momentTest_nonneg _ _), momentTest]
    apply mul_le_of_le_one_right (sq_nonneg _)
    simpa [← sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one (z*t/2)) 2
  apply tendsto_nhds_unique hd
  apply hcurv.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact (momentTest_integral μ ht).2.symm

theorem spectralLaw_secondMoment {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : ℝ => z^2) (spectralLaw b) ∧
    (∫ z : ℝ, z^2 ∂spectralLaw b) = 1980/(199*b^2) := by
  let _ := spectralLaw_probability b
  exact secondMoment_of_cosine_curvature _ (curvature_limit hb)

/-- A uniform upper bound for the logarithmic conductor of a shifted constituent. -/
theorem shifted_log_conductor {b : ℝ} (hb : 0 < b) (y a : ℝ) :
    Integrable (fun z : ℝ => Real.log (2 + |y + a*z|)) (spectralLaw b) ∧
    (∫ z, Real.log (2 + |y + a*z|) ∂spectralLaw b) ≤
      Real.log (2 + |y|) + (|a| / (2+|y|)) * (1 + 1980/(199*b^2)) := by
  let μ := spectralLaw b
  let _ : IsProbabilityMeasure μ := spectralLaw_probability b
  let C := 2 + |y|
  let k := |a| / C
  have hC : 0 < C := by dsimp [C]; positivity
  have hs := spectralLaw_secondMoment hb
  have hpoint (z : ℝ) : Real.log (2 + |y + a*z|) ≤ Real.log C + k*(1+z^2) := by
    let Z := 2 + |y+a*z|
    have hZ : 0 < Z := by dsimp [Z]; positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hZ hC)
    rw [Real.log_div hZ.ne' hC.ne'] at hlog
    have hz : |z| ≤ 1+z^2 := by nlinarith [sq_nonneg (|z|-1), sq_abs z]
    have htr : Z ≤ C + |a| *(1+z^2) := by
      have htr' := abs_add_le y (a*z)
      rw [abs_mul] at htr'
      dsimp [Z, C]
      linarith [mul_le_mul_of_nonneg_left hz (abs_nonneg a)]
    have hquot : Z/C ≤ 1+k*(1+z^2) := (div_le_iff₀ hC).mpr (by
      dsimp [k]
      field_simp
      nlinarith)
    linarith
  have hi : Integrable (fun z : ℝ => Real.log C + k*(1+z^2)) μ :=
    (integrable_const _).add (((integrable_const _).add hs.1).const_mul _)
  have hilog : Integrable (fun z : ℝ => Real.log (2+|y+a*z|)) μ := by
    have hc : Continuous (fun z : ℝ => Real.log (2 + |y+a*z|)) := by
      apply Continuous.log (by fun_prop)
      intro z
      exact (by positivity : (0:ℝ) < 2+|y+a*z|).ne'
    refine hi.mono' hc.aestronglyMeasurable (.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith [abs_nonneg (y+a*z)]))]
    exact hpoint z
  refine ⟨hilog, (integral_mono hilog hi hpoint).trans ?_⟩
  have hi1 : Integrable (fun z : ℝ => 1+z^2) μ := (integrable_const _).add hs.1
  have hi2 : Integrable (fun z : ℝ => k * (1+z^2)) μ := hi1.const_mul k
  have hi3 : Integrable (fun z : ℝ => z^2) μ := hs.1
  have hval : (∫ z : ℝ, z^2 ∂μ) = 1980/(199*b^2) := hs.2
  rw [integral_add (integrable_const (Real.log C)) hi2, integral_const_mul,
    integral_add (integrable_const (1:ℝ)) hi3, hval]
  simp [k, C]

end ERH.Bump

#print axioms ERH.Bump.spectralLaw_secondMoment

#print axioms ERH.Bump.shifted_log_conductor
