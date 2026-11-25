import Research.BumpLimit

/-! The sign of a tilted response follows from the untilted spectral law evaluated at the
effective real argument. The tilted multiplier itself has no definiteness hypothesis. -/

open MeasureTheory Set Filter
open scoped Topology
namespace ERH.TiltedWindow
open ERH.AveragedKernel

/-- A modulated cosine transform is the cosine transform of a positive law, up to a factor
of two. The law is the sum of the two reflected translates. -/
private noncomputable def shifts (μ : Measure ℝ) (W y : ℝ) :=
  μ.map (fun z : ℝ => y+W*z) + μ.map (fun z : ℝ => y-W*z)

private theorem cosine_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun z : ℝ => Real.cos (z*x)) μ :=
  (integrable_const (1:ℝ)).mono' (by fun_prop) (.of_forall (fun z => by
    simpa using abs_le.mpr ⟨Real.neg_one_le_cos (z*x), Real.cos_le_one _⟩))

private theorem shift_transform (μ : Measure ℝ) [IsFiniteMeasure μ] (W y x : ℝ) :
    cosineTransform (shifts μ W y) x =
      2 * (Real.cos (y*x) * cosineTransform μ (W*x)) := by
  unfold shifts cosineTransform
  rw [integral_add_measure (cosine_integrable _ _) (cosine_integrable _ _),
    integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
  have hi (v : ℝ → ℝ) (hc : Continuous v) : Integrable (fun z => Real.cos (v z*x)) μ :=
    (integrable_const (1:ℝ)).mono' (by fun_prop) (.of_forall (fun z => by
      simpa using abs_le.mpr ⟨Real.neg_one_le_cos (v z*x), Real.cos_le_one _⟩))
  rw [← integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop))]
  have hh (z : ℝ) : Real.cos ((y+W*z)*x)+Real.cos ((y-W*z)*x) =
      (2*Real.cos (y*x))*Real.cos (z*(W*x)) := by
    rw [add_mul,sub_mul,Real.cos_add,Real.cos_sub]
    rw [show W*z*x=z*(W*x) by ring]
    ring
  simp only [hh, integral_const_mul, mul_assoc]

theorem response_pos_real (μ : Measure ℝ) [IsFiniteMeasure μ] (W y : ℝ)
    {v : ℝ} (hv : 0 < v) :
    0 ≤ ∫ x in Ioi (0 : ℝ), Real.exp (-v*x) *
          (Real.cos (y*x) * cosineTransform μ (W*x)) := by
  let ν := shifts μ W y
  let _ : IsFiniteMeasure ν := by dsimp [ν, shifts]; infer_instance
  have h := poisson_average ν hv
  have hh (x : ℝ) : Real.exp (-v*x) * cosineTransform ν x =
      2 * (Real.exp (-v*x) * (Real.cos (y*x) * cosineTransform μ (W*x))) := by
    rw [show cosineTransform ν x = _ from shift_transform μ W y x]
    ring
  simp_rw [hh, integral_const_mul] at h
  have h0 : 0 ≤ ∫ z, v/(v^2+z^2) ∂ν :=
    integral_nonneg (fun z => div_nonneg hv.le (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  linarith

/-- The closed right half-plane, including purely imaginary arguments.  At the boundary
the only extra input is ordinary integrability of the undamped modulated window. -/
theorem response_closed (μ : Measure ℝ) [IsFiniteMeasure μ] (W y : ℝ)
    (h0 : IntegrableOn (fun x => Real.cos (y*x)*cosineTransform μ (W*x)) (Ioi 0))
    {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ ∫ x in Ioi (0 : ℝ), Real.exp (-v*x) *
          (Real.cos (y*x)*cosineTransform μ (W*x)) := by
  rcases hv.eq_or_lt with rfl|hp
  · let F := fun x : ℝ => Real.cos (y*x)*cosineTransform μ (W*x)
    have ht : Tendsto (fun t => ∫ x in Ioi (0:ℝ), Real.exp (-t*x)*F x) (𝓝[>] (0:ℝ))
        (𝓝 (∫ x in Ioi (0:ℝ), F x)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖) ?_ ?_
        h0.norm ?_
      · filter_upwards with t
        exact (show Continuous (fun x : ℝ => Real.exp (-t*x)) from by fun_prop).aestronglyMeasurable.mul
          h0.aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with t (ht : 0<t)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_of_le_one_left (norm_nonneg _) ((Real.exp_le_one_iff).mpr (by nlinarith))
      · filter_upwards with x
        have hc : Continuous (fun t : ℝ => Real.exp (-t*x)*F x) := by fun_prop
        simpa using (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have pos := ge_of_tendsto ht (Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t (ht' : 0 < t) => response_pos_real μ W y ht'))
    simpa [F] using pos
  · exact response_pos_real μ W y hp

/-- The growing exponential tilt cancels before the sign argument is applied. -/
theorem tilted_response_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] (W y u a w : ℝ)
    (h0 : IntegrableOn (fun x => Real.cos (y*x)*cosineTransform μ (W*x)) (Ioi 0))
    (prior : a ≤ w) :
    0 ≤ ∫ x in Ioi (0:ℝ), Real.exp ((u+a)*x)*cosineTransform μ (W*x) *
      Real.exp (-(u+w)*x)*Real.cos (y*x) := by
  have hh (x : ℝ) : Real.exp ((u+a)*x)*cosineTransform μ (W*x) *
      Real.exp (-(u+w)*x)*Real.cos (y*x) =
      Real.exp (-(w-a)*x) * (Real.cos (y*x)*cosineTransform μ (W*x)) := by
    rw [show -(w-a)*x=(u+a)*x+(-(u+w)*x) by ring, Real.exp_add]
    ring
  simp_rw [hh]
  exact response_closed μ W y h0 (sub_nonneg.mpr prior)

/-- The nonnegativity statement expressed directly as the real part of the complex
Lebesgue integral at a point of the closed right half-plane. -/
theorem complex_response_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] (W : ℝ)
    (hbase : IntegrableOn (fun x => cosineTransform μ (W*x)) (Ioi (0:ℝ)))
    (z : ℂ) (hz : 0 ≤ z.re) :
    0 ≤ (∫ x in Ioi (0:ℝ), Complex.exp (-z*(x:ℂ)) * (cosineTransform μ (W*x):ℂ)).re := by
  have hf : IntegrableOn (fun x : ℝ => Complex.exp (-z*(x:ℂ)) *
      (cosineTransform μ (W*x):ℂ)) (Ioi (0:ℝ)) := by
    apply hbase.norm.mono'
    · exact (show Continuous (fun x : ℝ => Complex.exp (-z*(x:ℂ))) from by fun_prop).aestronglyMeasurable.mul
        hbase.ofReal.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
      rw [norm_mul, Complex.norm_exp, Complex.norm_real]
      apply mul_le_of_le_one_left (norm_nonneg _)
      apply Real.exp_le_one_iff.mpr
      simp [Complex.mul_re, mul_nonneg hz hx.le]
  have hcos : IntegrableOn (fun x => Real.cos (z.im*x)*cosineTransform μ (W*x)) (Ioi (0:ℝ)) := by
    apply hbase.norm.mono'
    · exact (show Continuous (fun x : ℝ => Real.cos (z.im*x)) from by fun_prop).aestronglyMeasurable.mul
        hbase.aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
  have hreal := integral_re hf
  rw [RCLike.re_eq_complex_re] at hreal
  rw [← hreal]
  simpa [RCLike.re_eq_complex_re, Complex.mul_re, Complex.exp_re, Complex.mul_im, mul_assoc]
    using response_closed μ W z.im hcos hz

/-- The fixed compact polynomial window has an entire real Laplace response. -/
noncomputable def response (b t : ℝ) : ℝ :=
  b * ∫ x in (0:ℝ)..1, ERH.Bump.h x * Real.exp (-t*(b*x))

theorem response_antitone {b : ℝ} (hb : 0 ≤ b) : Antitone (response b) := by
  intro t v htv
  unfold response
  apply mul_le_mul_of_nonneg_left _ hb
  have hi (z : ℝ) : IntervalIntegrable (fun x => ERH.Bump.h x * Real.exp (-z*(b*x)))
      volume 0 1 :=
    (show Continuous (fun x => ERH.Bump.h x * Real.exp (-z*(b*x))) from by
      unfold ERH.Bump.h; fun_prop).intervalIntegrable _ _
  apply intervalIntegral.integral_mono_on (by norm_num) (hi _) (hi _)
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (ERH.Bump.h_nonneg hx)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg htv) (mul_nonneg hb hx.1))

/-- If the localized disk comparison holds at a putative zero, a certified strict gain
at the trial width excludes every smaller limiting width. -/
theorem exclude_width {b w W a P G : ℝ} (hb : 0 ≤ b) (hW : 0 < W)
    (disk : response b ((w-a)/W) - P*response b (-a/W) ≤ W*G)
    (gain : W*G < response b (1-a/W) - P*response b (-a/W)) : W < w := by
  by_contra! hsmall
  have harg : (w-a)/W ≤ 1-a/W := by
    rw [← div_self hW.ne', ← sub_div]
    exact div_le_div_of_nonneg_right (sub_le_sub_right hsmall _) hW.le
  have hresp := response_antitone hb harg
  linarith

/-- The concrete quartic and its scaled cosine factor are integrable at the limiting
real argument zero, including oscillation by an arbitrary imaginary part. -/
theorem bump_modulation_integrable {b W : ℝ} (hb : 0 < b) (hW : 0 < W) (y : ℝ) :
    IntegrableOn (fun x => Real.cos (y*x)*cosineTransform (ERH.Bump.spectralLaw b) (W*x))
      (Ioi 0) := by
  let F : ℝ → ℝ := fun x => Real.cos (y*x)*ERH.Bump.h (W*x/b)
  have heq : (fun x => Real.cos (y*x)*cosineTransform (ERH.Bump.spectralLaw b) (W*x))
      =ᵐ[volume.restrict (Ioi 0)] (Icc 0 (b/W)).indicator F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
    rw [ERH.Bump.spectralLaw_cosine_explicit hb (mul_nonneg hW.le hx.le)]
    by_cases h : x ≤ b/W
    · have hl : W*x ∈ Icc 0 b :=
        ⟨mul_nonneg hW.le hx.le, by simpa [mul_comm] using (le_div_iff₀ hW).mp h⟩
      simp [F, hl, show x ∈ Icc 0 (b/W) from ⟨hx.le,h⟩]
    · have hl : W*x ∉ Icc 0 b := fun hh =>
        h ((le_div_iff₀ hW).mpr (by simpa [mul_comm] using hh.2))
      simp [F, hl, show x ∉ Icc 0 (b/W) from fun hh => h hh.2]
  have hc : Continuous F := by unfold F ERH.Bump.h; fun_prop
  have hi : Integrable ((Icc 0 (b/W)).indicator F) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (hc.continuousOn.integrableOn_compact isCompact_Icc)
  exact hi.integrableOn.congr heq.symm

theorem bump_tilted_response_nonneg {b W : ℝ} (hb : 0 < b) (hW : 0 < W)
    (y u a w : ℝ) (prior : a ≤ w) :
    0 ≤ ∫ x in Ioi (0:ℝ), Real.exp ((u+a)*x)*cosineTransform (ERH.Bump.spectralLaw b) (W*x) *
      Real.exp (-(u+w)*x)*Real.cos (y*x) := by
  let _ := ERH.Bump.spectralLaw_probability b
  exact tilted_response_nonneg _ W y u a w (bump_modulation_integrable hb hW y) prior

end ERH.TiltedWindow

#print axioms ERH.TiltedWindow.tilted_response_nonneg

#print axioms ERH.TiltedWindow.exclude_width
#print axioms ERH.TiltedWindow.bump_tilted_response_nonneg

#print axioms ERH.TiltedWindow.complex_response_nonneg
