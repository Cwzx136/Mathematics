import Research.SpectralWindow
import Research.AveragedKernel
import Research.CompactBump

/-! The spectral law for the polynomial window used in the arithmetic bound. -/

open Set MeasureTheory
namespace ERH.Bump
open ERH.SpectralWindow ERH.AveragedKernel

theorem g_continuous : Continuous g := by
  apply continuous_indicator
  · intro x hx
    rw [frontier_Icc (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rcases hx with h | h
    · subst x
      norm_num [f]
    · have : x = 1 := h
      subst x
      norm_num [f]
  · exact (show Continuous f from by unfold f; fun_prop).continuousOn

theorem g_compactSupport : HasCompactSupport g :=
  HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc
    (fun _ hx => indicator_of_notMem hx _)

theorem g_nonnegative (x : ℝ) : 0 ≤ g x := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · simpa [g, hx] using f_nonneg hx
  · simp [g, hx]

theorem autocorrelation_polynomial {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    autocorrelation g x = (199/2520) * h x := by
  rw [autocorrelation_apply]
  have H := integral_add_right_eq_self (fun v : ℝ => g v * g (v - x)) x (μ := volume)
  simpa [mul_comm] using H.symm.trans (by simpa [mul_comm] using correlation hx)

theorem autocorrelation_origin : autocorrelation g 0 = 199/2520 := by
  rw [autocorrelation_polynomial (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)]
  norm_num [h]

theorem autocorrelation_vanish {x : ℝ} (hx : 1 < x) : autocorrelation g x = 0 := by
  rw [autocorrelation_apply]
  have Hz (v : ℝ) : g v * g (v - x) = 0 := by
    by_cases hv : v ∈ Icc (0 : ℝ) 1
    · have ho : v - x ∉ Icc (0 : ℝ) 1 := fun hmem => (by linarith [hmem.1, hv.2])
      simp [g, ho]
    · simp [g, hv]
  simp [Hz]

/-- The dilated angular law giving the window `x ↦ h(x/b)` on the positive half-line. -/
noncomputable def spectralLaw (b : ℝ) : Measure ℝ :=
  (angularLaw g).map (fun z : ℝ => z / b)

theorem spectralLaw_probability (b : ℝ) : IsProbabilityMeasure (spectralLaw b) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 <|
    angularLaw_probability g_continuous g_compactSupport (autocorrelation_origin ▸ by norm_num)

theorem spectralLaw_cosine (b : ℝ) (x : ℝ) :
    cosineTransform (spectralLaw b) x = autocorrelation g (x/b) / (199/2520) := by
  unfold cosineTransform spectralLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hh (v : ℝ) : (v / b) * x = v * (x / b) := by ring
  simp only [hh]
  rw [angularLaw_cosine g_continuous g_compactSupport (autocorrelation_origin ▸ by norm_num),
    autocorrelation_origin]

theorem spectralLaw_cosine_explicit {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    cosineTransform (spectralLaw b) x = (Icc (0 : ℝ) b).indicator (fun y => h (y/b)) x := by
  rw [spectralLaw_cosine]
  by_cases hx' : x ≤ b
  · rw [autocorrelation_polynomial ⟨div_nonneg hx hb.le, (div_le_one hb).mpr hx'⟩,
      indicator_of_mem (show x ∈ Icc 0 b from ⟨hx, hx'⟩)]
    ring
  · rw [autocorrelation_vanish ((one_lt_div hb).mpr (lt_of_not_ge hx')),
      indicator_of_notMem (show x ∉ Icc 0 b from fun hh => hx' hh.2), zero_div]

end ERH.Bump

#print axioms ERH.Bump.spectralLaw_probability
#print axioms ERH.Bump.spectralLaw_cosine_explicit
