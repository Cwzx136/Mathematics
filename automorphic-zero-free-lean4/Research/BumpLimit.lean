import Research.BumpSpectral

/-! Exact removal of the positive regulator from the two averaged kernels. -/

open MeasureTheory Set Filter
open scoped Topology
namespace ERH.Bump
open ERH.AveragedKernel

/-- The averaged Poisson kernel with the explicit probability law. -/
noncomputable def poleAverage (b t : ℝ) : ℝ :=
  ∫ z, t / (t^2 + z^2) ∂spectralLaw b

theorem poleAverage_exact {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    poleAverage b t = b * ∫ u in (0 : ℝ)..1, h u * Real.exp (-t * (b*u)) := by
  let _ := spectralLaw_probability b
  rw [poleAverage, poisson_average _ ht]
  let F : ℝ → ℝ := fun x => Real.exp (-t * x) * h (x/b)
  calc
    _ = ∫ x in Ioi (0 : ℝ), (Icc (0 : ℝ) b).indicator F x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [spectralLaw_cosine_explicit hb hx.le]
      by_cases hx' : x ∈ Icc (0 : ℝ) b <;> simp [F, hx']
    _ = ∫ x in Ioi (0 : ℝ) ∩ Icc (0 : ℝ) b, F x := setIntegral_indicator measurableSet_Icc
    _ = ∫ x in (0 : ℝ)..b, F x := by
      rw [intervalIntegral.integral_of_le hb.le]
      have heq : Ioi (0 : ℝ) ∩ Icc (0 : ℝ) b = Ioc (0:ℝ) b := by
        ext x
        constructor
        · exact fun hh => ⟨hh.1,hh.2.2⟩
        · exact fun hh => ⟨hh.1,hh.1.le,hh.2⟩
      rw [heq]
    _ = _ := by
      let G : ℝ → ℝ := fun u => h u * Real.exp (-t * (b*u))
      have hG (x : ℝ) : F x = G (x/b) := by
        simp [F, G, mul_div_cancel₀ _ hb.ne', mul_comm]
      simp_rw [hG]
      rw [intervalIntegral.integral_comp_div _ hb.ne']
      simp [hb.ne', G]

/-- The exact limiting gain of this positive averaging test, at any physical scale
`b > 0` and for any real pole coefficient. -/
theorem poleAverage_boundary {b : ℝ} (hb : 0 < b) (p : ℝ) :
    Tendsto (fun t => poleAverage b (1+t) - p * poleAverage b t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (b * ∫ u in (0 : ℝ)..1, h u * (Real.exp (-(b*u)) - p))) := by
  let J : ℝ → ℝ := fun t => b * ∫ u in (0 : ℝ)..1, h u * Real.exp (-t * (b*u))
  have hc : Continuous J := by
    apply continuous_const.mul
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    unfold Function.uncurry h
    fun_prop
  have hJ : Tendsto (fun t => J (1+t) - p * J t) (𝓝[>] (0 : ℝ)) (𝓝 (J 1 - p * J 0)) := by
    have hc2 : Continuous (fun t : ℝ => J (1+t) - p * J t) := by fun_prop
    simpa only [add_zero] using (hc2.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hlim : J 1 - p * J 0 = b * ∫ u in (0 : ℝ)..1, h u * (Real.exp (-(b*u)) - p) := by
    have h1 : IntervalIntegrable (fun u => h u * Real.exp (-(b*u))) volume 0 1 :=
      (show Continuous (fun u => h u * Real.exp (-(b*u))) from by unfold h; fun_prop).intervalIntegrable _ _
    have h2 : IntervalIntegrable h volume 0 1 :=
      (show Continuous h from by unfold h; fun_prop).intervalIntegrable _ _
    simp only [J, neg_one_mul, neg_zero, zero_mul, Real.exp_zero, mul_one]
    simp_rw [mul_sub, intervalIntegral.integral_sub h1 (h2.mul_const p),
      intervalIntegral.integral_mul_const]
    ring
  rw [← hlim]
  apply hJ.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [poleAverage_exact hb (by linarith : 0 < 1+t), poleAverage_exact hb ht]

end ERH.Bump

#print axioms ERH.Bump.poleAverage_exact
#print axioms ERH.Bump.poleAverage_boundary
