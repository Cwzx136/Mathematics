import Research.CompactBump
import Research.SmoothedWidth

/-! Certified two-sided moment bounds for a tilted positive Euler test. -/
noncomputable section
open MeasureTheory Set
namespace ERH.TiltedGain
open ERH.Bump

def major (x : ℝ) := 1+x+x^2/2+x^3/6+x^4/24+x^5/100

theorem exp_major {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 5/6) : Real.exp x ≤ major x := by
  have dm (v : ℝ) : HasDerivAt major (major v+v^4*(1/120-v/100)) v := by
    convert horner_hasDerivAt [(1:ℝ),1,1/2,1/6,1/24,1/100] v using 1
    · funext z; dsimp [horner,major]; ring
    · dsimp [horner,derivHorner,major]; ring
  have d (v : ℝ) : HasDerivAt (fun t => Real.exp (-t)*major t)
      (Real.exp (-v)*v^4*(1/120-v/100)) v := by
    convert ((Real.hasDerivAt_exp (-v)).comp v (hasDerivAt_neg v)).mul (dm v) using 1
    · rfl
    · simp only [Function.comp_apply]; ring
  have mono : MonotoneOn (fun t => Real.exp (-t)*major t) (Icc 0 (5/6)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun v => Real.exp (-v)*v^4*(1/120-v/100))
      (convex_Icc _ _) (continuous_iff_continuousAt.mpr (fun v => (d v).continuousAt)).continuousOn
      (fun v _ => (d v).hasDerivWithinAt) (fun v hv => by
        have hh : v ∈ Icc (0:ℝ) (5/6) := interior_subset hv
        exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (hh.1) 4)) (by linarith [hh.2]))
  have h0 := mono (show (0:ℝ) ∈ Icc 0 (5/6) by constructor <;> norm_num) (show x ∈ Icc 0 (5/6) from ⟨hx,hx'⟩) hx
  have h1 : 1 ≤ Real.exp (-x)*major x := by simpa [major] using h0
  rw [Real.exp_neg,←div_eq_inv_mul] at h1
  simpa using (le_div_iff₀ (Real.exp_pos _)).mp h1

def upperMoment (b : ℝ) := 329*b^5/6829680 + 59*b^4/167160 + 3715*b^3/1365936 + 57*b^2/3184 + 423*b/4378 + 315/796

theorem major_integral (b : ℝ) :
    (∫ x in (0:ℝ)..1, h x*major (b*x)) = upperMoment b := by
  let q : List ℝ := [(0), (1), (b/2), (b^2/6 - 330/199), (b^3/24 - 495*b/398 + 105/199), (b^4/120 - 99*b^2/199 + 84*b/199 + 315/199), (b^5/600 - 55*b^3/398 + 35*b^2/199 + 525*b/398 - 483/398), (-165*b^4/5572 + 10*b^3/199 + 225*b^2/398 - 207*b/199), (-99*b^5/15920 + 35*b^4/3184 + 525*b^3/3184 - 1449*b^2/3184 + 135/796), (7*b^5/2985 + 175*b^4/4776 - 161*b^3/1194 + 30*b/199), (63*b^5/7960 - 483*b^4/15920 + 27*b^2/398 - 5/398), (-1449*b^5/218900 + 45*b^3/2189 - 25*b/2189), (15*b^4/3184 - 25*b^2/4776), (27*b^5/25870 - 25*b^3/15522), (-25*b^4/66864), (-b^5/11940)]
  have d (v : ℝ) : HasDerivAt (horner q) (h v*major (b*v)) v := by
    convert horner_hasDerivAt q v using 1
    dsimp [q,h,major,derivHorner,horner]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => d v)
      ((by unfold h major; fun_prop : Continuous (fun v => h v*major (b*v))).intervalIntegrable _ _)]
  dsimp [q,horner,upperMoment]; ring

theorem upper_laplace {k : ℝ} (hk : 0 ≤ k) (hk' : k ≤ 5/6) :
    (∫ x in (0:ℝ)..1, h x*Real.exp (k*x)) ≤ upperMoment k := by
  rw [←major_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by unfold h; fun_prop : Continuous (fun x => h x*Real.exp (k*x))).intervalIntegrable _ _)
    ((by unfold h major; fun_prop : Continuous (fun x => h x*major (k*x))).intervalIntegrable _ _)
  intro x hx
  exact mul_le_mul_of_nonneg_left (exp_major (mul_nonneg hk hx.1)
    (le_trans (by simpa using mul_le_mul_of_nonneg_left hx.2 hk) hk')) (h_nonneg hx)

def tilted (B P r : ℝ) := B*(∫ x in (0:ℝ)..1,
     h x*(Real.exp (-((B*(1-r))*x))-P*Real.exp ((B*r)*x)))

theorem lower (B P r : ℝ) (hB : 0 < B) (hp : 0 ≤ P) (hr : 0 ≤ r) (hr' : r < 1)
    (hbr : B*r ≤ 5/6) :
    B*(momentPolynomial (B*(1-r))-P*upperMoment (B*r)) ≤ tilted B P r := by
  let k := B*(1-r)
  have hk : 0 < k := mul_pos hB (sub_pos.mpr hr')
  have m := general_gain_lower k 0 hk.le
  simp only [mul_zero,sub_zero] at m
  have lo := (mul_le_mul_iff_right₀ hk).mp m
  have hi := upper_laplace (mul_nonneg hB.le hr) hbr
  have fconv : Continuous (fun x => h x*Real.exp (-(k*x))) := by unfold h; fun_prop
  have gconv : Continuous (fun x => P*(h x*Real.exp (B*r*x))) := by unfold h; fun_prop
  have heq : tilted B P r = B*((∫ x in (0:ℝ)..1, h x*Real.exp (-(k*x)))-
      P*(∫ x in (0:ℝ)..1, h x*Real.exp (B*r*x))) := by
    unfold tilted
    apply congrArg (fun v : ℝ => B*v)
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (fconv.intervalIntegrable _ _) (gconv.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [k]; ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (sub_le_sub lo (mul_le_mul_of_nonneg_left hi hp)) hB.le

#print axioms lower
end ERH.TiltedGain
