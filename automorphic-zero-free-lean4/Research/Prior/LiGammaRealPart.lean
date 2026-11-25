import Research.Prior.LiEulerGammaBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A horizontal quadrature proof of the required archimedean estimate from
Euler's finite gamma products. No special-function integral identity is assumed. -/
namespace LiGammaRealPart
open Real Set Filter Topology

private noncomputable def pt (x y : ℝ) : ℂ := ⟨x,y⟩
private noncomputable def rad (y x : ℝ) : ℝ := log (x^2+y^2)/2
private noncomputable def flux (y x : ℝ) : ℝ := x/(x^2+y^2)
private noncomputable def approx (n : ℕ) (y x : ℝ) : ℝ :=
  x*log n + log (n.factorial:ℝ) - ∑ j∈Finset.range (n+1),rad y (x+j)

private theorem rad_eq (x y : ℝ) : rad y x=log ‖pt x y‖ := by
  have h := log_pow ‖pt x y‖ 2
  rw [Complex.sq_norm,Complex.normSq_apply] at h
  unfold rad
  change log (x*x+y*y)=(2:ℝ)*log ‖pt x y‖ at h
  rw [←sq,←sq] at h; linarith

private theorem rad_deriv {x : ℝ} (y : ℝ) (hx : 0 < x) :
    HasDerivAt (rad y) (flux y x) x := by
  have hp : 0 < x^2+y^2 := by positivity
  convert (((hasDerivAt_pow 2 x).add_const (y^2)).log hp.ne').div_const 2 using 1
  · rfl
  · unfold flux; field_simp; ring

private theorem rad_mono (y : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : rad y a ≤ rad y b := by
  have h := log_le_log (show 0<a^2+y^2 by positivity) (show a^2+y^2 ≤ b^2+y^2 by
    nlinarith [mul_self_le_mul_self ha.le hab])
  unfold rad; linarith

/-- Logarithmic derivative of a vertical modulus differs between positive real
abscissas by at most the difference of their reciprocals. -/
private theorem flux_gap (y : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |flux y a-flux y b| ≤ 1/a-1/b := by
  have hb : 0 < b := ha.trans_le hab
  have A : 0 < a^2+y^2 := by positivity
  have B : 0 < b^2+y^2 := by positivity
  have hb' : a*b ≤ a^2+b^2 := by nlinarith [sq_nonneg (a-b),mul_nonneg ha.le hb.le]
  have bd : |a*b-y^2| * (a*b) ≤ (a^2+y^2)*(b^2+y^2) := by
    have e : |a*b-y^2| ≤ a*b+y^2 := abs_le.mpr ⟨by nlinarith,by nlinarith [sq_nonneg y]⟩
    nlinarith [mul_le_mul_of_nonneg_right e (mul_nonneg ha.le hb.le),
      mul_le_mul_of_nonneg_right hb' (sq_nonneg y),sq_nonneg (y^2)]
  have rat : |a*b-y^2| / ((a^2+y^2)*(b^2+y^2)) ≤ 1/(a*b) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have eq : flux y a-flux y b=(b-a)*(a*b-y^2)/((a^2+y^2)*(b^2+y^2)) := by
    unfold flux; field_simp; ring
  rw [eq,abs_div,abs_mul, abs_of_nonneg (sub_nonneg.mpr hab),abs_of_pos (mul_pos A B)]
  have r := mul_le_mul_of_nonneg_left rat (sub_nonneg.mpr hab)
  convert r using 1 <;> field_simp

private theorem quadrature_one (y : ℝ) {x : ℝ} (hx : 0 < x) :
    |flux y x-(rad y (x+1)-rad y x)| ≤ 1/x-1/(x+1) := by
  obtain ⟨b,hb,he⟩ := exists_deriv_eq_slope (rad y) (show x<x+1 by linarith)
    (fun t ht => (rad_deriv y (hx.trans_le ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => (rad_deriv y (hx.trans ht.1)).differentiableAt.differentiableWithinAt)
  rw [(rad_deriv y (hx.trans hb.1)).deriv] at he
  have r := flux_gap y hx hb.1.le
  rw [he,show x+1-x=1 by ring,div_one] at r
  refine r.trans (sub_le_sub_left ?_ _)
  exact div_le_div_of_nonneg_left zero_le_one (hx.trans hb.1) hb.2.le

private theorem quadrature (y : ℝ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    |(∑ j∈Finset.range n,flux y (x+j))-(rad y (x+n)-rad y x)| ≤ 1/x-1/(x+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := quadrature_one y (show 0 < x+(n:ℝ) by positivity)
    simp only [Finset.sum_range_succ,Nat.cast_succ]
    have tr := abs_add_le ((∑ j∈Finset.range n,flux y (x+j))-(rad y (x+n)-rad y x))
      (flux y (x+n)-(rad y (x+n+1)-rad y (x+n)))
    rw [add_assoc x (n:ℝ) 1] at h tr
    convert tr.trans (add_le_add ih h) using 1 <;> congr 1 <;> ring

private theorem approx_deriv (n : ℕ) (y : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (approx n y) (log (n:ℝ) - ∑ j∈Finset.range (n+1),flux y (x+j)) x := by
  have h (j : ℕ) : HasDerivAt (fun t=>rad y (t+j)) (flux y (x+j)) x := by
    simpa [Function.comp_def] using (rad_deriv y (show 0<x+(j:ℝ) by positivity)).comp x ((hasDerivAt_id x).add_const (j:ℝ))
  unfold approx
  exact (by simpa [Pi.sub_def] using (((hasDerivAt_id x).mul_const (log (n:ℝ))).add_const
    (log (n.factorial:ℝ))).sub (HasDerivAt.fun_sum (u:=Finset.range (n+1)) (fun j _ => h j)))

private theorem approx_val {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    approx n y x = log ‖Complex.GammaSeq (pt x y) n‖ := by
  have np : (0:ℝ)<n := by exact_mod_cast hn
  have fac : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have id (j : ℕ) : pt x y+(j:ℂ)=pt (x+j) y := by apply Complex.ext <;> simp [pt]
  have nonz (j : ℕ) : pt (x+j) y ≠ 0 := by
    intro z
    have h : x+(j:ℝ)=0 := congrArg Complex.re z
    linarith [Nat.cast_nonneg (α:=ℝ) j]
  simp only [Complex.GammaSeq,norm_div,norm_mul,norm_prod,Complex.norm_natCast,id]
  rw [show (n:ℂ)=((n:ℝ):ℂ) by simp,Complex.norm_cpow_eq_rpow_re_of_pos np]
  rw [log_div (ne_of_gt (mul_pos (rpow_pos_of_pos np _) fac))
    (Finset.prod_ne_zero_iff.mpr (fun j _ => norm_ne_zero_iff.mpr (nonz j))),
    log_mul (rpow_pos_of_pos np _).ne' fac.ne',log_rpow np,
    log_prod (fun j _ => norm_ne_zero_iff.mpr (nonz j))]
  simp only [approx,rad_eq,pt]

private theorem approx_limit (y : ℝ) {x : ℝ} (hx : 0<x) :
    Tendsto (fun n:ℕ=>approx n y x) atTop (𝓝 (log ‖Complex.Gamma (pt x y)‖)) := by
  have gz := Complex.Gamma_ne_zero_of_re_pos (show 0<(pt x y).re from hx)
  have h := ((Complex.GammaSeq_tendsto_Gamma (pt x y)).norm).log (norm_ne_zero_iff.mpr gz)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (approx_val hn hx y).symm

/-- The chord bounds pass to the actual gamma function by pointwise convergence
of Euler's product, requiring no interchange of a limit and a derivative. -/
private theorem chord (y : ℝ) {a b : ℝ} (ha : 0<a) (hab : a<b) :
    rad y a-1/a ≤ (log ‖Complex.Gamma (pt b y)‖-log ‖Complex.Gamma (pt a y)‖)/(b-a) ∧
    (log ‖Complex.Gamma (pt b y)‖-log ‖Complex.Gamma (pt a y)‖)/(b-a) ≤ rad y b+1/a := by
  have bp : 0 < b := ha.trans hab
  let slopeN (n : ℕ) := (approx n y b-approx n y a)/(b-a)
  have finite (n : ℕ) (hn : 0<n) :
      rad y a-1/a-(b+1+|y|)/(n:ℝ) ≤ slopeN n ∧ slopeN n ≤ rad y b+1/a := by
    obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope (approx n y) hab
      (fun t ht => (approx_deriv n y (ha.trans_le ht.1)).continuousAt.continuousWithinAt)
      (fun t ht => (approx_deriv n y (ha.trans ht.1)).differentiableAt.differentiableWithinAt)
    have cp := ha.trans hc.1
    rw [(approx_deriv n y cp).deriv] at he
    have quad := abs_le.mp (quadrature y cp (n+1))
    have np : 0 < (n:ℝ) := by exact_mod_cast hn
    let u : ℝ := c+(n+1:ℕ)
    have ueq : u=c+(n:ℝ)+1 := by dsimp [u]; push_cast; ring
    have up : 0<u := by rw [ueq]; linarith
    have low : log n ≤ rad y u := by
      rw [rad_eq]
      apply log_le_log np
      exact (show (n:ℝ) ≤ (pt u y).re by change (n:ℝ)≤u; rw [ueq]; linarith).trans (Complex.re_le_norm _)
    have upb : rad y u ≤ log n+(b+1+|y|)/(n:ℝ) := by
      rw [rad_eq]
      have nonz : pt u y ≠ 0 := fun h => up.ne' (congrArg Complex.re h)
      have h := log_le_sub_one_of_pos (div_pos (norm_pos_iff.mpr nonz) np)
      rw [log_div (norm_ne_zero_iff.mpr nonz) np.ne'] at h
      have bound := Complex.norm_le_abs_re_add_abs_im (pt u y)
      change ‖pt u y‖ ≤ |u|+|y| at bound
      rw [abs_of_pos up] at bound
      have con : ‖pt u y‖/(n:ℝ) ≤ 1+(b+1+|y|)/(n:ℝ) := by
        rw [div_le_iff₀ np,add_mul,div_mul_cancel₀ _ np.ne',one_mul]
        linarith [hc.2]
      linarith
    have inv : 1/c ≤ 1/a := div_le_div_of_nonneg_left zero_le_one ha hc.1.le
    have nn : 0 ≤ 1/u := by positivity
    change -(1/c-1/u) ≤ _ ∧ _ ≤ 1/c-1/u at quad
    change rad y a-1/a-(b+1+|y|)/(n:ℝ) ≤ _ ∧ _ ≤ rad y b+1/a
    dsimp only [slopeN]
    change log (n:ℝ)-_=(approx n y b-approx n y a)/(b-a) at he
    constructor <;> linarith [quad.1,quad.2,rad_mono y ha hc.1.le,rad_mono y cp hc.2.le]
  have conv : Tendsto slopeN atTop (𝓝 ((log ‖Complex.Gamma (pt b y)‖-log ‖Complex.Gamma (pt a y)‖)/(b-a))) :=
    ((approx_limit y bp).sub (approx_limit y ha)).div_const _
  have delta : Tendsto (fun n:ℕ=>(b+1+|y|)/(n:ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have low := le_of_tendsto_of_tendsto (tendsto_const_nhds.sub delta) conv
    ((eventually_gt_atTop 0).mono (fun n hn => (finite n hn).1))
  have high := le_of_tendsto conv ((eventually_gt_atTop 0).mono (fun n hn => (finite n hn).2))
  exact ⟨by simpa using low,high⟩

private theorem gamma_logabs_deriv (y : ℝ) {a : ℝ} (ha : 0<a) :
    HasDerivAt (fun x:ℝ=>log ‖Complex.Gamma (pt x y)‖) (Complex.digamma (pt a y)).re a := by
  let z := pt a y
  have zg : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  have gz := Complex.differentiableAt_Gamma z (fun n h => by
    have hh := congrArg Complex.re h
    change a=(-(n:ℂ)).re at hh
    simp at hh
    linarith [Nat.cast_nonneg (α:=ℝ) n])
  have lin : HasDerivAt (fun w:ℂ=>w+(y:ℂ)*Complex.I) 1 (a:ℂ) := (hasDerivAt_id _).add_const _
  have ez : (a:ℂ)+(y:ℂ)*Complex.I=z := by apply Complex.ext <;> simp [z,pt]
  have gg : HasDerivAt (fun x:ℝ=>Complex.Gamma (pt x y)) (deriv Complex.Gamma z) a := by
    have shifted := gz.hasDerivAt
    rw [←ez] at shifted
    convert (shifted.comp (h := fun w:ℂ=>w+(y:ℂ)*Complex.I) (a:ℂ) lin).comp_ofReal using 1
    · funext x; congr 1; apply Complex.ext <;> simp [pt]
    · rw [mul_one,ez]
  have h := ((hasDerivAt_log (pow_ne_zero 2 (norm_ne_zero_iff.mpr zg))).comp a gg.norm_sq).div_const 2
  simp only [Function.comp_def,log_pow,Nat.cast_ofNat] at h
  convert h using 1
  · funext x; ring
  · rw [Complex.digamma_def,logDeriv_apply,Complex.inner,Complex.div_re,Complex.sq_norm]
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
    change _ = _
    dsimp only [z] at *
    field_simp
    ring

/-- The actual real digamma differs from the logarithmic modulus by at most the
reciprocal real part throughout the open right half-plane. -/
theorem real_digamma {z : ℂ} (hz : 0 < z.re) :
    |(Complex.digamma z).re-log ‖z‖| ≤ 1/z.re := by
  obtain ⟨a,y⟩ := z
  change 0<a at hz
  let G : ℝ→ℝ := fun x => log ‖Complex.Gamma (pt x y)‖
  have d : HasDerivAt G (Complex.digamma (pt a y)).re a := gamma_logabs_deriv y hz
  have sl := (hasDerivAt_iff_tendsto_slope_left_right.mp d).2
  have cont := (rad_deriv y hz).continuousAt
  have l := ge_of_tendsto sl
    (show ∀ᶠ b in 𝓝[>] a,rad y a-1/a ≤ slope G a b from by
      filter_upwards [self_mem_nhdsWithin] with b hb
      simpa [slope_def_field,G] using (chord y hz hb).1)
  have u := le_of_tendsto_of_tendsto sl ((cont.tendsto.mono_left nhdsWithin_le_nhds).add_const (1/a))
    (show ∀ᶠ b in 𝓝[>] a,slope G a b ≤ rad y b+1/a from by
      filter_upwards [self_mem_nhdsWithin] with b hb
      simpa [slope_def_field,G] using (chord y hz hb).2)
  rw [rad_eq] at l u
  change |(Complex.digamma (pt a y)).re-log ‖pt a y‖| ≤ 1/a
  rw [abs_le]; constructor <;> linarith

#print axioms flux_gap
#print axioms quadrature
#print axioms approx_limit
#print axioms chord
#print axioms real_digamma

end LiGammaRealPart
