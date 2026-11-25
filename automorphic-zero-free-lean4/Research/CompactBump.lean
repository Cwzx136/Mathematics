import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Exact compact autocorrelation and a ninth-order Taylor minorant.
All integrals in this module use the real Lebesgue measure. -/
noncomputable section
open MeasureTheory Set
namespace ERH.Bump

def horner : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: q, x => a+x*horner q x

def derivHorner : List ℝ → ℝ → ℝ
  | [], _ => 0
  | _ :: q, x => horner q x + x*derivHorner q x

theorem horner_hasDerivAt (q : List ℝ) (x : ℝ) :
    HasDerivAt (horner q) (derivHorner q x) x := by
  induction q with
  | nil => exact hasDerivAt_const x 0
  | cons a q ih =>
    convert (hasDerivAt_const x a).add ((hasDerivAt_id x).mul ih) using 1 <;>
      simp [horner,derivHorner] <;> rfl

def f (v : ℝ) := v*(1-v)*(1+5/2*v*(1-v))
def g := (Icc (0:ℝ) 1).indicator f
def h (x : ℝ) := (1-x)^3*(25*x^6+75*x^5-120*x^4-560*x^3+204*x^2+597*x+199)/199
def B : ℝ := 13/8

theorem f_nonneg {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : 0 ≤ f v := by
  unfold f
  have h1 : 0 ≤ 1-v := sub_nonneg.mpr hv.2
  have h0 := hv.1
  positivity

theorem overlap (x : ℝ) :
    (∫ v in (0:ℝ)..1-x, f v * f (v+x)) = (199/2520)*h x := by
  let q : List ℝ := [(0), (0), (5*x^4/4 - 5*x^3/2 + 3*x^2/4 + x/2), (5*x^4/4 + 5*x^3/6 - 17*x^2/4 + 3*x/2 + 1/3), (-25*x^4/8 + 10*x^3 - 15*x^2/4 - 31*x/8 + 3/4), (5*x^4/4 - 25*x^3/2 + 81*x^2/4 - 5*x - 31/20), (25*x^3/6 - 75*x^2/4 + 65*x/4 - 5/3), (75*x^2/14 - 25*x/2 + 65/14), (25*x/8 - 25/8), (25/36)]
  have diff (v : ℝ) : HasDerivAt (horner q) (f v*f (v+x)) v := by
    convert horner_hasDerivAt q v using 1
    dsimp [f,derivHorner,horner,q]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => diff v)
       ((by unfold f; fun_prop : Continuous (fun v => f v * f (v+x))).intervalIntegrable _ _)]
  dsimp [horner,q,h]; ring

theorem h_nonneg {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : 0 ≤ h x := by
  have hr : 0 ≤ 1-x := sub_nonneg.mpr hx.2
  have hn := intervalIntegral.integral_nonneg (μ := volume) (f := fun v => f v * f (v+x)) hr
    (fun v hv => mul_nonneg (f_nonneg ⟨hv.1, by linarith [hv.2,hx.1]⟩)
                            (f_nonneg ⟨by linarith [hv.1,hx.1],by linarith [hv.2]⟩))
  rw [overlap] at hn
  linarith

/-- Identify the whole-line correlation of the compact bump with its real polynomial
on the interval where the two supports intersect. -/
theorem correlation {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    (∫ v : ℝ, g v*g (v+x)) = (199/2520)*h x := by
  have hi : (fun v : ℝ => g v*g (v+x)) =
      (Icc 0 (1-x)).indicator (fun v => f v*f (v+x)) := by
    funext v
    by_cases hmem : v ∈ Icc 0 (1-x)
    · have hv : v ∈ Icc 0 1 := ⟨hmem.1,by linarith [hmem.2,hx.1]⟩
      have hvx : v+x ∈ Icc 0 1 := ⟨by linarith [hmem.1,hx.1],by linarith [hmem.2]⟩
      simp [g,hmem,hv,hvx]
    · by_cases hv : v ∈ Icc 0 1
      · have hvx : v+x ∉ Icc 0 1 := fun h => hmem ⟨hv.1,by linarith [h.2]⟩
        simp [g,hv,hvx,hmem]
      · simp [g,hv,hmem]
  change (∫ v, (fun v : ℝ => g v*g (v+x)) v) = _
  rw [hi, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
       ←intervalIntegral.integral_of_le (sub_nonneg.mpr hx.2),overlap]

def taylor9 (v : ℝ) := horner [(1), (-1), (1/2), (-1/6), (1/24), (-1/120), (1/720), (-1/5040), (1/40320), (-1/362880)] v

theorem taylor9_le {x : ℝ} (hx : 0 ≤ x) : taylor9 x ≤ Real.exp (-x) := by
  have dT (v : ℝ) : HasDerivAt taylor9 (-(v^9)/362880 - taylor9 v) v := by
    unfold taylor9
    convert horner_hasDerivAt _ v using 1
    dsimp [derivHorner,horner]; ring
  have deriv (v : ℝ) : HasDerivAt (fun t => Real.exp t*taylor9 t)
      (-(Real.exp v * v^9)/362880) v := by
    convert (Real.hasDerivAt_exp v).mul (dT v) using 1
    ring
  have mono : AntitoneOn (fun t => Real.exp t*taylor9 t) (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun v => -(Real.exp v * v^9)/362880)
      (convex_Ici _) ((continuous_iff_continuousAt.mpr fun v => (deriv v).continuousAt).continuousOn)
      (fun v _ => (deriv v).hasDerivWithinAt) (fun v hv => by
        have h0 : 0 ≤ v := interior_subset hv
        have := mul_nonneg (Real.exp_pos v).le (pow_nonneg h0 9)
        linarith)
  have h' := mono (show (0:ℝ) ∈ Ici (0:ℝ) from (le_rfl : (0:ℝ) ≤ 0)) (show x ∈ Ici 0 from hx) hx
  have hh : Real.exp x * taylor9 x ≤ 1 := by simpa [taylor9,horner] using h'
  rw [Real.exp_neg, ←one_div]
  exact (le_div_iff₀ (Real.exp_pos _)).2 (by linarith [mul_comm (Real.exp x) (taylor9 x)])

def momentPolynomial (b : ℝ) := -271*b^9/112304774400 + 47*b^8/1502032896 - 347*b^7/928836480 + 719*b^6/176520960 - 329*b^5/8195616 + 59*b^4/167160 - 3715*b^3/1365936 + 57*b^2/3184 - 423*b/4378 + 315/796

/-- A fully rational lower bound on the integral used by the positive averaging test. -/
theorem general_gain_lower (b p : ℝ) (hb : 0 ≤ b) :
    b*(momentPolynomial b-(315/796)*p) ≤
     b*(∫ x in (0:ℝ)..1, h x*(Real.exp (-(b*x))-p)) := by
  let q : List ℝ := [(0), (1 - p), (-b/2), (b^2/6 + 330*p/199 - 330/199), (-b^3/24 + 495*b/398 - 105*p/199 + 105/199), (b^4/120 - 99*b^2/199 - 84*b/199 - 315*p/199 + 315/199), (-b^5/720 + 55*b^3/398 + 35*b^2/199 - 525*b/398 + 483*p/398 - 483/398), (b^6/5040 - 165*b^4/5572 - 10*b^3/199 + 225*b^2/398 + 207*b/199), (-b^7/40320 + 33*b^5/6368 + 35*b^4/3184 - 525*b^3/3184 - 1449*b^2/3184 - 135*p/796 + 135/796), (b^8/362880 - 11*b^6/14328 - 7*b^5/3582 + 175*b^4/4776 + 161*b^3/1194 - 30*b/199), (-b^9/3628800 + 11*b^7/111440 + 7*b^6/23880 - 21*b^5/3184 - 483*b^4/15920 + 27*b^2/398 + 5*p/398 - 5/398), (-b^8/89152 - b^7/26268 + 35*b^6/35024 + 483*b^5/87560 - 45*b^3/2189 + 25*b/2189), (11*b^9/9628416 + b^8/229248 - 5*b^7/38208 - 161*b^6/191040 + 15*b^4/3184 - 25*b^2/4776), (-b^9/2235168 + 5*b^8/331136 + 23*b^7/206960 - 9*b^5/10348 + 25*b^3/15522), (-5*b^9/3209472 - 23*b^8/1783040 + 3*b^6/22288 - 25*b^4/66864), (23*b^9/17193600 - b^7/55720 + b^5/14328), (3*b^8/1426432 - 5*b^6/458496), (-b^9/4546752 + 5*b^7/3410064), (-5*b^8/28885248), (5*b^9/274409856)]
  have diff (x : ℝ) : HasDerivAt (horner q) (h x*(taylor9 (b*x)-p)) x := by
    convert horner_hasDerivAt q x using 1
    dsimp [q,h,taylor9,derivHorner,horner]; ring
  have cont : Continuous (fun x => h x*(taylor9 (b*x)-p)) := by
    unfold h taylor9; dsimp [horner]; fun_prop
  have J := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
        (fun x _ => diff x) (cont.intervalIntegrable _ _)
  have V : horner q 1-horner q 0 = momentPolynomial b-(315/796)*p := by
    dsimp [q,horner,momentPolynomial]; ring
  apply mul_le_mul_of_nonneg_left _ hb
  rw [←V,←J]
  apply intervalIntegral.integral_mono_on (by norm_num) (cont.intervalIntegrable _ _)
     ((by unfold h; fun_prop : Continuous (fun x => h x*(Real.exp (-(b*x))-p))).intervalIntegrable _ _)
  intro x hx
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (taylor9_le (mul_nonneg hb hx.1)) p) (h_nonneg hx)


theorem gain_lower (p : ℝ) :
    B*(95181399549361514143/344366740312739020800-(315/796)*p) ≤
     B*(∫ x in (0:ℝ)..1, h x*(Real.exp (-(B*x))-p)) := by
  have M : momentPolynomial B = 95181399549361514143/344366740312739020800 := by norm_num [momentPolynomial,B]
  simpa only [M] using general_gain_lower B p (by norm_num [B])

#print axioms correlation
#print axioms gain_lower
end ERH.Bump
