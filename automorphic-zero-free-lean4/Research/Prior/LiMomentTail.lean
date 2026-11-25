import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Summation of the even high-zero moments before taking a maximum.
The displayed moment hypothesis is the output of the unit-interval/integral comparison.
It applies to arbitrary index types and does not assume the desired tail is summable. -/
namespace LiMomentIntegral
open Real Set

/-- Bound a truncated logarithmic Dirichlet tail on the grid starting at `y+1`.
Here `r` is one less than the exponent of the decaying density. -/
theorem grid {y H d : ℝ} (hy : 0 < y) (hd : 0 ≤ d) (hH : d ≤ H)
    (q K : ℕ) :
    (∑ j ∈ Finset.range K, (H+d*(log (y+j+1)-log y+log 2))/(y+j+1)^(q+2)) ≤
      ((H+d*log 2)/((q:ℝ)+1)+d/((q:ℝ)+1)^2)/y^(q+1) := by
  let r : ℝ := (q:ℝ)+1
  have hr : 0 < r := by dsimp [r]; positivity
  let A : ℝ → ℝ := fun t => H+d*(log t-log y+log 2)
  let G : ℝ → ℝ := fun t => A t/t^(q+2)
  let F : ℝ → ℝ := fun t => (A t/r+d/r^2)/t^(q+1)
  have dA {t : ℝ} (ht : 0 < t) : HasDerivAt A (d/t) t := by
    convert ((((hasDerivAt_log ht.ne').sub_const (log y)).add_const (log 2)).const_mul d).const_add H using 1; rfl
  have apos {t : ℝ} (ht : y ≤ t) : d ≤ A t := by
    dsimp [A]
    have ht' := log_le_log hy ht
    nlinarith [mul_nonneg hd (show 0 ≤ log t-log y+log 2 by linarith [log_nonneg (by norm_num : (1:ℝ) ≤ 2)])]
  have dF {t : ℝ} (ht : 0 < t) : HasDerivAt F (-(G t)) t := by
    convert ((((dA ht).div_const r).add_const (d/r^2)).div (hasDerivAt_pow (q+1) t) (by positivity)) using 1
    dsimp [G,r]
    push_cast
    simp only [pow_succ]
    field_simp
    ring
  have dG {t : ℝ} (ht : 0 < t) : HasDerivAt G ((d-((q:ℝ)+2)*A t)/t^(q+3)) t := by
    convert (dA ht).div (hasDerivAt_pow (q+2) t) (by positivity) using 1
    push_cast
    simp only [pow_succ]
    field_simp
  have ga : AntitoneOn G (Ici y) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici y)
    · intro t ht; exact (dG (hy.trans_le ht)).continuousAt.continuousWithinAt
    · intro t ht
      have h := interior_subset ht
      exact (dG (hy.trans_le h)).differentiableAt.differentiableWithinAt
    · intro t ht
      have h : y ≤ t := interior_subset ht
      rw [(dG (hy.trans_le h)).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (pow_nonneg (hy.le.trans h) _)
      have a := apos h
      nlinarith [mul_nonneg hr.le (hd.trans a)]
  have step (s : ℝ) (hs : y ≤ s) : G (s+1) ≤ F s-F (s+1) := by
    have cont : ContinuousOn F (Icc s (s+1)) := fun t ht => (dF (hy.trans_le (hs.trans ht.1))).continuousAt.continuousWithinAt
    have diff : DifferentiableOn ℝ F (Ioo s (s+1)) := fun t ht => (dF (hy.trans_le (hs.trans ht.1.le))).differentiableAt.differentiableWithinAt
    obtain ⟨c,hc,hder⟩ := exists_deriv_eq_slope F (show s < s+1 by linarith) cont diff
    rw [(dF (hy.trans_le (hs.trans hc.1.le))).deriv] at hder
    have decrease := ga (hs.trans hc.1.le) (show y ≤ s+1 by linarith) hc.2.le
    rw [show s+1-s=1 by ring, div_one] at hder
    linarith
  have segment (n : ℕ) : (∑ j ∈ Finset.range n,G (y+j+1)) ≤ F y-F (y+n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ, ←add_assoc]
      linarith [step (y+n) (by simp)]
  have endpos : 0 ≤ F (y+K) := by
    have hA : 0 ≤ A (y+K) := hd.trans (apos (by simp))
    dsimp [F]; positivity
  simpa [G,F,A,r] using (segment K).trans (sub_le_self _ endpos)

end LiMomentIntegral

namespace LiMomentTail
open Real

private theorem cosh_tail (v : ℝ) :
    HasSum (fun k : ℕ => v^(2*(k+1))/(Nat.factorial (2*(k+1)) : ℝ)) (cosh v-1) := by
  simpa using (hasSum_nat_add_iff' 1).mpr (hasSum_cosh v)

private theorem sinh_tail {a : ℝ} (ha : 0 < a) :
    HasSum (fun k : ℕ => a^(2*(k+1))/(Nat.factorial (2*(k+1)+1) : ℝ)) (sinh a/a-1) := by
  have h : HasSum (fun k : ℕ => a^(2*k)/(Nat.factorial (2*k+1) : ℝ)) (sinh a/a) := by
    convert (hasSum_sinh a).div_const a using 1
    ext k
    rw [pow_succ]
    field_simp
  simpa using (hasSum_nat_add_iff' 1).mpr h

/-- A uniform bound on the even moments of all finite subcollections, with the
integral denominator `4(k+1)-1 = 4k+3`, implies the hyperbolic-sine tail bound. -/
theorem bound {ι : Type*} (v : ι → ℝ) {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (mom : ∀ (s : Finset ι) (k : ℕ),
       ∑ i ∈ s, (v i)^(2*(k+1)) ≤ C*a^(2*(k+1))/(4*(k:ℝ)+3)) :
    Summable (fun i => cosh (v i)-1) ∧
    (∑' i : ι, (cosh (v i)-1)) ≤ C*(sinh a/a-1) := by
  have cpos : ∀ i, 0 ≤ cosh (v i)-1 := fun i => sub_nonneg.mpr (one_le_cosh (v i))
  have major (s : Finset ι) : ∑ i ∈ s, (cosh (v i)-1) ≤ C*(sinh a/a-1) := by
    have left := hasSum_sum (s := s) (fun i _ => cosh_tail (v i))
    have right := (sinh_tail ha).mul_left C
    rw [←left.tsum_eq, ←right.tsum_eq]
    apply left.summable.tsum_le_tsum _ right.summable
    intro k
    change (∑ i ∈ s, (v i)^(2*(k+1))/(Nat.factorial (2*(k+1)) : ℝ)) ≤ _
    rw [←Finset.sum_div]
    let j := 2*(k+1)
    have hj : (j:ℝ)+1 ≤ 4*(k:ℝ)+3 := by dsimp [j]; push_cast; linarith
    have h0 : 0 < (j:ℝ)+1 := by positivity
    have hf : 0 < (Nat.factorial j : ℝ) := by positivity
    have hm : (∑ i ∈ s, (v i)^j) ≤ C*a^j/((j:ℝ)+1) :=
      (mom s k).trans (div_le_div_of_nonneg_left (mul_nonneg hC (pow_nonneg ha.le _)) h0 hj)
    change (∑ i ∈ s, (v i)^j)/(Nat.factorial j : ℝ) ≤ C*(a^j/(Nat.factorial (j+1) : ℝ))
    calc
      _ ≤ (C*a^j/((j:ℝ)+1))/(Nat.factorial j : ℝ) := div_le_div_of_nonneg_right hm hf.le
      _ = _ := by
        have fact : (Nat.factorial (j+1) : ℝ) = ((j:ℝ)+1)*(Nat.factorial j : ℝ) := by
          exact_mod_cast Nat.factorial_succ j
        rw [fact, div_div, mul_div_assoc]
  exact ⟨summable_of_sum_le cpos major, Real.tsum_le_of_sum_le cpos major⟩

/-- A logarithmic bound on the number of high zeros in each unit interval,
together with the pointwise log-modulus bound, implies the full infinite tail estimate. -/
theorem unit_bins {ι : Type*} (v : ι → ℝ) (bin : ι → ℕ)
    {y H d a : ℝ} (hy : 0 < y) (hd : 0 ≤ d) (hH : d ≤ H) (ha : 0 < a)
    (count : ∀ (s : Finset ι) (j : ℕ),
       ((s.filter (fun i => bin i=j)).card : ℝ) ≤ 8*(H+d*(log (y+j+1)-log y+log 2)))
    (weight : ∀ i, |v i| ≤ a*y^2/(y+(bin i:ℝ)+1)^2) :
    Summable (fun i => cosh (v i)-1) ∧
    (∑' i : ι, (cosh (v i)-1)) ≤ 8*y*(H+d*(log 2+1/3))*(sinh a/a-1) := by
  classical
  have hlog : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hh0 := hd.trans hH
  apply bound v (by positivity) ha
  intro s k
  let e := 2*(k+1)
  let q := 4*k+2
  let A (j : ℕ) := H+d*(log (y+j+1)-log y+log 2)
  let K := s.sup bin + 1
  have maps : ∀ i ∈ s, bin i ∈ Finset.range K := fun i hi =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := bin) hi))
  have indiv {i : ι} {j : ℕ} (hi : bin i=j) :
      (v i)^e ≤ (a*y^2)^e/(y+j+1)^(q+2) := by
    have ww := weight i
    rw [hi] at ww
    calc
      _ = |v i|^e := by simp [e,pow_mul,sq_abs]
      _ ≤ (a*y^2/(y+j+1)^2)^e := pow_le_pow_left₀ (abs_nonneg _) ww _
      _ = _ := by rw [div_pow, ←pow_mul, show 2*e=q+2 by dsimp [e,q]; omega]
  have inbin (j : ℕ) : (∑ i ∈ s with bin i=j, (v i)^e) ≤
      8*(a*y^2)^e*(A j/(y+j+1)^(q+2)) := by
    calc
      _ ≤ ∑ i ∈ s with bin i=j, (a*y^2)^e/(y+j+1)^(q+2) :=
        Finset.sum_le_sum (fun i hi => indiv (Finset.mem_filter.mp hi).2)
      _ = ((s.filter (fun i => bin i=j)).card : ℝ)*((a*y^2)^e/(y+j+1)^(q+2)) := by simp
      _ ≤ (8*A j)*((a*y^2)^e/(y+j+1)^(q+2)) := mul_le_mul_of_nonneg_right (count s j) (by positivity)
      _ = _ := by ring
  have hg := LiMomentIntegral.grid hy hd hH q K
  have hc := mul_le_mul_of_nonneg_left hg (show 0 ≤ 8*(a*y^2)^e by positivity)
  have first : (∑ i ∈ s, (v i)^e) ≤ 8*(a*y^2)^e*
       (((H+d*log 2)/((q:ℝ)+1)+d/((q:ℝ)+1)^2)/y^(q+1)) := by
    calc
      _ = ∑ j ∈ Finset.range K, ∑ i ∈ s with bin i=j,(v i)^e := (Finset.sum_fiberwise_of_maps_to maps _).symm
      _ ≤ ∑ j ∈ Finset.range K, 8*(a*y^2)^e*(A j/(y+j+1)^(q+2)) := Finset.sum_le_sum (fun j _ => inbin j)
      _ = _ := (Finset.mul_sum ..).symm
      _ ≤ _ := hc
  let r : ℝ := (q:ℝ)+1
  have r3 : 3 ≤ r := by dsimp [r,q]; push_cast; linarith
  have rp : 0 < r := by linarith
  have den (W : ℝ) : 8*(a*y^2)^e * (W/y^(q+1)) = 8*y*a^e*W := by
    rw [mul_pow, ←pow_mul, show 2*e=(q+1)+1 by dsimp [e,q]; omega, pow_succ _ (q+1)]
    field_simp
  rw [den] at first
  have hsmall : (H+d*log 2)/r+d/r^2 ≤ (H+d*(log 2+1/3))/r := by
    field_simp
    nlinarith [mul_nonneg hd (sub_nonneg.mpr r3)]
  have hrid : r=4*(k:ℝ)+3 := by dsimp [r,q]; push_cast; ring
  calc
    _ ≤ _ := first
    _ ≤ 8*y*a^e*((H+d*(log 2+1/3))/r) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by rw [hrid]; dsimp [e]; ring

/-- The numerical constant nine from the conductor bound `d log 4095 ≤ H`. -/
theorem nine {H d : ℝ} (hd : 0 ≤ d) (hH : d*log 4095 ≤ H) :
    8*(H+d*(log 2+1/3)) ≤ 9*H := by
  have p := log_le_log (show 0 < (2:ℝ)^119 by positivity) (show (2:ℝ)^119 ≤ 4095^10 by norm_num)
  rw [log_pow, log_pow] at p
  norm_num at p
  have h : 8*(log 2+1/3) ≤ log 4095 := by linarith [log_two_gt_d9]
  nlinarith [mul_nonneg hd (sub_nonneg.mpr h)]

/-- Monotonicity supplying every intermediate Li index below the integrated endpoint. -/
theorem sinh_ratio_mono {a A : ℝ} (ha : 0 < a) (h : a ≤ A) :
    (sinh a/a-1)/a ≤ (sinh A/A-1)/A := by
  have series {x : ℝ} (hx : 0 < x) : HasSum
      (fun k : ℕ => x^(2*k+1)/(Nat.factorial (2*(k+1)+1) : ℝ)) ((sinh x/x-1)/x) := by
    convert (sinh_tail hx).div_const x using 1
    ext k
    rw [show x^(2*(k+1)) = x^(2*k+1)*x by rw [←pow_succ]; congr 1]
    field_simp
  have sa := series ha
  have sA := series (ha.trans_le h)
  rw [←sa.tsum_eq, ←sA.tsum_eq]
  exact sa.summable.tsum_le_tsum
    (fun k => div_le_div_of_nonneg_right (pow_le_pow_left₀ ha.le h _) (by positivity)) sA.summable

/-- The normalized hyperbolic-sine loss is nonnegative at every positive scale. -/
theorem sinh_nonneg_loss {a : ℝ} (ha : 0 < a) : 0 ≤ sinh a/a-1 := by
  rw [←(sinh_tail ha).tsum_eq]
  exact tsum_nonneg (fun _ => by positivity)

#print axioms LiMomentIntegral.grid
#print axioms bound
#print axioms unit_bins
#print axioms nine
#print axioms sinh_ratio_mono
end LiMomentTail
