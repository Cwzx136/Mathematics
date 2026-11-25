import Research.Prior.LiMomentTail
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-! Explicit Euler and archimedean error estimates used at the three
abscissas in the threshold-free quadratic Li proof. -/
namespace LiEulerGammaBounds
open Real Set MeasureTheory

noncomputable def eulerWeight (s : ℝ) (n : ℕ) : ℝ := 1/((n:ℝ)+1)^s
noncomputable def logWeight (s : ℝ) (n : ℕ) : ℝ := log ((n:ℝ)+1)/((n:ℝ)+1)^s
noncomputable def eulerRatio (s : ℝ) : ℝ :=
  (∑' n:ℕ,logWeight s n)/(∑' n:ℕ,eulerWeight s n)

private theorem logWeight_nonneg (s : ℝ) (n : ℕ) : 0 ≤ logWeight s n := by
  unfold logWeight
  apply div_nonneg (log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  positivity

private theorem weight_sum {s : ℝ} (h : 1 < s) : Summable (eulerWeight s) := by
  apply ((summable_one_div_nat_add_rpow 1 s).mpr h).congr
  intro n
  rw [abs_of_nonneg (show 0 ≤ (n:ℝ)+1 by positivity)]; rfl

private theorem log6_upper : log (6:ℝ) ≤ (13/5)*log 2 := by
  have h := log_le_log (show (0:ℝ)<6^5 by positivity) (show (6:ℝ)^5 ≤ 2^13 by norm_num)
  rw [log_pow,log_pow] at h; norm_num at h; linarith

/-- Bounding the logarithmic numerator by an exact sum–integral comparison.
All logarithms appearing in the finite head are bounded by integer powers. -/
theorem numerator_two : Summable (logWeight 2) ∧ (∑' n:ℕ,logWeight 2 n) ≤ 0.97 := by
  have hH : 1 ≤ log 6-log 2 := by
    rw [←log_div (by norm_num) (by norm_num),show (6:ℝ)/2=3 by norm_num]
    have l := log_le_log (exp_pos 1) (show exp 1 ≤ 3 by linarith [exp_one_lt_d9])
    simpa only [log_exp] using l
  have tail (N : ℕ) : (∑ j∈Finset.range N,logWeight 2 (j+6)) ≤ (log 6+1)/6 := by
    have h := LiMomentIntegral.grid (y:=6) (H:=log 6-log 2) (d:=1) (by norm_num) (by norm_num) hH 0 N
    have eq (j : ℕ) : logWeight 2 (j+6) =
      ((log 6-log 2)+1*(log (6+j+1)-log 6+log 2))/(6+j+1)^(0+2) := by
      unfold logWeight
      rw [rpow_two,Nat.cast_add,Nat.cast_ofNat,add_comm 6 (j:ℝ)]
      ring
    simp only [eq]
    convert h using 1; norm_num
  have hs := summable_of_sum_range_le (fun n => logWeight_nonneg 2 (n+6)) tail
  have tl := Real.tsum_le_of_sum_range_le (fun n => logWeight_nonneg 2 (n+6)) tail
  have h3 := log_le_log (show (0:ℝ)<3^5 by positivity) (show (3:ℝ)^5 ≤ 2^8 by norm_num)
  have h5 := log_le_log (show (0:ℝ)<5^3 by positivity) (show (5:ℝ)^3 ≤ 2^7 by norm_num)
  rw [log_pow,log_pow] at h3 h5
  norm_num at h3 h5
  have l4 : log (4:ℝ) = 2*log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow]; norm_num
  have head : (∑ n∈Finset.range 6,logWeight 2 n) ≤ 0.5 := by
    norm_num [Finset.sum_range_succ,logWeight,rpow_two]
    linarith [log_two_lt_d9,log6_upper]
  have all := (summable_nat_add_iff 6).mp hs
  refine ⟨all,?_⟩
  rw [←all.sum_add_tsum_nat_add 6]
  linarith [log_two_lt_d9,log6_upper]

/-- The Dirichlet series quotient equal to −ζ′(2)/ζ(2) is below .65. -/
theorem euler_at_two : eulerRatio 2 < 0.65 := by
  have h := (weight_sum (by norm_num : (1:ℝ)<2)).sum_le_tsum (Finset.range 7)
    (fun n _ => (by positivity : 0 ≤ 1/((n:ℝ)+1)^(2:ℝ)))
  have head : 1.5 ≤ ∑ j∈Finset.range 7,eulerWeight 2 j := by
    norm_num [Finset.sum_range_succ,eulerWeight,rpow_two]
  have den : (1.5:ℝ) ≤ ∑' i,eulerWeight 2 i := head.trans h
  unfold eulerRatio
  rw [div_lt_iff₀ (by linarith)]
  linarith [numerator_two.2]

/-- At large real parts, the logarithmic weight starts at two, so moving the
abscissa by thirteen buys a factor of 8192 for the entire numerator. -/
theorem euler_high {s : ℝ} (hs : 15 ≤ s) : eulerRatio s < 0.001 := by
  have w (n : ℕ) : logWeight s n ≤ (1/8192)*logWeight 2 n := by
    cases n with
    | zero => simp [logWeight]
    | succ k =>
      let x : ℝ := (k.succ:ℝ)+1
      have x2 : 2 ≤ x := by dsimp [x]; push_cast; linarith
      have xp : 0 < x := by linarith
      have x1 : 1 ≤ x := by linarith
      have logx := log_nonneg x1
      have powbase : (8192:ℝ) ≤ x^13 := by
        simpa only [show (2:ℝ)^13=8192 by norm_num] using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) x2 13
      have ab : x^(15:ℝ) ≤ x^s := rpow_le_rpow_of_exponent_le x1 hs
      have mul : 8192*x^2 ≤ x^s := by
        apply le_trans _ ab
        rw [show (15:ℝ)=(15:ℕ) by norm_num,rpow_natCast]
        nlinarith [mul_le_mul_of_nonneg_right powbase (sq_nonneg x)]
      change log x/x^s ≤ (1/8192)*(log x/x^(2:ℝ))
      rw [rpow_two,show (1/8192:ℝ)*(log x/x^2)=log x/(8192*x^2) by ring]
      exact div_le_div_of_nonneg_left logx (by positivity) mul
  have small : Summable (logWeight s) :=
    (numerator_two.1.mul_left (1/8192:ℝ)).of_nonneg_of_le (logWeight_nonneg s) w
  have top := small.tsum_le_tsum w (numerator_two.1.mul_left (1/8192:ℝ))
  rw [numerator_two.1.tsum_mul_left] at top
  have h := (weight_sum (s:=s) (by linarith)).sum_le_tsum (Finset.range 1)
    (fun n _ => (by positivity : 0 ≤ 1/((n:ℝ)+1)^s))
  have den : (1:ℝ) ≤ ∑' i,eulerWeight s i := by
    change (∑ i∈Finset.range 1,eulerWeight s i) ≤ ∑' i,eulerWeight s i at h
    simpa only [Finset.sum_range_one,show eulerWeight s 0=1 by simp [eulerWeight]] using h
  unfold eulerRatio
  rw [div_lt_iff₀ (by linarith)]
  linarith [numerator_two.2]

/-- The Laplace kernel in the classical integral for log z−ψ(z) is bounded
between zero and one throughout the positive real axis. -/
theorem laplace_kernel {x : ℝ} (hx : 0 < x) :
    0 ≤ 1/(1-exp (-x))-1/x ∧ 1/(1-exp (-x))-1/x ≤ 1 := by
  have e := exp_pos (-x)
  have neg : exp (-x)<1 := exp_lt_one_iff.mpr (by linarith)
  have low := add_one_le_exp (-x)
  have hi := add_one_le_exp x
  have inv : exp x * exp (-x)=1 := by rw [←exp_add]; simp
  have hmul := mul_le_mul_of_nonneg_right hi e.le
  constructor
  · rw [sub_nonneg]
    exact div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)
  · rw [sub_le_iff_le_add,div_le_iff₀ (by linarith)]
    have h : exp (-x) ≤ (1-exp (-x))/x := (le_div_iff₀ hx).mpr (by nlinarith)
    rw [show (1-exp (-x))/x=1/x-(1/x)*exp (-x) by ring] at h
    nlinarith

/-- The digamma error bound follows directly from its classical Laplace integral.
Only the integral identity for the actual special function is supplied. -/
theorem digamma_bound {z : ℂ} (hz : 0 < z.re)
    (integralIdentity : Complex.log z-Complex.digamma z =
      ∫ x : ℝ in Ioi 0,Complex.exp (-z*(x:ℂ))*((1/(1-exp (-x))-1/x:ℝ):ℂ)) :
    ‖Complex.log z-Complex.digamma z‖ ≤ 1/z.re := by
  rw [integralIdentity]
  have hg := integrableOn_exp_mul_Ioi (a := -z.re) (by linarith) 0
  have bound := norm_integral_le_of_norm_le hg (f := fun x:ℝ =>
    Complex.exp (-z*(x:ℂ))*((1/(1-exp (-x))-1/x:ℝ):ℂ)) (by
      filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioi 0) measurableSet_Ioi] with x hx
      change 0 < x at hx
      rw [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (laplace_kernel hx).1]
      simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,
        mul_zero,sub_zero]
      nlinarith [mul_le_mul_of_nonneg_left (laplace_kernel hx).2 (exp_pos (-z.re*x)).le])
  rw [integral_exp_mul_Ioi (by linarith),mul_zero,exp_zero,neg_div_neg_eq] at bound
  exact bound

#print axioms numerator_two
#print axioms euler_at_two
#print axioms euler_high
#print axioms laplace_kernel
#print axioms digamma_bound

end LiEulerGammaBounds
