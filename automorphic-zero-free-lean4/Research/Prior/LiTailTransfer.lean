import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Transfer of the positive phase sum through an explicitly bounded modulus loss.
The unit-interval zero count and the lower bound for the phase sum are analytical inputs. -/
namespace LiTailTransfer
open Real

/-- A pointwise comparison remains valid after absolutely summing a zero divisor. -/
theorem tsum_comparison {ι : Type*} (v θ : ι → ℝ)
    (hb : Summable (fun i => 1-cos (θ i)))
    (he : Summable (fun i => cosh (v i)-1))
    (hs : Summable (fun i => 1-cosh (v i)*cos (θ i))) :
    (∑' i : ι, (1-cos (θ i))) - (∑' i : ι, (cosh (v i)-1)) ≤ ∑' i : ι, (1-cosh (v i)*cos (θ i)) := by
  rw [←hb.tsum_sub he]
  apply (hb.sub he).tsum_le_tsum _ hs
  intro i
  nlinarith [mul_nonneg (sub_nonneg.mpr (one_le_cosh (v i))) (sub_nonneg.mpr (cos_le_one (θ i)))]

/-- The logarithmic margin at the smallest height needs no decimal log approximations
beyond Mathlib's proved rational lower bound for log 2. -/
theorem log_margin {T : ℝ} (hT : 4096 ≤ T) :
    8*log T/11 ≤ log T + 2*log (log T) - log 576 := by
  have h4096 : log (4096:ℝ) = 12*log 2 := by
    rw [show (4096:ℝ) = 2^12 by norm_num, log_pow]; norm_num
  have hlarge := log_le_log (by norm_num : 0 < (4096:ℝ)) hT
  have L8 : 8 ≤ log T := by linarith [log_two_gt_d9]
  have hlog := log_le_log (by norm_num : 0 < (8:ℝ)) L8
  have harith : (576:ℝ)^11 ≤ 4096^3*8^22 := by norm_num
  have hh := log_le_log (by norm_num : 0 < (576:ℝ)^11) harith
  rw [log_mul (by norm_num) (by norm_num), log_pow, log_pow, log_pow] at hh
  norm_num at hh
  linarith

/-- The endpoint error estimate used in the uniform theorem is strictly below one. -/
theorem endpoint_ratio {T : ℝ} (hT : 4096 ≤ T) :
    let L := log T
    let a := L+2*log L-log 576
    288 * exp a / ((T-1)*a^2) < 1 := by
  dsimp only
  set L := log T
  set a := L+2*log L-log 576
  have ht : 0 < T := by linarith
  have hl : 0 < L := log_pos (by linarith)
  have ha : 8*L/11 ≤ a := log_margin hT
  have ap : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hexp : exp a = T*L^2/576 := by
    dsimp [a]
    rw [exp_sub, exp_add, show 2 * log L = log L + log L by ring, exp_add, exp_log hl,
      exp_log (by norm_num : 0 < (576:ℝ)), show exp L = T from exp_log ht]
    ring
  have hr : 0 < T-1 := by linarith
  have hsq : (8*L/11)^2 ≤ a^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ a+8*L/11 by linarith)]
  have hT' : 4095*T/4096 ≤ T-1 := by linarith
  have hden := mul_le_mul hT' hsq (sq_nonneg _) hr.le
  rw [hexp, div_lt_one (mul_pos hr (sq_pos_of_pos ap))]
  nlinarith [mul_pos ht (sq_pos_of_pos hl)]

/-- Assuming an actual lower bound on the angle sum, the integrated hyperbolic-sine
majorant entails strict positivity at the uniform endpoint. -/
theorem endpoint_transfer {T H B E S : ℝ} (ht : 4096 ≤ T) (hH : 0 < H)
    (hB : 2*(T-1)^2*(log T+2*log (log T)-log 576)*H/128 ≤ B)
    (hE : E ≤ 9*(T-1)*H*(sinh (log T+2*log (log T)-log 576)/
      (log T+2*log (log T)-log 576)-1)) (hS : B-E ≤ S) : 0 < S := by
  let a := log T+2*log (log T)-log 576
  have hL : 0 < log T := log_pos (by linarith)
  have ha : 0 < a := lt_of_lt_of_le (by positivity : 0 < 8*log T/11) (log_margin ht)
  have hy : 0 < T-1 := by linarith
  have hrat := endpoint_ratio ht
  change 288*exp a/((T-1)*a^2) < 1 at hrat
  rw [div_lt_one (mul_pos hy (sq_pos_of_pos ha))] at hrat
  have hsinh : sinh a/a-1 < exp a/(2*a) := by
    rw [sinh_eq]
    field_simp
    linarith [exp_pos (-a)]
  have hleft := mul_lt_mul_of_pos_left hsinh (show 0 < 9*(T-1)*H by positivity)
  have hright : 9*(T-1)*H*(exp a/(2*a)) < 2*(T-1)^2*a*H/128 := by
    have h := mul_lt_mul_of_pos_right hrat (mul_pos hy hH)
    field_simp
    nlinarith
  change 2*(T-1)^2*a*H/128 ≤ B at hB
  change E ≤ 9*(T-1)*H*(sinh a/a-1) at hE
  linarith

#print axioms tsum_comparison
#print axioms log_margin
#print axioms endpoint_ratio
#print axioms endpoint_transfer

end LiTailTransfer
