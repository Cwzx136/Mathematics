import Research.Prior.LiMomentTail
import Research.Prior.LiTailTransfer

/-! Integrated Li-coefficient positivity from the spectral phase mass and a
unit-interval zero count. The real variables `v` and `θ` are the signed log
modulus and the phase, each already multiplied by the index `m`. -/
namespace LiUniformTransfer
open Real

private theorem inside {T a H : ℝ} (hT : 4096 ≤ T) (ha : 0 < a) (hH : 0 < H)
    (hmax : a ≤ log T+2*log (log T)-log 576) :
    9*(T-1)*H*(sinh a/a-1) < 2*(T-1)^2*a*H/128 := by
  let A := log T+2*log (log T)-log 576
  have hA : 0 < A := ha.trans_le hmax
  have hy : 0 < T-1 := by linarith
  let B := 2*(T-1)^2*A*H/128
  let E := 9*(T-1)*H*(sinh A/A-1)
  have hh : 0 < B-E := LiTailTransfer.endpoint_transfer hT hH le_rfl le_rfl le_rfl
  have large : (9*(T-1)*H)*((sinh A/A-1)/A) < 2*(T-1)^2*H/128 := by
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hA).mpr
    dsimp [B,E] at hh
    linarith
  have ratio := (mul_le_mul_of_nonneg_left (LiMomentTail.sinh_ratio_mono ha hmax)
    (show 0 ≤ 9*(T-1)*H by positivity)).trans_lt large
  have resized := mul_lt_mul_of_pos_right ratio ha
  rw [mul_assoc (9*(T-1)*H), div_mul_cancel₀ _ ha.ne'] at resized
  linarith

/-- For each index in the explicit nonlinear prefix, the analytic inputs are a
lower bound for the phase sum, a cardinality bound on each unit shell of the
high divisor, and the pointwise geometric upper bound for the log modulus. -/
theorem positive {ι : Type*} (v θ : ι → ℝ) (high : Set ι) (bin : high → ℕ)
    {T m d H : ℝ} (hT : 4096 ≤ T) (hm : 0 < m) (hd : 0 ≤ d) (hH : 0 < H)
    (hHd : d*log 4095 ≤ H)
    (hcap : m ≤ 2*(T-1)^2*(log T+2*log (log T)-log 576))
    (low : ∀ i, i ∉ high → v i=0)
    (count : ∀ (s : Finset high) (j : ℕ), ((s.filter (fun i => bin i=j)).card : ℝ) ≤
       8*(H+d*(log ((T-1)+j+1)-log (T-1)+log 2)))
    (weight : ∀ i : high, |v i| ≤ m/(2*((T-1)+(bin i:ℝ)+1)^2))
    (hb : Summable (fun i => 1-cos (θ i)))
    (hs : Summable (fun i => 1-cosh (v i)*cos (θ i)))
    (base : m*H/128 ≤ ∑' i : ι, (1-cos (θ i))) :
    0 < ∑' i : ι, (1-cosh (v i)*cos (θ i)) := by
  let y := T-1
  let a := m/(2*y^2)
  have hy : 0 < y := by dsimp [y]; linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hm' : m = 2*y^2*a := by dsimp [a]; field_simp
  have hacap : a ≤ log T+2*log (log T)-log 576 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*y^2)).mpr
    dsimp [y]; linarith
  have dH : d ≤ H := by
    have h4 : log (4:ℝ) = 2*log 2 := by rw [show (4:ℝ)=2^2 by norm_num, log_pow]; norm_num
    have hc := log_le_log (by norm_num : (0:ℝ)<4) (by norm_num : (4:ℝ)≤4095)
    have hl : 1 ≤ log 4095 := by linarith [log_two_gt_d9]
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hl)]
  have hw (i : high) : |v i| ≤ a*y^2/(y+(bin i:ℝ)+1)^2 := by
    have hw' := weight i
    change |v i| ≤ m/(2*(y+(bin i:ℝ)+1)^2) at hw'
    convert hw' using 1
    dsimp [a]; field_simp
  obtain ⟨tail,tail_le⟩ := LiMomentTail.unit_bins (fun i : high => v i) bin hy hd dH ha count hw
  have support : Function.support (fun i => cosh (v i)-1) ⊆ high := by
    intro i hi
    by_contra hn
    exact hi (by simp [low i hn])
  have hsum := (hasSum_subtype_iff_of_support_subset support).mp tail.hasSum
  have hadd := LiTailTransfer.tsum_comparison v θ hb hsum.summable hs
  rw [hsum.tsum_eq] at hadd
  have hscale := LiMomentTail.nine hd hHd
  have hE : (∑' i : high, (cosh (v i)-1)) ≤ 9*y*H*(sinh a/a-1) := by
    refine tail_le.trans ?_
    apply mul_le_mul_of_nonneg_right _ (LiMomentTail.sinh_nonneg_loss ha)
    nlinarith [mul_le_mul_of_nonneg_left hscale hy.le]
  have hmarg := inside hT ha hH hacap
  change 9*y*H*(sinh a/a-1) < 2*y^2*a*H/128 at hmarg
  rw [←hm'] at hmarg
  linarith

#print axioms positive
end LiUniformTransfer
