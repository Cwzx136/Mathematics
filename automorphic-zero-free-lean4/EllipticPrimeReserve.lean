import EllipticEulerGain
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EllipticBernstein

/-- The local cost retained at a prime of norm q. The parameter M is any upper
bound for σ; the effective elliptic proof can take M=1.02. -/
theorem prime_reserve (q σ σ₁ M κ : ℝ) (hq : 1 < q) (hσ : 0 < σ)
    (hM : σ ≤ M) (hσ₁ : σ ≤ σ₁) (hk0 : 0 ≤ κ) (hk1 : κ ≤ 1)
    (b θ : ℕ → ℝ) (ramified : ℕ → Bool) (hb : ∀ n, |b n| ≤ 1) :
    let f := fun n : ℕ => Real.log q * (((q^(-σ))^(n+1)-κ*(q^(-σ₁))^(n+1)) *
                  specialCoefficient (ramified n) (b n) (θ n))
    Summable f ∧ (1-κ)/20 * (Real.log q / (q^M - 1)) ≤ ∑' n : ℕ, f n := by
  dsimp only
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have ha0 := (Real.rpow_pos_of_pos hq0 (-σ)).le
  have ha1 := Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr hσ)
  have hc0 := (Real.rpow_pos_of_pos hq0 (-σ₁)).le
  have hca := Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hσ₁)
  have h := geometric_reserve (q^(-σ)) (q^(-σ₁)) κ ha0 ha1 hc0 hca hk0 hk1 b θ ramified hb
  have hbig := Real.one_lt_rpow hq hσ
  have hi := Real.rpow_pos_of_pos hq0 σ
  have hid : q^(-σ)/(1-q^(-σ)) = 1/(q^σ-1) := by
    rw [Real.rpow_neg hq0.le]
    field_simp [hi.ne', (sub_pos.mpr hbig).ne', (sub_neg.mpr hbig).ne']
  have hle : 1/(q^M-1) ≤ 1/(q^σ-1) :=
    one_div_le_one_div_of_le (sub_pos.mpr hbig)
      (sub_le_sub_right (Real.rpow_le_rpow_of_exponent_le hq.le hM) 1)
  have hlog := Real.log_nonneg hq.le
  constructor
  · exact h.1.mul_left _
  · rw [h.1.tsum_mul_left]
    calc
      (1-κ)/20*(Real.log q/(q^M-1)) =
        Real.log q*((1-κ)/20*(1/(q^M-1))) := by ring
      _ ≤ Real.log q*((1-κ)/20*(q^(-σ)/(1-q^(-σ)))) := by
        rw [hid]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hle (by positivity)) hlog
      _ ≤ _ := mul_le_mul_of_nonneg_left h.2 hlog

#print axioms prime_reserve
end EllipticBernstein
