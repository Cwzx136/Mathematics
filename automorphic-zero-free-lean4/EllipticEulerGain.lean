import EllipticLocal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace EllipticBernstein

def mass : List Entry → Nat
  | [] => 0
  | (_,_,c)::s => c + mass s

theorem special_abs (b θ : ℝ) (hb : |b| ≤ 1) (s : List Entry) :
    |specialEval b (Real.cos θ) s| ≤ (mass s : ℝ) := by
  induction s with
  | nil => simp [specialEval, mass]
  | cons e s ih =>
    obtain ⟨l,j,c⟩ := e
    have ht : |chebT l (Real.cos θ)| ≤ 1 := by
      rw [chebT_eq_standard, Polynomial.Chebyshev.T_real_cos]
      exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hp := pow_le_one₀ (abs_nonneg b) hb (n:=j)
    simp only [specialEval, mass, Nat.cast_add]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg c), abs_pow]
    calc
      (c:ℝ) * |b|^j * |chebT l (Real.cos θ)| ≤
        (c:ℝ) * 1 * 1 := (mul_le_mul
          (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg c)) ht (abs_nonneg _)
          (by positivity))
      _ = _ := by ring

noncomputable def specialCoefficient (ramified : Bool) (b θ : ℝ) : ℝ :=
  (if ramified then specialEven b (Real.cos θ) reducedTable
    else specialEval b (Real.cos θ) reducedTable)/1000000

theorem specialCoefficient_bounds (e : Bool) {b : ℝ} (hb : |b| ≤ 1) (θ : ℝ) :
    1/20 ≤ specialCoefficient e b θ ∧ specialCoefficient e b θ ≤ 4 := by
  have hmass : mass reducedTable = 3240845 := by decide +kernel
  have bounds (r : ℝ) (hr : |r| ≤ 1) :
      50000 ≤ specialEval r (Real.cos θ) reducedTable ∧
      specialEval r (Real.cos θ) reducedTable ≤ 3240845 := by
    constructor
    · exact special_margin _ _ (abs_le.mp hr).1 (abs_le.mp hr).2
        (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
    · have h := (le_abs_self _).trans (special_abs r θ hr reducedTable)
      simpa only [hmass, Nat.cast_ofNat] using h
  have h := bounds b hb
  cases e with
  | false =>
    simp only [specialCoefficient, Bool.false_eq_true, ↓reduceIte]
    constructor <;> linarith [h.1, h.2]
  | true =>
    have hn := bounds (-b) (by simpa only [abs_neg] using hb)
    simp only [specialCoefficient, ↓reduceIte, special_involution]
    constructor <;> linarith [h.1, h.2, hn.1, hn.2]

/-- A complete local Stechkin series. The hypotheses on a,c are satisfied
by a=q^(-σ), c=q^(-σ₁), σ₁≥σ>0. Both absolute convergence and the reserve
of one twentieth times the differenced geometric series are proved. -/
theorem geometric_reserve (a c κ : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hc : 0 ≤ c) (hca : c ≤ a) (hk0 : 0 ≤ κ) (hk1 : κ ≤ 1)
    (b θ : ℕ → ℝ) (ramified : ℕ → Bool) (hb : ∀ n, |b n| ≤ 1) :
    let f := fun n : ℕ => (a^(n+1)-κ*c^(n+1)) * specialCoefficient (ramified n) (b n) (θ n)
    Summable f ∧ (1-κ)/20*(a/(1-a)) ≤ ∑' n : ℕ, f n := by
  dsimp only
  have bounds n := specialCoefficient_bounds (ramified n) (hb n) (θ n)
  have hp n : c^(n+1) ≤ a^(n+1) := pow_le_pow_left₀ hc hca _
  have hdist n : (1-κ)*a^(n+1) ≤ a^(n+1)-κ*c^(n+1) := by
    have := mul_le_mul_of_nonneg_left (hp n) hk0
    linarith
  have hnon n : 0 ≤ a^(n+1)-κ*c^(n+1) :=
    (mul_nonneg (sub_nonneg.mpr hk1) (pow_nonneg ha _)).trans (hdist n)
  have gsum : HasSum (fun n : ℕ => a^(n+1)) (a/(1-a)) := by
    simpa only [pow_succ', div_eq_mul_inv] using (hasSum_geometric_of_lt_one ha ha1).mul_left a
  have upper := gsum.summable.mul_right 4
  have main : Summable (fun n : ℕ => (a^(n+1)-κ*c^(n+1)) *
      specialCoefficient (ramified n) (b n) (θ n)) := by
    apply Summable.of_nonneg_of_le _ _ upper
    · intro n
      exact mul_nonneg (hnon n) ((by norm_num : (0:ℝ) ≤ 1/20).trans (bounds n).1)
    · intro n
      exact mul_le_mul (sub_le_self _ (mul_nonneg hk0 (pow_nonneg hc _))) (bounds n).2
        ((by norm_num : (0:ℝ) ≤ 1/20).trans (bounds n).1) (pow_nonneg ha _)
  constructor
  · exact main
  · have lower := gsum.mul_left ((1-κ)/20)
    rw [← lower.tsum_eq]
    apply lower.summable.tsum_le_tsum (hg := main)
    intro n
    calc
      (1-κ)/20*a^(n+1) = ((1-κ)*a^(n+1))*(1/20) := by ring
      _ ≤ _ := mul_le_mul (hdist n) (bounds n).1 (by norm_num) (hnon n)

#print axioms specialCoefficient_bounds
#print axioms geometric_reserve
end EllipticBernstein
