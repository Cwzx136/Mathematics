import Research.SignedKernel
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order

noncomputable section
namespace ERH.HadamardBudget
open ERH.MultiShift ERH.SignedKernel

/-- Apply the signed abscissa comparison to arbitrary real data. -/
def difference (m : ℕ) (f : ℕ → ℝ) := f 0 - linear m f

theorem difference_sub (m : ℕ) (a b : ℕ → ℝ) :
    difference m (fun j => a j-b j) = difference m a - difference m b := by
  unfold difference linear
  simp_rw [show ∀ k : ℕ, (a (2*k+1)-b (2*k+1))-(a (2*k+2)-b (2*k+2)) =
      (a (2*k+1)-a (2*k+2))-(b (2*k+1)-b (2*k+2)) from fun _ => by ring]
  rw [Finset.sum_sub_distrib]
  ring

theorem difference_mul (m : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    difference m (fun j => c*f j) = c*difference m f := by
  unfold difference linear
  simp_rw [← mul_sub]
  rw [← Finset.mul_sum]
  ring

theorem hasSum_difference {ι : Type*} (m : ℕ) {f : ℕ → ι → ℝ} {a : ℕ → ℝ}
    (ha : ∀ j, HasSum (f j) (a j)) :
    HasSum (fun i => difference m (fun j => f j i)) (difference m a) := by
  exact (ha 0).sub ((hasSum_sum (s := Finset.range m)
    (fun k _ => (ha (2*k+1)).sub (ha (2*k+2)))).add
    (HasSum.mul_left (weight m) (ha (2*m+1))))

/-- Prime powers, with initial nonnegative coefficient c and 0≤x≤1, acquire
the weight 1−linear(x^j). The assertion permits an infinite Euler expansion. -/
theorem euler_difference_nonneg {ι : Type*} (m : ℕ) (c x : ι → ℝ) (e : ℕ → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (he : ∀ j : ℕ, HasSum (fun i => c i * (x i)^j) (e j)) : 0 ≤ difference m e := by
  have h := hasSum_difference m he
  rw [← h.tsum_eq]
  apply tsum_nonneg
  intro i
  rw [difference_mul]
  apply mul_nonneg (hc i)
  simpa [difference] using (euler_weight_pos m (hx i).1 (hx i).2).le

/-- From the ordinary absolutely convergent reflected Hadamard sums and ordinary
Euler sums at the listed real abscissae, recover the target-zero inequality.
The list of paired zeros may be infinite and all weights may be nonintegral. -/
theorem target_from_expansions {I J : Type*} (m : ℕ) {u : ℝ} (hu : 0 < u)
    (b y w : I → ℝ) (bstrip : ∀ i, 0 ≤ b i ∧ b i ≤ 1) (hw : ∀ i, 0 ≤ w i)
    (i₀ : I) (hq : w i₀=1) (hy : y i₀=0)
    (c x : J → ℝ) (hc : ∀ k, 0 ≤ c k) (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (arch e : ℕ → ℝ)
    (euler : ∀ j : ℕ, HasSum (fun k => c k * (x k)^j) (e j))
    (hadamard : ∀ j : ℕ, HasSum
      (fun i => w i*pair (u+j) (b i) (y i)) (arch j-e j)) :
    1/(1+u-b i₀) ≤ difference m arch+(2*(m:ℝ)+1) := by
  have h := hasSum_difference m hadamard
  have expand (i : I) :
      difference m (fun j : ℕ => w i*pair (u+j) (b i) (y i)) =
        w i*corrected m u (b i) (y i) := by
    rw [difference_mul]
    simp [difference, corrected]
  have nonneg (i : I) : 0 ≤ difference m (fun j : ℕ => w i*pair (u+j) (b i) (y i)) := by
    rw [expand]; exact mul_nonneg (hw i) (corrected_nonneg m hu (bstrip i).1 (bstrip i).2 _)
  have hsel := h.summable.le_tsum i₀ (fun i _ => nonneg i)
  rw [h.tsum_eq,expand,hq,one_mul,hy,difference_sub] at hsel
  have he := euler_difference_nonneg m c x e hc hx euler
  linarith [target m hu (bstrip i₀).1 (bstrip i₀).2]

#print axioms target_from_expansions
end ERH.HadamardBudget
