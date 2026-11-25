import Research.EdgeDisks
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Multiple selected zeros, each tested at its own ordinate.
The explicit-formula budget is an assumption. All finite real analysis and
kernel cancellation below are proved internally. Indices distinguish multiplicities. -/
noncomputable section
open scoped BigOperators
namespace ERH.Occupation

def kernel (u t : ℝ) : ℝ := u / (u^2 + t^2)
def atten (v x : ℝ) : ℝ := v/(v+x)

theorem kernel_nonneg {v : ℝ} (hv : 0 < v) (t : ℝ) : 0 ≤ kernel v t := by
  unfold kernel
  positivity

/-- Moving a pole inward diminishes its Poisson kernel by at most v/(v+x). -/
theorem kernel_transport {v x : ℝ} (hv : 0 < v) (hx : 0 ≤ x) (t : ℝ) :
    atten v x * kernel v t ≤ kernel (v+x) t := by
  have h : 0 < v+x := by linarith
  have hd : 0 < v^2+t^2 := by positivity
  have hD : 0 < (v+x)^2+t^2 := by positivity
  unfold kernel atten
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos h hd) hD).2
  nlinarith only [mul_nonneg (sq_nonneg t) (mul_nonneg hx (show 0 ≤ 2*v+x by linarith))]

def pairs (k : ℕ) : Finset (Fin k × Fin k) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2)

def crossSignal {k : ℕ} (v : ℝ) (x y b : Fin k → ℝ) (p : Fin k × Fin k) : ℝ :=
  b p.1 * kernel (v+x p.2) (y p.1-y p.2) +
  b p.2 * kernel (v+x p.1) (y p.1-y p.2)

def crossPole {k : ℕ} (v : ℝ) (y b : Fin k → ℝ) (p : Fin k × Fin k) : ℝ :=
  b p.1 * b p.2 * kernel v (y p.1-y p.2)

/-- Budget after the two static poles have been normalized to total weight one.
B is the sum of the gamma costs; e bounds the remaining analytic error. -/
def Budget {k : ℕ} (v B e : ℝ) (x y b : Fin k → ℝ) : Prop :=
  (∑ i, b i / (v+x i)) + ∑ p ∈ pairs k, crossSignal v x y b p ≤
    1/v + B + e + ∑ p ∈ pairs k, crossPole v y b p

theorem cancel_pair {k : ℕ} {v : ℝ} {x y b : Fin k → ℝ}
    (hv : 0 < v) (hx : ∀ i, 0 ≤ x i) (hb : ∀ i, 0 ≤ b i)
    (paid : ∀ i, b i ≤ atten v (x i)) (p : Fin k × Fin k) :
    crossPole v y b p ≤ crossSignal v x y b p := by
  have h := kernel_nonneg hv (y p.1-y p.2)
  have h2 := mul_le_mul_of_nonneg_right (paid p.2) h
  have h3 := kernel_transport hv (hx p.2) (y p.1-y p.2)
  have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) (hb p.1)
  have h5 := kernel_nonneg (show 0 < v+x p.1 by linarith [hx p.1]) (y p.1-y p.2)
  unfold crossPole crossSignal
  rw [mul_assoc]
  exact h4.trans (le_add_of_nonneg_right (mul_nonneg (hb p.2) h5))

theorem cancel_budget {k : ℕ} {v B e : ℝ} {x y b : Fin k → ℝ}
    (hv : 0 < v) (hx : ∀ i, 0 ≤ x i) (hb : ∀ i, 0 ≤ b i)
    (paid : ∀ i, b i ≤ atten v (x i)) (h : Budget v B e x y b) :
    ∑ i, b i/(v+x i) ≤ 1/v+B+e := by
  have hc := Finset.sum_le_sum (s := pairs k)
      (fun p _ => cancel_pair (y := y) hv hx hb paid p)
  unfold Budget at h
  linarith

private theorem posPart_mul (a : ℝ) : max a 0 * a = (max a 0)^2 := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h]; ring
  · rw [max_eq_left h]; ring

/-- A weighted occupancy inequality for an individual arbitrary finite tuple.
The single analytic input is its budget for each nonnegative normalized weight.
The degree charges C may differ from index to index. -/
theorem energy_bound {k : ℕ} {v e : ℝ} (x y C : Fin k → ℝ)
    (hv : 0 < v) (he : 0 ≤ e) (hx : ∀ i, 0 ≤ x i) (hC : ∀ i, 0 ≤ C i)
    (budget : ∀ b : Fin k → ℝ, (∀ i, 0 ≤ b i) → (∑ i, (b i)^2) = 1 →
      Budget v (∑ i, b i * C i) e x y b) :
    Real.sqrt (∑ i, (max (atten v (x i)-v*C i) 0)^2) ≤ 1 + v*e := by
  let d := fun i => max (atten v (x i)-v*C i) 0
  let M := Real.sqrt (∑ i, (d i)^2)
  change M ≤ _
  by_cases hm : M ≤ 1
  · exact hm.trans (le_add_of_nonneg_right (mul_nonneg hv.le he))
  have hp : 0 < M := by linarith
  have hM : M^2 = ∑ i, (d i)^2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  let b := fun i => d i/M
  have hd : ∀ i, 0 ≤ d i := fun _ => le_max_right _ _
  have hb : ∀ i, 0 ≤ b i := fun i => div_nonneg (hd i) hp.le
  have hnorm : (∑ i, (b i)^2) = 1 := by
    simp only [b, div_pow, ← Finset.sum_div]
    rw [← hM, div_self (pow_ne_zero 2 hp.ne')]
  have paid (i : Fin k) : b i ≤ atten v (x i) := by
    have ha : 0 ≤ atten v (x i) := by
      unfold atten
      exact div_nonneg hv.le (by linarith [hx i])
    have hl : d i ≤ atten v (x i) := max_le (by linarith [mul_nonneg hv.le (hC i)]) ha
    apply (div_le_iff₀ hp).2
    calc
      d i ≤ atten v (x i) := hl
      _ ≤ atten v (x i)*M := le_mul_of_one_le_right ha (le_of_not_ge hm)
  have hnet := cancel_budget hv hx hb paid (budget b hb hnorm)
  have hdual : ∑ i, b i*(atten v (x i)-v*C i) = M := by
    have z (i : Fin k) : b i*(atten v (x i)-v*C i) = (d i)^2/M := by
      dsimp only [b]
      rw [div_mul_eq_mul_div, show d i*(atten v (x i)-v*C i) = (d i)^2 from posPart_mul _]
    simp only [z, ← Finset.sum_div, ← hM]
    field_simp
  have expand : (∑ i, b i*(atten v (x i)-v*C i)) =
      v*((∑ i, b i/(v+x i)) - ∑ i, b i*C i) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold atten
    ring
  rw [expand] at hdual
  have hvv : v*(1/v)=1 := by field_simp
  have hmul := mul_le_mul_of_nonneg_left hnet hv.le
  rw [mul_add, mul_add, hvv] at hmul
  linarith

/-- Finite exclusion from the moving-ordinate budget.  Here k=r⁴, the common
weight is 1/r², the total moving degree charge is G, and the optimizing
abscissa is v=(r-1)/G. No condition is imposed on differences of ordinates. -/
theorem strict_count_barrier {k : ℕ} {r G A : ℝ} (hr : 1 < r)
    (hk : (k : ℝ) = r^4) (hG : 0 < G) (hA : 0 ≤ A)
    (hsmall : A < (r-1)^2/G) :
    ∃ e : ℝ, 0 < e ∧ ∀ x y : Fin k → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ A) →
      ¬ Budget ((r-1)/G) G e x y (fun _ => 1/r^2) := by
  obtain ⟨e,he,hgap⟩ := EdgeDisks.below_barrier hr hG hA hsmall
  refine ⟨e,he,?_⟩
  intro x y hx hbudget
  let v := (r-1)/G
  have hv : 0 < v := div_pos (sub_pos.mpr hr) hG
  have hrp : 0 < r := by linarith
  have heq : v+(r-1)^2/G = v*r := by dsimp [v]; ring
  have hvr : v+A ≤ v*r := by linarith
  have hr1 : r ≤ r^2 := by nlinarith [mul_nonneg hrp.le (sub_nonneg.mpr hr.le)]
  have paid (i : Fin k) : 1/r^2 ≤ atten v (x i) := by
    unfold atten
    apply (div_le_div_iff₀ (show 0 < r^2 by positivity)
      (show 0 < v+x i by linarith [(hx i).1])).2
    nlinarith [mul_le_mul_of_nonneg_left hr1 hv.le,(hx i).2]
  have hnet := cancel_budget hv (fun i => (hx i).1)
    (b := fun _ => 1/r^2) (fun _ => by positivity) paid hbudget
  have each (i : Fin k) : (1/r^2)/(v+A) ≤ (1/r^2)/(v+x i) := by
    apply div_le_div_of_nonneg_left (by positivity)
      (by linarith [(hx i).1]) (by linarith [(hx i).2])
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun i _ => each i)
  have hbound : (k : ℝ)*((1/r^2)/(v+A)) ≤ 1/v+G+e := by
    simpa using hsum.trans hnet
  have hdiag : (k : ℝ)*((1/r^2)/(v+A)) = r^2/(v+A) := by
    rw [hk]
    field_simp
  rw [hdiag] at hbound
  have hbound' := (div_le_iff₀ (show 0 < v+A by linarith)).mp hbound
  change (v+A)*(1/v+G+e) < r^2 at hgap
  nlinarith

/-- An actual eventual bound for tuples of eligible occurrences. An injective
tuple can still repeat a geometric zero location when its multiplicity is bigger
than one. The analytic budget is quantified before the high-ordinate conclusion. -/
theorem eventual_cluster_exclusion {ι : Type*} {k : ℕ} {r G A : ℝ} (hr : 1 < r)
    (hk : (k : ℝ) = r^4) (hG : 0 < G) (hA : 0 ≤ A)
    (hsmall : A < (r-1)^2/G) (eligible : ℝ → ι → Prop) (x y : ℝ → ι → ℝ)
    (budget : ∀ e : ℝ, 0 < e → ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ z : Fin k → ι,
      Function.Injective z → (∀ i, eligible T (z i)) →
      Budget ((r-1)/G) G e (fun i => x T (z i)) (fun i => y T (z i))
        (fun _ => 1/r^2)) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ z : Fin k → ι, Function.Injective z →
      (∀ i, eligible T (z i)) → ¬ (∀ i, 0 ≤ x T (z i) ∧ x T (z i) ≤ A) := by
  obtain ⟨e,he,hex⟩ := strict_count_barrier hr hk hG hA hsmall
  obtain ⟨T₀,hT₀⟩ := budget e he
  refine ⟨T₀,?_⟩
  intro T hT z hz hgood hnear
  exact hex _ _ hnear (hT₀ T hT z hz hgood)

/-- For a subpower window the total gamma charge is G=c sqrt(k). This expresses
the optimized layer in the intrinsic coefficient c per standard constituent. -/
theorem subpower_radius {r c : ℝ} (hr : 1 < r) (hc : 0 < c) :
    (r-1)^2/(c*r^2) = (1-1/r)^2/c := by
  have hp : 0 < r := by linarith
  field_simp

/-- The limiting half-gamma multiplier gives c=d/4 for degree d.
With two arbitrary cuspidal zero occurrences the strict rounded denominator is 9.876 d. -/
theorem two_occurrences_constant {r d : ℝ} (hr : 1 < r) (hr4 : r^4 = 2) (hd : 0 < d) :
    1/((9876/1000)*d) < (1-1/r)^2/(d/4) := by
  have hrp : 0 < r := by linarith
  have hl : (1189207/1000000 : ℝ) < r := by
    by_contra! hc
    have hh := pow_le_pow_left₀ hrp.le hc 4
    rw [hr4] at hh
    norm_num at hh
  have hi := one_div_lt_one_div_of_lt (show (0:ℝ) < 1189207/1000000 by norm_num) hl
  norm_num at hi
  have ha : (1591035/10000000 : ℝ) < 1-1/r := by rw [one_div]; linarith
  have hs : (1591035/10000000 : ℝ)^2 ≤ (1-1/r)^2 :=
    pow_le_pow_left₀ (by norm_num) ha.le 2
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  have hc : (1/4:ℝ) < (1-1/r)^2*(9876/1000) := by nlinarith
  nlinarith [mul_lt_mul_of_pos_right hc hd]


/-- A variant for essentially self-dual forms. The cross pole has the
nonnegative coefficient λ; after dividing the real-trace square by two λ=1/2. -/
def scaledBudget {k : ℕ} (poleScale v B e : ℝ) (x y b : Fin k → ℝ) : Prop :=
  (∑ i, b i/(v+x i)) + ∑ p ∈ pairs k, crossSignal v x y b p ≤
     1/v+B+e + poleScale*(∑ p ∈ pairs k, crossPole v y b p)

theorem cancel_scaled {k : ℕ} {poleScale v B e : ℝ} {x y b : Fin k → ℝ}
    (hv : 0 < v) (hx : ∀ i, 0 ≤ x i) (hb : ∀ i, 0 ≤ b i)
    (coverage : ∀ i j, poleScale*(b i*b j) ≤ b i*atten v (x j)+b j*atten v (x i))
    (h : scaledBudget poleScale v B e x y b) :
    ∑ i, b i/(v+x i) ≤ 1/v+B+e := by
  have point (p : Fin k × Fin k) :
      poleScale*crossPole v y b p ≤ crossSignal v x y b p := by
    let t := y p.1-y p.2
    have hz := kernel_nonneg hv t
    have hs := mul_le_mul_of_nonneg_right (coverage p.1 p.2) hz
    have h₁ := mul_le_mul_of_nonneg_left (kernel_transport hv (hx p.2) t) (hb p.1)
    have h₂ := mul_le_mul_of_nonneg_left (kernel_transport hv (hx p.1) t) (hb p.2)
    change poleScale*(b p.1*b p.2*kernel v t) ≤
        b p.1*kernel (v+x p.2) t+b p.2*kernel (v+x p.1) t
    linarith only [hs,h₁,h₂]
  have hc := Finset.sum_le_sum (s := pairs k) (fun p _ => point p)
  rw [← Finset.mul_sum] at hc
  unfold scaledBudget at h
  linarith

/-- Uniform version accommodating either normalization of the moving test.
Only k times the common weight and the inequality paying for each cross pole enter. -/
theorem scaled_count_barrier {k : ℕ} {w poleScale r G A : ℝ} (hr : 1 < r)
    (hw : 0 < w) (hcount : (k : ℝ)*w = r^2) (hcover : poleScale*w*r ≤ 2)
    (hG : 0 < G) (hA : 0 ≤ A) (hsmall : A < (r-1)^2/G) :
    ∃ e : ℝ, 0 < e ∧ ∀ x y : Fin k → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ A) →
      ¬ scaledBudget poleScale ((r-1)/G) G e x y (fun _ => w) := by
  obtain ⟨e,he,hgap⟩ := EdgeDisks.below_barrier hr hG hA hsmall
  refine ⟨e,he,?_⟩
  intro x y hx hbudget
  let v := (r-1)/G
  have hv : 0 < v := div_pos (sub_pos.mpr hr) hG
  have hrp : 0 < r := by linarith
  have heq : v+(r-1)^2/G = v*r := by dsimp [v]; ring
  have hlow (i : Fin k) : 1/r ≤ atten v (x i) := by
    apply (div_le_div_iff₀ hrp (show 0 < v+x i by linarith [(hx i).1])).2
    nlinarith [(hx i).2]
  have cov : poleScale*w ≤ 2/r := (le_div_iff₀ hrp).2 hcover
  have hp (i j : Fin k) : poleScale*(w*w) ≤ w*atten v (x j)+w*atten v (x i) := by
    have hh : 2/r ≤ atten v (x j)+atten v (x i) := by
      have ez : 2/r = 1/r+1/r := by ring
      rw [ez]; exact add_le_add (hlow j) (hlow i)
    have hh' := mul_le_mul_of_nonneg_left (cov.trans hh) hw.le
    linarith only [hh']
  have hnet := cancel_scaled hv (fun i => (hx i).1) (b := fun _ => w)
    (fun _ => hw.le) hp hbudget
  have each (i : Fin k) : w/(v+A) ≤ w/(v+x i) :=
    div_le_div_of_nonneg_left hw.le (by linarith [(hx i).1]) (by linarith [(hx i).2])
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun i _ => each i)
  have hbound : (k : ℝ)*(w/(v+A)) ≤ 1/v+G+e := by
    simpa using hsum.trans hnet
  rw [← mul_div_assoc,hcount] at hbound
  have hbound' := (div_le_iff₀ (show 0 < v+A by linarith)).mp hbound
  change (v+A)*(1/v+G+e) < r^2 at hgap
  nlinarith

/-- For the real-trace square choose r⁴=2k and w=2/r². -/
theorem selfDual_count_barrier {k : ℕ} {r G A : ℝ} (hr : 1 < r)
    (hk : 2*(k : ℝ) = r^4) (hG : 0 < G) (hA : 0 ≤ A)
    (hsmall : A < (r-1)^2/G) :
    ∃ e : ℝ, 0 < e ∧ ∀ x y : Fin k → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ A) →
      ¬ scaledBudget (1/2) ((r-1)/G) G e x y (fun _ => 2/r^2) := by
  have hrp : 0 < r := by linarith
  apply scaled_count_barrier hr (by positivity) _ _ hG hA hsmall
  · rw [← mul_div_assoc, mul_comm (k : ℝ), hk]
    field_simp
  · have eq : (1/2:ℝ)*(2/r^2)*r = 1/r := by field_simp
    rw [eq]
    apply (div_le_iff₀ hrp).2
    linarith

end ERH.Occupation
#print axioms ERH.Occupation.energy_bound
#print axioms ERH.Occupation.strict_count_barrier
#print axioms ERH.Occupation.eventual_cluster_exclusion
#print axioms ERH.Occupation.subpower_radius
#print axioms ERH.Occupation.two_occurrences_constant
#print axioms ERH.Occupation.selfDual_count_barrier
