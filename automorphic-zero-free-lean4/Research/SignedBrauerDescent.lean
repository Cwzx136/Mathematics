import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sign-sensitive descent for meromorphic divisors

Positive integer order means a zero and negative order a pole. All equalities of
meromorphic functions below are equalities on punctured neighborhoods. Thus a
pointwise value picked for Lean's totalized inverse at a pole is irrelevant.
-/

open Filter
open scoped Topology BigOperators

namespace SignedBrauerDescent

variable {ι : Type*}

/-- An entire function that is not the zero function has finite order at each point. -/
theorem finite_order_of_entire {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (hne : f ≠ 0) (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ := by
  rw [(hf z).meromorphicOrderAt_eq]
  have ha : analyticOrderAt f z ≠ ⊤ :=
    fun h => hne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hf).mp h)
  cases h : analyticOrderAt f z with
  | top => exact (ha h).elim
  | coe n => simp

/-- The exact signed multiplicity identity, with any analytic unit correction. -/
theorem signedOrder {s : Finset ι} {f : ι → ℂ → ℂ} {F u : ℂ → ℂ}
    {n m : ι → ℤ} {z : ℂ} (hu : AnalyticAt ℂ u z) (hunit : u z ≠ 0)
    (hfac : F =ᶠ[𝓝[≠] z] u * (∏ i ∈ s, f i ^ n i))
    (hf : ∀ i ∈ s, MeromorphicAt (f i) z)
    (hm : ∀ i ∈ s, meromorphicOrderAt (f i) z = (m i : WithTop ℤ)) :
    meromorphicOrderAt F z = ((∑ i ∈ s, n i * m i : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_congr hfac, meromorphicOrderAt_mul_of_ne_zero hu hunit,
    meromorphicOrderAt_prod (fun i hi => (hf i hi).zpow (n i)), WithTop.coe_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [meromorphicOrderAt_zpow (hf i hi), hm i hi, WithTop.coe_mul]

/-- A rational Brauer relation is read after clearing its positive denominator.
The equality of local orders also proves finite order of the target. -/
theorem signedOrder_power {s : Finset ι} {f : ι → ℂ → ℂ} {F u : ℂ → ℂ}
    {n m : ι → ℤ} {z : ℂ} {N : ℕ} (hN : 0 < N) (hF : MeromorphicAt F z)
    (hu : AnalyticAt ℂ u z) (hunit : u z ≠ 0)
    (hfac : F ^ N =ᶠ[𝓝[≠] z] u * (∏ i ∈ s, f i ^ n i))
    (hf : ∀ i ∈ s, MeromorphicAt (f i) z)
    (hm : ∀ i ∈ s, meromorphicOrderAt (f i) z = (m i : WithTop ℤ)) :
    ∃ a : ℤ, meromorphicOrderAt F z = (a : WithTop ℤ) ∧
      (N : ℤ) * a = ∑ i ∈ s, n i * m i := by
  have hp := signedOrder hu hunit hfac hf hm
  rw [meromorphicOrderAt_pow hF] at hp
  cases ho : meromorphicOrderAt F z with
  | top =>
    rw [ho] at hp
    rw [WithTop.mul_top (by exact_mod_cast Nat.ne_of_gt hN)] at hp
    exact (WithTop.top_ne_coe hp).elim
  | coe a =>
    refine ⟨a, rfl, ?_⟩
    rw [ho] at hp
    exact_mod_cast hp

/-- A real-part distance to the nearer edge of the *open* unitary critical strip. -/
def InEdge (c d : ℝ) (z : ℂ) : Prop :=
  0 < z.re ∧ z.re < 1 ∧
  min z.re (1 - z.re) ≤ 1 / (c * d * Real.log |z.im|)

theorem inEdge_of_degree_le {c d D : ℝ} {z : ℂ}
    (hc : 0 < c) (hd : 0 < d) (hD : d ≤ D) (ht : 1 < |z.im|)
    (hz : InEdge c D z) : InEdge c d z := by
  obtain ⟨h₀, h₁, hw⟩ := hz
  have hl := Real.log_pos ht
  refine ⟨h₀, h₁, hw.trans (one_div_le_one_div_of_le (by positivity) ?_)⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hc.le) hl.le

/-- The maximum with one handles an empty selected set of constituents. -/
noncomputable def maxDegree (s : Finset ι) (d : ι → ℕ) : ℕ := max 1 (s.sup d)

theorem degree_le_maxDegree {s : Finset ι} (d : ι → ℕ) {i : ι} (hi : i ∈ s) :
    d i ≤ maxDegree s d := (Finset.le_sup hi).trans (le_max_right _ _)

/-- At high ordinates one needs the zero-free region of positive exponents to
exclude zeros and that of negative exponents to exclude poles. The other
constituents are entire and may vanish. `hfac` may include local correction units. -/
theorem signedEdges
    (s : Finset ι) (f : ι → ℂ → ℂ) (n : ι → ℤ) (d H : ι → ℕ)
    (c : ℝ) (hc : 0 < c) (hd : ∀ i ∈ s, 0 < d i)
    (ha : ∀ i ∈ s, ∀ z, AnalyticAt ℂ (f i) z) (hneq : ∀ i ∈ s, f i ≠ 0)
    (hfree : ∀ i ∈ s, ∀ z : ℂ, (H i : ℝ) ≤ |z.im| →
      InEdge c (d i) z → f i z ≠ 0)
    (F u : ℂ → ℂ) (z : ℂ) (ht : 1 < |z.im|)
    (hu : AnalyticAt ℂ u z) (hunit : u z ≠ 0)
    (hfac : F =ᶠ[𝓝[≠] z] u * (∏ i ∈ s, f i ^ n i)) :
    let pos := s.filter (fun i => 0 < n i)
    let neg := s.filter (fun i => n i < 0)
    (((pos.sup H : ℕ) : ℝ) ≤ |z.im| → InEdge c (maxDegree pos d) z →
      meromorphicOrderAt F z ≤ 0) ∧
    (((neg.sup H : ℕ) : ℝ) ≤ |z.im| → InEdge c (maxDegree neg d) z →
      0 ≤ meromorphicOrderAt F z) := by
  classical
  let m : ι → ℤ := fun i => (meromorphicOrderAt (f i) z).untop₀
  have hm (i : ι) (hi : i ∈ s) : meromorphicOrderAt (f i) z = (m i : WithTop ℤ) :=
    (WithTop.coe_untop₀_of_ne_top (finite_order_of_entire (ha i hi) (hneq i hi) z)).symm
  have hn (i : ι) (hi : i ∈ s) : 0 ≤ m i := by
    apply WithTop.coe_nonneg.mp
    rw [← hm i hi]
    exact (ha i hi z).meromorphicOrderAt_nonneg
  have hF := signedOrder hu hunit hfac (fun i hi => (ha i hi z).meromorphicAt) hm
  have hzero (A : Finset ι) (hA : ((A.sup H : ℕ) : ℝ) ≤ |z.im|)
      (hE : InEdge c (maxDegree A d) z) (i : ι) (hi : i ∈ s)
      (hia : i ∈ A) : m i = 0 := by
    have hregion : InEdge c (d i) z := inEdge_of_degree_le hc
      (by exact_mod_cast hd i hi) (by exact_mod_cast degree_le_maxDegree d hia) ht hE
    have hT : (H i : ℝ) ≤ |z.im| := by
      apply le_trans _ hA
      exact_mod_cast (Finset.le_sup (f := H) hia)
    have hv := (ha i hi z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (hfree i hi z hT hregion)
    have heq : (m i : WithTop ℤ) = ((0:ℤ) : WithTop ℤ) := (hm i hi).symm.trans hv
    exact WithTop.coe_injective heq
  constructor
  · intro hH he
    rw [hF]
    apply WithTop.coe_le_coe.mpr
    apply Finset.sum_nonpos
    intro i hi
    by_cases hp : 0 < n i
    · rw [hzero _ hH he i hi (Finset.mem_filter.mpr ⟨hi, hp⟩), mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hp) (hn i hi)
  · intro hH he
    rw [hF]
    apply WithTop.coe_nonneg.mpr
    apply Finset.sum_nonneg
    intro i hi
    by_cases hp : n i < 0
    · rw [hzero _ hH he i hi (Finset.mem_filter.mpr ⟨hi, hp⟩), mul_zero]
    · exact mul_nonneg (le_of_not_gt hp) (hn i hi)


/-- The zero count and the pole count of a signed product are separately bounded
by the positive and negative coefficient budgets, at any finite set of points.
Both bounds count multiplicities. The local hypotheses use a finite integer
order for each analytic constituent, which follows from `finite_order_of_entire`
for a non-identically-zero entire function. -/
theorem finiteDivisorBudgets (s : Finset ι) (P : Finset ℂ)
    (f : ι → ℂ → ℂ) (F u : ℂ → ℂ) (n : ι → ℤ) (m : ι → ℂ → ℤ)
    (hu : ∀ z ∈ P, AnalyticAt ℂ u z) (hunit : ∀ z ∈ P, u z ≠ 0)
    (hfac : ∀ z ∈ P, F =ᶠ[𝓝[≠] z] u * (∏ i ∈ s, f i ^ n i))
    (hf : ∀ z ∈ P, ∀ i ∈ s, MeromorphicAt (f i) z)
    (hm : ∀ z ∈ P, ∀ i ∈ s, meromorphicOrderAt (f i) z = (m i z : WithTop ℤ))
    (hn : ∀ z ∈ P, ∀ i ∈ s, 0 ≤ m i z) :
    (∑ z ∈ P, max (meromorphicOrderAt F z).untop₀ 0) ≤
        ∑ i ∈ s, max (n i) 0 * ∑ z ∈ P, m i z ∧
    (∑ z ∈ P, max (-(meromorphicOrderAt F z).untop₀) 0) ≤
        ∑ i ∈ s, max (-n i) 0 * ∑ z ∈ P, m i z := by
  have hord (z : ℂ) (hz : z ∈ P) :
      (meromorphicOrderAt F z).untop₀ = ∑ i ∈ s, n i * m i z := by
    rw [signedOrder (hu z hz) (hunit z hz) (hfac z hz) (hf z hz) (hm z hz)]
    rfl
  have bound (a : ι → ℤ) (z : ℂ) (hz : z ∈ P) :
      max (∑ i ∈ s, a i * m i z) 0 ≤ ∑ i ∈ s, max (a i) 0 * m i z :=
    max_le (Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right
      (le_max_left _ _) (hn z hz i hi))) (Finset.sum_nonneg (fun i hi =>
      mul_nonneg (le_max_right _ _) (hn z hz i hi)))
  constructor
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun z hz => (hord z hz) ▸ bound n z hz)
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro z hz
    rw [hord z hz, ← Finset.sum_neg_distrib]
    simpa only [neg_mul] using bound (fun i => -n i) z hz

/-- A concrete height above which a shrinking edge region avoids a finite set
of vertical lines. Values outside the open strip are harmless in the maximum. -/
noncomputable def correctionHeight (B : Finset ℝ) (c d : ℝ) : ℝ :=
  let vals := insert 2 (B.image (fun b => Real.exp (1 / (c*d*min b (1-b)) + 1)))
  vals.max' ⟨2, Finset.mem_insert_self _ _⟩

theorem fixedLinesMiss {B : Finset ℝ} {c d : ℝ} {z : ℂ}
    (hc : 0 < c) (hd : 0 < d) (hT : correctionHeight B c d ≤ |z.im|)
    (hE : InEdge c d z) : z.re ∉ B := by
  classical
  intro hb
  obtain ⟨h₀, h₁, hw⟩ := hE
  have hm : 0 < min z.re (1-z.re) := lt_min h₀ (sub_pos.mpr h₁)
  let vals := insert (2:ℝ) (B.image (fun b => Real.exp (1 / (c*d*min b (1-b))+1)))
  have h₂ : (2:ℝ) ≤ |z.im| :=
    le_trans (vals.le_max' 2 (Finset.mem_insert_self _ _)) hT
  have hExp : Real.exp (1/(c*d*min z.re (1-z.re))+1) ≤ |z.im| :=
    le_trans (vals.le_max' _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ hb))) hT
  have ht : 1 < |z.im| := lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) h₂
  have hl := Real.log_pos ht
  have hlog := (Real.le_log_iff_exp_le (lt_trans zero_lt_one ht)).mpr hExp
  have hstrict : 1/(c*d*min z.re (1-z.re)) < Real.log |z.im| := by linarith
  have hh := (div_lt_iff₀ (mul_pos (mul_pos hc hd) hm)).mp hstrict
  have hsmall := (le_div_iff₀ (mul_pos (mul_pos hc hd) hl)).mp hw
  linarith only [hh, show Real.log |z.im| * (c*d*min z.re (1-z.re)) ≤ 1 by
    convert hsmall using 1; ring]

/-- Every root of a local Euler factor has an explicitly fixed real part. -/
theorem eulerFactorRoot {α : ℂ} {q : ℝ} {z : ℂ} (ha : α ≠ 0) (hq : 1 < q)
    (hz : 1 - α * Complex.exp (-z * (Real.log q : ℂ)) = 0) :
    z.re = Real.log ‖α‖ / Real.log q := by
  have hmul := (sub_eq_zero.mp hz).symm
  have hnorm := congrArg (fun x : ℂ => ‖x‖) hmul
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, norm_one] at hnorm
  have hExp : Real.exp (Real.log ‖α‖ + (-z.re) * Real.log q) = Real.exp 0 := by
    rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr ha), Real.exp_zero]
    exact hnorm
  have he := Real.exp_injective hExp
  apply (eq_div_iff (Real.log_pos hq).ne').mpr
  linarith


/-- When both sign bounds apply, the canonical meromorphic representative is
holomorphic and has nonzero value at the point. -/
theorem unit_of_two_bounds {F : ℂ → ℂ} {z : ℂ} (hF : MeromorphicNFAt F z)
    (hzero : meromorphicOrderAt F z ≤ 0) (hpole : 0 ≤ meromorphicOrderAt F z) :
    AnalyticAt ℂ F z ∧ F z ≠ 0 :=
  ⟨hF.meromorphicOrderAt_nonneg_iff_analyticAt.mp hpole,
   hF.meromorphicOrderAt_eq_zero_iff.mp (le_antisymm hzero hpole)⟩

/-- A finite correction by actual Euler factors with arbitrary integer exponents
is a holomorphic unit in the high edge regions. -/
theorem eulerCorrection (b : Finset ι) (α : ι → ℂ) (q : ι → ℝ) (n : ι → ℤ)
    (ha : ∀ i ∈ b, α i ≠ 0) (hq : ∀ i ∈ b, 1 < q i)
    {c d : ℝ} {z : ℂ} (hc : 0 < c) (hd : 0 < d)
    (hT : correctionHeight (b.image (fun i => Real.log ‖α i‖ / Real.log (q i))) c d ≤ |z.im|)
    (hE : InEdge c d z) :
    let u := fun w : ℂ => ∏ i ∈ b, (1 - α i * Complex.exp (-w * (Real.log (q i) : ℂ))) ^ n i
    AnalyticAt ℂ u z ∧ u z ≠ 0 := by
  classical
  have hline := fixedLinesMiss hc hd hT hE
  have hn (i : ι) (hi : i ∈ b) :
      1 - α i * Complex.exp (-z * (Real.log (q i) : ℂ)) ≠ 0 := by
    intro h
    exact hline (eulerFactorRoot (ha i hi) (hq i hi) h ▸ Finset.mem_image_of_mem _ hi)
  constructor
  · apply Finset.analyticAt_fun_prod
    intro i hi
    have fac : AnalyticAt ℂ (fun w : ℂ => 1 - α i * Complex.exp (-w * (Real.log (q i) : ℂ))) z := by
      fun_prop
    exact fac.zpow (n := n i) (hn i hi)
  · exact Finset.prod_ne_zero_iff.mpr (fun i hi => zpow_ne_zero _ (hn i hi))

#print axioms eulerCorrection
#print axioms unit_of_two_bounds
#print axioms finiteDivisorBudgets
#print axioms fixedLinesMiss
#print axioms eulerFactorRoot
#print axioms finite_order_of_entire
#print axioms signedOrder
#print axioms signedOrder_power
#print axioms inEdge_of_degree_le
#print axioms signedEdges

end SignedBrauerDescent
