import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The real kernel on the normalized edge coordinates and its multiplicity budget. -/
namespace EdgeDisks

/-- The real part of 1/(v+x+iy), where x is inward horizontal displacement. -/
noncomputable def poisson (v x y : ℝ) : ℝ := (v+x) / ((v+x)^2+y^2)

/-- The Poisson kernel has a uniform lower bound on the half-disk. -/
theorem halfDisk_lower {v R x y : ℝ} (hv : 0 < v) (hx : 0 ≤ x)
    (hR : 0 ≤ R) (hRv : R ≤ v) (hd : x^2+y^2 ≤ R^2) :
    1/(v+R) ≤ poisson v x y := by
  have hxR : x ≤ R := by nlinarith [sq_nonneg y, sq_nonneg (x-R)]
  have hvx : 0 < v+x := by linarith
  have den : 0 < (v+x)^2+y^2 := by positivity
  unfold poisson
  apply (div_le_div_iff₀ (by linarith : 0 < v+R) den).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hxR) (sub_nonneg.mpr hRv)]

/-- List all candidate zeros with multiplicities (an index need not designate a distinct point).
A kernel budget for these indices bounds their exact cardinality. -/
theorem disk_count {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    {v R B : ℝ} (hv : 0 < v) (hR : 0 ≤ R) (hRv : R ≤ v)
    (inside : ∀ i ∈ s, 0 ≤ x i ∧ (x i)^2+(y i)^2 ≤ R^2)
    (budget : ∑ i ∈ s, poisson v (x i) (y i) ≤ B) :
    (s.card : ℝ) ≤ (v+R)*B := by
  have h := Finset.sum_le_sum fun i hi =>
    halfDisk_lower hv (inside i hi).1 hR hRv (inside i hi).2
  have hsum : (s.card : ℝ) / (v+R) ≤ B := by
    simpa [div_eq_mul_inv] using h.trans budget
  simpa [mul_comm] using (div_le_iff₀ (by linarith : 0 < v+R)).mp hsum

/-- Optimize the limiting integer count. For P=1 the static pole alone forbids a
one-zero exclusion, but permits radii (sqrt m-1)^2/C for m=2,3,4. -/
theorem optimized_barrier {r C : ℝ} (hr : 1 < r) (hC : 0 < C) :
    ((r-1)/C + (r-1)^2/C) * (1/((r-1)/C)+C) = r^2 := by
  have h : r-1 ≠ 0 := by linarith
  field_simp
  ring

/-- An explicit positive margin absorbs an unknown analytic remainder. -/
theorem below_barrier {r C R : ℝ} (hr : 1 < r) (hC : 0 < C)
    (hR : 0 ≤ R) (hsmall : R < (r-1)^2/C) :
    ∃ e : ℝ, 0 < e ∧
      ((r-1)/C+R) * (1/((r-1)/C)+C+e) < r^2 := by
  let v := (r-1)/C
  have hv : 0 < v := div_pos (sub_pos.mpr hr) hC
  have ht : 0 < 1/v+C := by positivity
  have hd : 0 < v+R := by linarith
  have hstrict : (v+R)*(1/v+C) < r^2 := by
    calc
      _ < (v+(r-1)^2/C)*(1/v+C) := mul_lt_mul_of_pos_right (by linarith) ht
      _ = r^2 := optimized_barrier hr hC
  refine ⟨(r^2-(v+R)*(1/v+C))/(2*(v+R)), by positivity, ?_⟩
  change (v+R)*(1/v+C+(r^2-(v+R)*(1/v+C))/(2*(v+R))) < r^2
  rw [mul_add]
  have heq : (v+R)*((r^2-(v+R)*(1/v+C))/(2*(v+R))) =
      (r^2-(v+R)*(1/v+C))/2 := by field_simp
  rw [heq]
  linarith

/-- Moving the center to a zero removes the vertical-disk restriction.
This covers any multiplicity in the general P-budget. -/
theorem onAxis_lower {v R x : ℝ} (hv : 0 < v) (hx : 0 ≤ x) (hxR : x ≤ R) :
    1/(v+R) ≤ poisson v x 0 := by
  have hpos : 0 < v+x := by linarith
  have heq : poisson v x 0 = 1/(v+x) := by unfold poisson; field_simp; ring
  rw [heq]
  exact one_div_le_one_div_of_le hpos (by linarith)

/-- Exact optimizer with an arbitrary static pole P=p² and multiplicity m=r². -/
theorem general_barrier {p r C : ℝ} (_hp : 0 < p) (hpr : p < r) (hC : 0 < C) :
    let v := p*(r-p)/C
    (v+(r-p)^2/C)*(p^2/v+C)=r^2 := by
  dsimp
  have h : r-p ≠ 0 := by linarith
  field_simp
  ring

/-- The analytic input is a uniform Poisson-sum budget for a prescribed number of
zeros. The conclusion limits *all* finite subsets in the half-disk at large heights.
The height parameter is real, so this includes every sequence of ordinates. -/
theorem eventual_disk_exclusion {ι : Type*} (m : ℕ) {r C R : ℝ}
    (hr : 1 < r) (hr2 : r ≤ 2) (hm : (m : ℝ) = r^2)
    (hC : 0 < C) (hR : 0 ≤ R) (hsmall : R < (r-1)^2/C)
    (eligible : ℝ → ι → Prop) (x y : ℝ → ι → ℝ)
    (budget : ∀ e : ℝ, 0 < e → ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ s : Finset ι,
      s.card = m → (∀ i ∈ s, eligible T i) →
      ∑ i ∈ s, poisson ((r-1)/C) (x T i) (y T i) ≤ 1/((r-1)/C)+C+e) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ s : Finset ι,
      (∀ i ∈ s, eligible T i ∧ 0 ≤ x T i ∧ (x T i)^2+(y T i)^2 ≤ R^2) →
      s.card < m := by
  obtain ⟨e, he, hgap⟩ := below_barrier hr hC hR hsmall
  obtain ⟨T₀, hT₀⟩ := budget e he
  refine ⟨T₀, ?_⟩
  intro T hT s hs
  by_contra! hcard
  obtain ⟨t, hts, htm⟩ := Finset.exists_subset_card_eq hcard
  have hv : 0 < (r-1)/C := div_pos (sub_pos.mpr hr) hC
  have hrR : R ≤ (r-1)/C := by
    apply le_trans hsmall.le
    apply div_le_div_of_nonneg_right _ hC.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.le) (sub_nonneg.mpr hr2)]
  have h := disk_count t (x T) (y T) hv hR hrR
      (fun i hi => (hs i (hts hi)).2)
      (hT₀ T hT t htm (fun i hi => (hs i (hts hi)).1))
  rw [htm, hm] at h
  exact (not_lt_of_ge h) hgap

end EdgeDisks
