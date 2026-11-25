import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A sharp single-shift version of the paired Stechkin inequalities.
The center coordinates are m = σ−1/2 and x = β−1/2. -/
namespace ERH.Stechkin
noncomputable section

/-- Real part of the reciprocal at horizontal separation a and vertical separation t. -/
def atom (a t : ℝ) : ℝ := a / (a^2+t^2)

/-- Contributions from two horizontal reflections of the same zero. -/
def pair (m x t : ℝ) : ℝ := atom (m-x) t + atom (m+x) t

/-- All paired contributions are nonnegative, and at the target ordinate
one whole target pole survives the subtraction. -/
def Admissible (m n k : ℝ) : Prop :=
  (∀ x t : ℝ, -(1/2 : ℝ) ≤ x → x ≤ 1/2 → k * pair n x t ≤ pair m x t) ∧
  (∀ x : ℝ, 0 ≤ x → x ≤ 1/2 → 1/(m-x) + k * pair n x 0 ≤ pair m x 0)

private theorem sqBound {x : ℝ} (hl : -(1 / 2 : ℝ) ≤ x) (hu : x ≤ 1/2) :
    x^2 ≤ 1/4 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ 1/2+x by linarith)]

private theorem shape {m x t : ℝ} (hm : 1/2 < m)
    (hl : -(1 / 2 : ℝ) ≤ x) (hu : x ≤ 1/2) :
    pair m x t = 2*m*(m^2-x^2+t^2) / ((m^2-x^2+t^2)^2+4*x^2*t^2) := by
  have h1 : 0 < m-x := by linarith
  have h2 : 0 < m+x := by linarith
  have h3 : 0 < m^2-x^2+t^2 := by nlinarith [mul_pos h1 h2, sq_nonneg t]
  have d1 : 0 < (m-x)^2+t^2 := by positivity
  have d2 : 0 < (m+x)^2+t^2 := by positivity
  have d3 : 0 < (m^2-x^2+t^2)^2+4*x^2*t^2 := by positivity
  unfold pair atom
  field_simp [ne_of_gt d1, ne_of_gt d2, ne_of_gt d3]
  ring

private theorem atom_zero {a : ℝ} (ha : 0 < a) : atom a 0 = 1/a := by
  unfold atom
  simp only [zero_pow (by decide : 2 ≠ 0), add_zero]
  field_simp

private theorem pair_nonneg {n x t : ℝ} (hn : 1/2 < n)
    (hl : -(1 / 2 : ℝ) ≤ x) (hu : x ≤ 1/2) : 0 ≤ pair n x t := by
  have h1 : 0 < n-x := by linarith
  have h2 : 0 < n+x := by linarith
  unfold pair atom
  positivity

/-- Positivity after multiplication of the outer pair by the central-distance ratio. -/
theorem pair_scaled {m n x t : ℝ} (hm : 1/2 < m) (hmn : m ≤ n)
    (hsum : 3/2 ≤ m^2+n^2) (hl : -(1/2 : ℝ) ≤ x) (hu : x ≤ 1/2) :
    m / n * pair n x t ≤ pair m x t := by
  have hn : 1/2 < n := lt_of_lt_of_le hm hmn
  have mn : 0 < m := by linarith
  have nn : 0 < n := by linarith
  let X := m^2-x^2+t^2
  let Y := n^2-x^2+t^2
  let C := 4*x^2*t^2
  have b1 : 0 < m^2-x^2 := by
    nlinarith [mul_pos (show 0 < m-x by linarith) (show 0 < m+x by linarith)]
  have b2 : 0 < n^2-x^2 := by
    nlinarith [mul_pos (show 0 < n-x by linarith) (show 0 < n+x by linarith)]
  have hX : 0 < X := by dsimp [X]; nlinarith [sq_nonneg t]
  have hY : 0 < Y := by dsimp [Y]; nlinarith [sq_nonneg t]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hXY : X ≤ Y := by
    dsimp [X,Y]; nlinarith [mul_nonneg (sub_nonneg.mpr hmn) (show 0 ≤ n+m by linarith)]
  have hCO : 0 ≤ m^2+n^2-6*x^2 := by linarith [sqBound hl hu]
  have hXC : 0 ≤ X*Y-C := by
    dsimp [X,Y,C]
    nlinarith [mul_pos b1 b2, mul_nonneg hCO (sq_nonneg t), sq_nonneg (t^2)]
  have hratio : Y/(Y^2+C) ≤ X/(X^2+C) := by
    apply (div_le_div_iff₀ (by positivity : 0 < Y^2+C) (by positivity : 0 < X^2+C)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hXY) hXC]
  rw [shape hn hl hu, shape hm hl hu]
  change m/n*(2*n*Y/(Y^2+C)) ≤ 2*m*X/(X^2+C)
  calc
    m/n*(2*n*Y/(Y^2+C)) = (2*m)*(Y/(Y^2+C)) := by field_simp
    _ ≤ (2*m)*(X/(X^2+C)) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

/-- Two scalar inequalities suffice for all zeros and for the target zero. -/
theorem admissible_of_bounds {m n k : ℝ} (hm : 1/2 < m) (hmn : m ≤ n)
    (hsum : 3/2 ≤ m^2+n^2) (hk : 0 ≤ k)
    (hinf : k*n ≤ m) (htarget : k*(2*n)*(m+1/2) ≤ n^2-1/4) :
    Admissible m n k := by
  have hn : 1/2 < n := lt_of_lt_of_le hm hmn
  have nn : 0 < n := by linarith
  constructor
  · intro x t hl hu
    calc
      k * pair n x t ≤ (m/n) * pair n x t :=
        mul_le_mul_of_nonneg_right ((le_div_iff₀ nn).2 hinf) (pair_nonneg hn hl hu)
      _ ≤ _ := pair_scaled hm hmn hsum hl hu
  · intro x hx hu
    have hl : -(1/2 : ℝ) ≤ x := by linarith
    have a : 0 < m-x := by linarith
    have b : 0 < m+x := by linarith
    have c : 0 < n-x := by linarith
    have d : 0 < n+x := by linarith
    have h : k*(2*n)*(m+x) ≤ n^2-x^2 := by
      linarith [mul_le_mul_of_nonneg_left (show m+x ≤ m+1/2 by linarith)
             (show 0 ≤ k*(2*n) by positivity), sqBound hl hu]
    unfold pair
    rw [atom_zero a,atom_zero b,atom_zero c,atom_zero d]
    apply add_le_add_right
    have hr : 1/(n-x)+1/(n+x) = (2*n)/((n-x)*(n+x)) := by
      field_simp; ring
    rw [hr, ← mul_div_assoc]
    apply (div_le_div_iff₀ (mul_pos c d) b).2
    nlinarith

/-- Best outer distance among all single shifts in this two-requirement problem. -/
noncomputable def optimalOuter (m : ℝ) : ℝ := Real.sqrt (2*m^2+m+1/4)

theorem optimalOuter_sq {m : ℝ} (hm : 1/2 < m) :
    (optimalOuter m)^2 = 2*m^2+m+1/4 := by
  apply Real.sq_sqrt
  nlinarith [sq_nonneg m]

theorem optimalOuter_gt {m : ℝ} (hm : 1/2 < m) : m < optimalOuter m := by
  have hj := optimalOuter_sq hm
  have hn : 0 ≤ optimalOuter m := Real.sqrt_nonneg _
  nlinarith [sq_nonneg m, mul_nonneg (show 0 ≤ m by linarith) hn,
    sq_nonneg (optimalOuter m-m)]

/-- The optimized variable weight works at every vertical displacement. -/
theorem optimal_admissible {m : ℝ} (hm : 1/2 < m) :
    Admissible m (optimalOuter m) (m/optimalOuter m) := by
  have ho := optimalOuter_gt hm
  have hs := optimalOuter_sq hm
  have hn : 0 < optimalOuter m := by linarith
  have hp : 0 < m := by linarith
  apply admissible_of_bounds hm (le_of_lt ho)
  · nlinarith [sq_nonneg (m-1/2)]
  · positivity
  · exact le_of_eq (div_mul_cancel₀ _ (ne_of_gt hn))
  · field_simp
    nlinarith

/-- Explicit link between the real expression and the real part of a complex reciprocal. -/
theorem atom_eq_reciprocal (a t : ℝ) :
    atom a t = ((⟨a,t⟩ : ℂ)⁻¹).re := by
  simp only [atom, Complex.inv_re, Complex.normSq_apply, pow_two]

/-- For σ>1 the optimized weight is strictly greater than the traditional uniform value. -/
theorem optimal_weight_improves {m : ℝ} (hm : 1/2 < m) :
    1 / Real.sqrt 5 < m / optimalOuter m := by
  have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have h5s := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hN := optimalOuter_gt hm
  have hNs := optimalOuter_sq hm
  apply (div_lt_div_iff₀ h5 (by linarith : 0 < optimalOuter m)).2
  have hs : (optimalOuter m)^2 < (m*Real.sqrt 5)^2 := by
    rw [mul_pow, h5s, hNs]
    nlinarith [mul_pos (show 0 < m-1/2 by linarith) (show 0 < 3*m+1/2 by linarith)]
  have hp : 0 < m*Real.sqrt 5 := mul_pos (by linarith) h5
  nlinarith [sq_nonneg (m*Real.sqrt 5 - optimalOuter m)]

/-- Kadiri's classical parameters with σ=m+1/2. -/
theorem classical_admissible {m : ℝ} (hm : 1/2 < m) :
    Admissible m (Real.sqrt ((m+1/2)^2+1/4)) (1/Real.sqrt 5) := by
  let n := Real.sqrt ((m+1/2)^2+1/4)
  have ns : n^2=(m+1/2)^2+1/4 := Real.sq_sqrt (by positivity)
  have hp : 0 < m := by linarith
  have hn : 0 < n := Real.sqrt_pos.2 (by positivity)
  have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hn1 : n ≤ m*Real.sqrt 5 := by
    have haux : n^2 ≤ (m*Real.sqrt 5)^2 := by
      rw [ns, mul_pow, hs5]
      nlinarith [mul_nonneg (show 0 ≤ m-1/2 by linarith) (show 0 ≤ 4*m+1 by linarith)]
    exact le_of_sq_le_sq haux (by positivity)
  have hn2 : 2*n ≤ (m+1/2)*Real.sqrt 5 := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, ns, mul_pow, hs5]
    nlinarith [sq_nonneg (m-1/2)]
  apply admissible_of_bounds hm (n := n)
  · apply le_of_sq_le_sq _ (le_of_lt hn)
    rw [ns]; nlinarith
  · rw [ns]; nlinarith [sq_nonneg (m-1/2)]
  · positivity
  · rw [div_mul_eq_mul_div, one_mul]
    exact (div_le_iff₀ h5).2 hn1
  · rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ h5, ns]
    nlinarith [mul_le_mul_of_nonneg_right hn2 (show 0 ≤ m+1/2 by linarith)]

/-- Reciprocal pair at the boundary, at exactly the target height. -/
def boundary (n : ℝ) : ℝ := 1/(n-1/2)+1/(n+1/2)

private theorem boundary_pos {n : ℝ} (hn : 1/2 < n) : 0 < boundary n := by
  have a : 0 < n-1/2 := by linarith
  have b : 0 < n+1/2 := by linarith
  unfold boundary
  positivity

/-- The full subtracted pole pair removes exactly the original companion pole. -/
theorem saturates_boundary {m : ℝ} (hm : 1/2 < m) :
    (m/optimalOuter m)*boundary (optimalOuter m) = 1/(m+1/2) := by
  let N := optimalOuter m
  have hm' : 0 < m := by linarith
  have hN : m < N := optimalOuter_gt hm
  have hN' : 0 < N := by linarith
  have h1 : 0 < N-1/2 := by linarith
  have h2 : 0 < N+1/2 := by linarith
  have h3 : 0 < m+1/2 := by linarith
  have he : (N-1/2)*(N+1/2)=2*m*(m+1/2) := by
    nlinarith [show N^2=2*m^2+m+1/4 from optimalOuter_sq hm]
  change (m/N)*boundary N=_
  have hf0 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      1/a + 1/b = (b+a)/(a*b) := by field_simp
  have hf : boundary N = (2*N)/((N-1/2)*(N+1/2)) := by
    unfold boundary
    rw [hf0 _ _ h1 h2]
    ring
  rw [hf,he]
  field_simp

private def tangentSlope (N : ℝ) := 1/(N-1/2)^2+1/(N+1/2)^2

private theorem reciprocal_tangent {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    1/a+(a-x)/a^2 ≤ 1/x := by
  field_simp
  nlinarith [sq_nonneg (a-x)]

private theorem boundary_tangent {N n : ℝ} (hN : 1/2 < N) (hn : 1/2 < n) :
    boundary N + tangentSlope N*N ≤ boundary n + tangentSlope N*n := by
  have h1 := reciprocal_tangent (a:=N-1/2) (x:=n-1/2) (by linarith) (by linarith)
  have h2 := reciprocal_tangent (a:=N+1/2) (x:=n+1/2) (by linarith) (by linarith)
  unfold boundary tangentSlope
  simp only [div_eq_mul_inv] at h1 h2 ⊢
  linarith

/-- Exact finite-dimensional upper bound for any collection of positive shifts satisfying
the two moment bounds forced by the kernel inequalities. -/
theorem mixture_weight_of_moments {ι : Type*} (s : Finset ι) (w n : ι → ℝ)
    {m : ℝ} (hm : 1/2 < m) (hw : ∀ i ∈ s, 0 ≤ w i) (hn : ∀ i ∈ s, 1/2 < n i)
    (hinf : ∑ i ∈ s, w i*n i ≤ m)
    (hzero : ∑ i ∈ s, w i*boundary (n i) ≤ 1/(m+1/2)) :
    ∑ i ∈ s, w i ≤ m/optimalOuter m := by
  let N := optimalOuter m
  let A := tangentSlope N
  have hN : m < N := optimalOuter_gt hm
  have hN1 : 1/2 < N := lt_trans hm hN
  have hpos : 0 < N := by linarith
  have a : 0 < N-1/2 := by linarith
  have b : 0 < N+1/2 := by linarith
  have hA : 0 < A := by dsimp [A,tangentSlope]; positivity
  have hB : 0 < boundary N := boundary_pos hN1
  have hline : ∀ i ∈ s, (boundary N+A*N)*w i ≤
                             w i*boundary (n i)+A*(w i*n i) := by
    intro i hi
    have h := mul_le_mul_of_nonneg_right (boundary_tangent hN1 (hn i hi)) (hw i hi)
    change (boundary N + A*N)*w i ≤ (boundary (n i)+A*n i)*w i at h
    linarith
  have hcost : (boundary N+A*N)*(∑ i ∈ s, w i) ≤ 1/(m+1/2)+A*m := calc
    _ = ∑ i ∈ s, (boundary N+A*N)*w i := Finset.mul_sum ..
    _ ≤ ∑ i ∈ s, (w i*boundary (n i)+A*(w i*n i)) := Finset.sum_le_sum hline
    _ = (∑ i ∈ s, w i*boundary (n i))+A*(∑ i ∈ s, w i*n i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add hzero (mul_le_mul_of_nonneg_left hinf (le_of_lt hA))
  have hs : (m/N)*boundary N=1/(m+1/2) := saturates_boundary hm
  have hnM : m/N*N=m := div_mul_cancel₀ _ (ne_of_gt hpos)
  have hid : 1/(m+1/2)+A*m = (boundary N+A*N)*(m/N) := by
    rw [← hs]
    calc
      _ = (m/N)*boundary N + A*((m/N)*N) := by rw [hnM]
      _ = _ := by ring
  rw [hid] at hcost
  exact le_of_mul_le_mul_left hcost (by positivity : 0 < boundary N+A*N)

/-- An admissible finite mixture uses the same two requirements as one shift. -/
def MixtureAdmissible {ι : Type*} (s : Finset ι) (w n : ι → ℝ) (m : ℝ) : Prop :=
  (∀ x t : ℝ, -(1/2 : ℝ) ≤ x → x ≤ 1/2 →
      (∑ i ∈ s, w i*pair (n i) x t) ≤ pair m x t) ∧
  (∀ x : ℝ, 0 ≤ x → x ≤ 1/2 →
      1/(m-x)+(∑ i ∈ s, w i*pair (n i) x 0) ≤ pair m x 0)

private theorem outer_at_boundary {n : ℝ} (hn : 1/2 < n) :
    pair n (1/2) 0 = boundary n := by
  have a : 0 < n-1/2 := by linarith
  have b : 0 < n+1/2 := by linarith
  simp only [pair,boundary,atom_zero a,atom_zero b]

/-- At the boundary the differenced pair retains exactly the singular pole. -/
theorem pole_cancellation {m : ℝ} (hm : 1/2 < m) :
    pair m (1/2) 0 - (m/optimalOuter m)*pair (optimalOuter m) (1/2) 0 = 1/(m-1/2) := by
  rw [outer_at_boundary hm, outer_at_boundary (lt_trans hm (optimalOuter_gt hm)), saturates_boundary hm]
  unfold boundary
  ring

private theorem scaled_center (a Y : ℝ) (hY : 0 < Y) :
    Y/2 * pair a 0 (Real.sqrt Y) = a*Y/(a^2+Y) := by
  unfold pair atom
  rw [sub_zero, add_zero, Real.sq_sqrt (le_of_lt hY)]
  ring

private theorem center_tail {a Y : ℝ} (ha : 0 < a) (hY : 0 < Y) :
    a-a^3/Y ≤ a*Y/(a^2+Y) := by
  have hd : 0 < a^2+Y := by positivity
  field_simp
  nlinarith [show 0 ≤ a^5 by positivity]

/-- The center at large ordinate and the target at the boundary force two budgets on a
mixture. The proof of the first budget is elementary and uniform for each finite set. -/
theorem moments_of_mixture {ι : Type*} (s : Finset ι) (w n : ι → ℝ)
    {m : ℝ} (hm : 1/2 < m) (hw : ∀ i ∈ s, 0 ≤ w i) (hn : ∀ i ∈ s, 1/2 < n i)
    (hh : MixtureAdmissible s w n m) :
    (∑ i ∈ s, w i*n i ≤ m) ∧
    (∑ i ∈ s, w i*boundary (n i) ≤ 1/(m+1/2)) := by
  have hp : 0 < m := by linarith
  constructor
  · let B := ∑ i ∈ s, w i*(n i)^3
    let M := ∑ i ∈ s, w i*n i
    have hB : 0 ≤ B := by
      apply Finset.sum_nonneg
      intro i hi
      have hw' := hw i hi
      have hn' : 0 < n i := by linarith [hn i hi]
      positivity
    have herror (Y : ℝ) (hY : 0 < Y) : M-B/Y ≤ m := by
      have hu := mul_le_mul_of_nonneg_left (hh.1 0 (Real.sqrt Y) (by norm_num) (by norm_num))
                  (show 0 ≤ Y/2 by positivity)
      rw [scaled_center m Y hY, Finset.mul_sum] at hu
      have hlow : M-B/Y ≤ ∑ i ∈ s, (Y/2)*(w i*pair (n i) 0 (Real.sqrt Y)) := calc
        _ = ∑ i ∈ s, (w i*n i-(w i*(n i)^3)/Y) := by
          dsimp [M,B]; simp only [div_eq_mul_inv, Finset.sum_mul, Finset.sum_sub_distrib]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i hi
          have hn' : 0 < n i := by linarith [hn i hi]
          calc
            _ = w i*(n i-(n i)^3/Y) := by ring
            _ ≤ w i*(n i*Y/((n i)^2+Y)) :=
              mul_le_mul_of_nonneg_left (center_tail hn' hY) (hw i hi)
            _ = _ := by rw [← scaled_center (n i) Y hY]; ring
      have hmY : m*Y/(m^2+Y) ≤ m := by
        apply (div_le_iff₀ (by positivity : 0 < m^2+Y)).2
        nlinarith [show 0 ≤ m^3 by positivity]
      exact hlow.trans (hu.trans hmY)
    change M ≤ m
    by_contra! hM
    have hd : 0 < M-m := by linarith
    let Y := (B+1)/(M-m)
    have hY : 0 < Y := by dsimp [Y]; positivity
    have herr := herror Y hY
    have hrel : (M-m)*Y ≤ B := (le_div_iff₀ hY).1 (by linarith)
    have heq : (M-m)*Y = B+1 := by dsimp [Y]; field_simp
    linarith
  · have ht := hh.2 (1/2) (by norm_num) (by norm_num)
    rw [outer_at_boundary hm] at ht
    have heq : (∑ i ∈ s, w i*pair (n i) (1/2) 0) = ∑ i ∈ s, w i*boundary (n i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [outer_at_boundary (hn i hi)]
    rw [heq] at ht
    unfold boundary at ht ⊢
    linarith

/-- Sharp upper bound even among all nonnegative finite mixtures of arbitrary shifts. -/
theorem mixture_weight_optimal {ι : Type*} (s : Finset ι) (w n : ι → ℝ)
    {m : ℝ} (hm : 1/2 < m) (hw : ∀ i ∈ s, 0 ≤ w i) (hn : ∀ i ∈ s, 1/2 < n i)
    (hh : MixtureAdmissible s w n m) :
    ∑ i ∈ s, w i ≤ m/optimalOuter m := by
  obtain ⟨h1,h2⟩ := moments_of_mixture s w n hm hw hn hh
  exact mixture_weight_of_moments s w n hm hw hn h1 h2

end
end ERH.Stechkin
