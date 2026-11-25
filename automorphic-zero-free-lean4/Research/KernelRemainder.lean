import Research.HadamardFar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! A uniform inverse-square remainder for the complex Laplace kernel of a compact
piecewise twice differentiable profile. Both integrations by parts are executed in the proof. -/

open Set MeasureTheory
namespace ERH.KernelRemainder

noncomputable def damping (w : ℂ) (x : ℝ) := Complex.exp (-w*(x:ℂ))
noncomputable def laplace (w : ℂ) (q : ℝ → ℂ) (a b : ℝ) :=
  ∫ x in a..b, q x * damping w x

private theorem damping_continuous (w : ℂ) : Continuous (damping w) := by
  unfold damping
  fun_prop

private theorem damping_deriv (w : ℂ) (x : ℝ) :
    HasDerivAt (damping w) (-w*damping w x) x := by
  unfold damping
  have hd := (((hasDerivAt_id (x:ℂ)).const_mul (-w)).cexp).comp_ofReal
  simpa [mul_comm] using hd

private theorem damping_norm_le {w : ℂ} (hw : 0 ≤ w.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖damping w x‖ ≤ 1 := by
  rw [damping, Complex.norm_exp, Real.exp_le_one_iff]
  simp [Complex.mul_re, mul_nonneg hw hx]

/-- Integration by parts on one closed piece. Derivatives need only hold in the interior. -/
theorem once (w : ℂ) (q d : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hq : ContinuousOn q (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt q (d x) x) (hi : IntervalIntegrable d volume a b) :
    w * laplace w q a b =
      q a * damping w a - q b * damping w b + laplace w d a b := by
  have hf := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := q) (v := damping w) (u' := d) (v' := fun x => -w*damping w x)
    ((uIcc_of_le hab).symm ▸ hq) (damping_continuous w).continuousOn
    (by simpa [min_eq_left hab,max_eq_right hab] using hd)
    (fun x _ => damping_deriv w x) hi
    ((continuous_const.mul (damping_continuous w)).intervalIntegrable _ _)
  have hh (x : ℝ) : q x * (-w*damping w x) = -w * (q x*damping w x) := by ring
  change (∫ x in a..b, q x*(-w*damping w x)) = _ at hf
  simp_rw [hh] at hf
  rw [intervalIntegral.integral_const_mul] at hf
  unfold laplace
  linear_combination -hf

/-- Exact second-order identity, including both boundary derivatives. -/
theorem twice (w : ℂ) (q d e : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hq : ContinuousOn q (Icc a b)) (hd : ContinuousOn d (Icc a b))
    (hqd : ∀ x ∈ Ioo a b, HasDerivAt q (d x) x)
    (hde : ∀ x ∈ Ioo a b, HasDerivAt d (e x) x) (he : IntervalIntegrable e volume a b) :
    w^2*laplace w q a b - w*(q a*damping w a-q b*damping w b) =
      d a*damping w a-d b*damping w b + laplace w e a b := by
  linear_combination w * once w q d hab hq hqd (hd.intervalIntegrable_of_Icc hab) +
    once w d e hab hd hde he

private theorem norm_laplace {w : ℂ} (hw : 0 ≤ w.re) (q : ℝ → ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hi : IntervalIntegrable q volume a b) :
    ‖laplace w q a b‖ ≤ ∫ x in a..b, ‖q x‖ := by
  unfold laplace
  apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
  apply intervalIntegral.integral_mono_on hab
    (hi.mul_continuousOn (damping_continuous w).continuousOn).norm hi.norm
  intro x hx
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (damping_norm_le hw (ha.trans hx.1))

/-- One-piece inverse-square numerator bound. No matching of derivatives at later
interior breakpoints is required. -/
theorem piece_bound {w : ℂ} (hw : 0 ≤ w.re) (q d e : ℝ → ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hq : ContinuousOn q (Icc a b)) (hd : ContinuousOn d (Icc a b))
    (hqd : ∀ x ∈ Ioo a b, HasDerivAt q (d x) x)
    (hde : ∀ x ∈ Ioo a b, HasDerivAt d (e x) x) (he : IntervalIntegrable e volume a b) :
    ‖w^2*laplace w q a b - w*(q a*damping w a-q b*damping w b)‖ ≤
      ‖d a‖ + ‖d b‖ + ∫ x in a..b, ‖e x‖ := by
  rw [twice w q d e hab hq hd hqd hde he]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (norm_laplace hw e ha hab he)
  apply (norm_sub_le _ _).trans
  simp only [norm_mul]
  exact add_le_add
    (mul_le_of_le_one_right (norm_nonneg _) (damping_norm_le hw ha))
    (mul_le_of_le_one_right (norm_nonneg _) (damping_norm_le hw (ha.trans hab)))

/-- Piecewise regularity. The two endpoint values of `d` are its continuous one-sided
traces on the current cell. The second derivative only needs to be integrable. -/
structure Regular (q d e : ℝ → ℂ) (a b : ℝ) : Prop where
  cont : ContinuousOn q (Icc a b)
  derivCont : ContinuousOn d (Icc a b)
  deriv : ∀ x ∈ Ioo a b, HasDerivAt q (d x) x
  derivTwice : ∀ x ∈ Ioo a b, HasDerivAt d (e x) x
  integrable : IntervalIntegrable e volume a b

private theorem telescope (f : ℕ → ℂ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (f i-f (i+1)) = f 0-f n := by
  induction n with
  | zero => simp
  | succ n h => rw [Finset.sum_range_succ, h]; abel

/-- The explicit constant used for a general piecewise smooth profile. -/
noncomputable def budget (t : ℕ → ℝ) (d e : ℕ → ℝ → ℂ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (‖d i (t i)‖ + ‖d i (t (i+1))‖ + ∫ x in t i..t (i+1), ‖e i x‖)

theorem partition_bound {w : ℂ} (hw : 0 ≤ w.re) (t : ℕ → ℝ) (n : ℕ)
    (q : ℝ → ℂ) (d e : ℕ → ℝ → ℂ) (hstart : t 0 = 0) (ht : Monotone t)
    (h0 : q 0 = 1) (hD : q (t n) = 0)
    (reg : ∀ i < n, Regular q (d i) (e i) (t i) (t (i+1))) :
    ‖w^2*laplace w q 0 (t n)-w‖ ≤ budget t d e n := by
  let F := fun i => q (t i)*damping w (t i)
  let A := fun i => w^2*laplace w q (t i) (t (i+1)) - w*(F i-F (i+1))
  have hi : ∀ i < n, IntervalIntegrable (fun x => q x*damping w x) volume (t i) (t (i+1)) := by
    intro i hi
    exact ((reg i hi).cont.mul (damping_continuous w).continuousOn).intervalIntegrable_of_Icc
      (ht (Nat.le_succ _))
  have hsum : (∑ i ∈ Finset.range n, A i) = w^2*laplace w q 0 (t n)-w := by
    dsimp only [A]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, telescope]
    unfold laplace
    rw [intervalIntegral.sum_integral_adjacent_intervals hi]
    simp [F, hstart, h0, hD, damping]
  rw [← hsum]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro i hi
  have H := reg i (Finset.mem_range.mp hi)
  have ha : 0 ≤ t i := hstart ▸ ht (Nat.zero_le i)
  exact piece_bound hw q (d i) (e i) ha (ht (Nat.le_succ _)) H.cont H.derivCont
    H.deriv H.derivTwice H.integrable

/-- Scaling the numerator at `w=Lz` gives the true inverse-square remainder, with
one power of `L` in the denominator. -/
theorem scaled_bound {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : 0 < z.re)
    (t : ℕ → ℝ) (n : ℕ) (q : ℝ → ℂ) (d e : ℕ → ℝ → ℂ) (hstart : t 0 = 0) (ht : Monotone t)
    (h0 : q 0 = 1) (hD : q (t n) = 0)
    (reg : ∀ i < n, Regular q (d i) (e i) (t i) (t (i+1))) :
    ‖(L:ℂ)*laplace ((L:ℂ)*z) q 0 (t n) - 1/z‖ ≤ budget t d e n / (L*‖z‖^2) := by
  have hz' : z ≠ 0 := fun h => by simp [h] at hz
  have hw : 0 ≤ ((L:ℂ)*z).re := by simpa [Complex.mul_re] using (mul_pos hL hz).le
  have hineq := partition_bound hw t n q d e hstart ht h0 hD reg
  apply (le_div_iff₀ (mul_pos hL (sq_pos_of_pos (norm_pos_iff.mpr hz')))).mpr
  let I := laplace ((L:ℂ)*z) q 0 (t n)
  have heq : ((L:ℂ)*I-1/z)*((L:ℂ)*z^2) = ((L:ℂ)*z)^2*I - (L:ℂ)*z := by
    field_simp
  calc
    _ = ‖((L:ℂ)*I-1/z)*((L:ℂ)*z^2)‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hL.le, I]
    _ = _ := congrArg norm heq
    _ ≤ _ := hineq

/-- Identification of the compact interval integral with the half-line kernel. -/
theorem compact_laplace (w : ℂ) (q : ℝ → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ x, D < x → q x = 0) :
    (∫ x in Ioi (0:ℝ), q x*damping w x) = laplace w q 0 D := by
  let F := fun x => q x*damping w x
  calc
    _ = ∫ x in Ioi (0:ℝ), (Ioc 0 D).indicator F x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      by_cases h : x ≤ D
      · exact (indicator_of_mem (show x ∈ Ioc 0 D from ⟨hx,h⟩) F).symm
      · have ho : x ∉ Ioc 0 D := fun he => h he.2
        simp [F, hs x (lt_of_not_ge h), ho]
    _ = ∫ x in Ioc (0:ℝ) D, F x := by
      rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr (fun x hx => hx.1)]
    _ = _ := by rw [laplace, intervalIntegral.integral_of_le hD]

/-- The whole-line-to-the-right formulation used by the signed Hadamard comparison. -/
theorem halfline_scaled_bound {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : 0 < z.re)
    (t : ℕ → ℝ) (n : ℕ) (q : ℝ → ℂ) (d e : ℕ → ℝ → ℂ) (hstart : t 0 = 0) (ht : Monotone t)
    (h0 : q 0 = 1) (hD : q (t n) = 0) (hs : ∀ x, t n < x → q x = 0)
    (reg : ∀ i < n, Regular q (d i) (e i) (t i) (t (i+1))) :
    ‖(L:ℂ) * (∫ x in Ioi (0:ℝ), q x * Complex.exp (-((L:ℂ)*z)*(x:ℂ))) - 1/z‖ ≤
       budget t d e n / (L*‖z‖^2) := by
  change ‖(L:ℂ) * (∫ x in Ioi (0:ℝ), q x*damping ((L:ℂ)*z) x) - 1/z‖ ≤ _
  rw [compact_laplace _ _ (hstart ▸ ht (Nat.zero_le n)) hs]
  exact scaled_bound hL hz t n q d e hstart ht h0 hD reg

/-- Taking the real part supplies the actual countable far-zero sum, without a separate
pointwise Fourier remainder hypothesis. The reference zero-count budget remains explicit. -/
theorem real_far_sum {ι : Type*} {L η D M : ℝ} (hL : 0 < L) (hη : 0 < η) (hD : 0 ≤ D)
    (t : ℕ → ℝ) (n : ℕ) (q : ℝ → ℂ) (d e : ℕ → ℝ → ℂ) (hstart : t 0 = 0) (ht : Monotone t)
    (h0 : q 0 = 1) (hend : q (t n) = 0) (hcompact : ∀ x, t n < x → q x = 0)
    (reg : ∀ i < n, Regular q (d i) (e i) (t i) (t (i+1)))
    (z z₀ : ι → ℂ) (hz : ∀ i, 0 < (z i).re) (hfar : ∀ i, η ≤ ‖z i‖)
    (href : ∀ i, 0 < ‖z₀ i‖) (hshift : ∀ i, ‖z₀ i-z i‖ ≤ D)
    (hsum : Summable (fun i => 1/‖z₀ i‖^2)) (hb : ∑' i, 1/‖z₀ i‖^2 ≤ M*L) :
    let E := fun i => ((L:ℂ)*(∫ x in Ioi (0:ℝ), q x * Complex.exp (-((L:ℂ)*z i)*(x:ℂ))) -
      1/z i).re
    Summable (fun i => |E i|) ∧
      ∑' i, |E i| ≤ budget t d e n*M*(1+D/η)^2 := by
  dsimp only
  have hn : 0 ≤ budget t d e n := by
    unfold budget
    apply Finset.sum_nonneg
    intro i _
    apply add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    exact intervalIntegral.integral_nonneg (ht (Nat.le_succ _)) (fun _ _ => norm_nonneg _)
  apply ERH.SignedHadamard.far_sum z z₀ _ hη hD hn hL hfar href hshift _ hsum hb
  intro i
  apply (Complex.abs_re_le_norm _).trans
  have h := halfline_scaled_bound hL (hz i) t n q d e hstart ht h0 hend hcompact reg
  convert h using 1
  ring

end ERH.KernelRemainder

#print axioms ERH.KernelRemainder.piece_bound

#print axioms ERH.KernelRemainder.halfline_scaled_bound

#print axioms ERH.KernelRemainder.real_far_sum
