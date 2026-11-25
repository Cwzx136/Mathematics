import Research.Prior.LiPoissonInputs
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Ordinary summability hypotheses for the Li formula follow from a single
positive Poisson series. -/
namespace LiDivisorConvergence
open Real LiAllHeights LiReflectedPair Filter Topology

/-- The quadratic Taylor remainder at 1 is uniformly bounded for all complex
increments of norm at most one. -/
private theorem remainder (n : ℕ) :
    ∃ C:ℝ, 0≤C ∧ ∀ w:ℂ,‖w‖≤1 → ‖(1-w)^n-1+n*w‖ ≤ C*‖w‖^2 := by
  induction n with
  | zero => exact ⟨0,le_rfl,by simp⟩
  | succ n ih =>
    obtain ⟨C,hC,rec⟩ := ih
    refine ⟨2*C+n,by positivity,?_⟩
    intro w hw
    have uw : ‖1-w‖≤2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    have id : (1-w)^(n+1)-1+(n+1:ℕ)*w=
        (1-w)*((1-w)^n-1+n*w)+(n:ℂ)*w^2 := by push_cast; rw [pow_succ]; ring
    rw [id]
    have z := norm_add_le ((1-w)*((1-w)^n-1+n*w)) ((n:ℂ)*w^2)
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_natCast] at z
    nlinarith [mul_le_mul uw (rec w hw) (norm_nonneg _) (by norm_num : (0:ℝ)≤2)]

theorem li_far_bound (n : ℕ) :
    ∃ C:ℝ,0≤C ∧ ∀ β γ:ℝ,0≤β → β≤1 → 1≤|γ| →
        ‖liTerm n β γ‖ ≤ C/γ^2 := by
  obtain ⟨C,cp,r⟩ := remainder n
  refine ⟨n+C,by positivity,?_⟩
  intro β γ hb hb' hg
  let z : ℂ := ⟨β,γ⟩
  have zi : |γ| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have g0 : 0 < |γ| := by linarith
  have zp : 0 < ‖z‖ := g0.trans_le zi
  have zz : 0 < β^2+γ^2 := by nlinarith [sq_pos_of_pos g0,sq_abs γ,sq_nonneg β]
  let w := 1/z
  have wf : ‖w‖ ≤ 1/|γ| := by
    dsimp [w]; rw [norm_div,norm_one]; exact div_le_div_of_nonneg_left zero_le_one g0 zi
  have w1 : ‖w‖ ≤ 1 := wf.trans ((div_le_one g0).mpr hg)
  have re : w.re=β/(β^2+γ^2) := by simp [w,z,Complex.normSq_apply,sq]
  have re0 : 0≤w.re := by rw [re]; positivity
  have re1 : w.re≤1/γ^2 := by
    rw [re]
    apply (div_le_div_of_nonneg_right hb' zz.le).trans
    exact div_le_div_of_nonneg_left zero_le_one (by nlinarith [sq_pos_of_pos g0,sq_abs γ]) (by linarith [sq_nonneg β])
  have sqw : ‖w‖^2 ≤ 1/γ^2 := by
    have h := mul_self_le_mul_self (norm_nonneg w) wf
    simpa only [←sq,div_pow,one_pow,sq_abs] using h
  have s := r w w1
  have cost := (Complex.abs_re_le_norm ((1-w)^n-1+n*w)).trans s
  have ab : |liTerm n β γ| ≤ |((1-w)^n-1+n*w).re|+(n:ℝ)*w.re := by
    have id : liTerm n β γ = (n:ℝ)*w.re-((1-w)^n-1+n*w).re := by
      simp [liTerm,Complex.add_re,Complex.sub_re,Complex.mul_re,w,z]
    rw [id]
    have h := abs_sub ((n:ℝ)*w.re) (((1-w)^n-1+n*w).re)
    have pos : 0≤(n:ℝ)*w.re := mul_nonneg (by positivity) re0
    rw [abs_of_nonneg pos] at h
    linarith
  rw [Real.norm_eq_abs]
  nlinarith [mul_le_mul_of_nonneg_left sqw cp,mul_le_mul_of_nonneg_left re1 (Nat.cast_nonneg (α:=ℝ) n),
    show (n+C)/γ^2=(n:ℝ)*(1/γ^2)+C*(1/γ^2) by ring]

private theorem kernel_lower {β γ B : ℝ} (hb : 0≤β) (hb' : β≤1) (hB : |γ|≤B) :
    2/(9+B^2) ≤ kernel 3 β γ := by
  have x : 0<3-β := by linarith
  have s : γ^2 ≤ B^2 := by simpa only [←sq,sq_abs] using mul_self_le_mul_self (abs_nonneg γ) hB
  have q : (3-β)^2+γ^2 ≤ 9+B^2 := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hb')]
  unfold kernel
  apply (div_le_div_of_nonneg_left (by norm_num) (by positivity) q).trans
  apply div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem escapes {ι : Type*} (β γ : ι→ℝ) (strip : ∀ i,0≤β i ∧ β i≤1)
    (hs : Summable (fun i=>kernel 3 (β i) (γ i))) (B : ℝ) :
    ∀ᶠ i in cofinite,B < |γ i| := by
  have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (show 0<(2:ℝ)/(9+B^2) by positivity))
  filter_upwards [h] with i hi
  by_contra! c
  exact (kernel_lower (strip i).1 (strip i).2 c).not_gt hi

private theorem tail_compare {β γ : ℝ} (hb : 0≤β) (hb' : β≤1) (hg : 1≤|γ|) :
    1/γ^2 ≤ 5*kernel 3 β γ := by
  have x : 0<3-β := by linarith
  have g2 : 1≤γ^2 := by simpa only [←sq,sq_abs,one_pow] using mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hg
  have K := kernel_lower hb hb' (B:=|γ|) le_rfl
  rw [sq_abs] at K
  have p : 1/γ^2 ≤ 5*(2/(9+γ^2)) := by
    rw [←mul_div_assoc,div_le_div_iff₀ (by linarith) (by positivity)]; nlinarith
  linarith

theorem li_summable {ι : Type*} (β γ : ι→ℝ) (strip : ∀ i,0≤β i ∧ β i≤1)
    (hs : Summable (fun i=>kernel 3 (β i) (γ i))) (n : ℕ) :
    Summable (fun i=>liTerm n (β i) (γ i)) := by
  obtain ⟨C,cp,bound⟩ := li_far_bound n
  apply (hs.mul_left (5*C)).of_norm_bounded_eventually
  filter_upwards [escapes β γ strip hs 1] with i hi
  have b := bound (β i) (γ i) (strip i).1 (strip i).2 hi.le
  have h := mul_le_mul_of_nonneg_left (tail_compare (strip i).1 (strip i).2 hi.le) cp
  calc
    _ ≤ C/γ i^2 := b
    _ = C*(1/γ i^2) := by ring
    _ ≤ (5*C)*kernel 3 (β i) (γ i) := by linarith

/-- Each translated Poisson series has a summable majorant off a finite set. -/
theorem poisson_summable {ι : Type*} (β γ : ι→ℝ) (strip : ∀ i,0≤β i ∧ β i≤1)
    (hs : Summable (fun i=>kernel 3 (β i) (γ i))) {a : ℝ} (ha : 3≤a) (t : ℝ) :
    Summable (fun i=>kernel a (β i) (t-γ i)) := by
  apply (hs.mul_left (20*a)).of_norm_bounded_eventually
  filter_upwards [escapes β γ strip hs (max 1 (2*|t|))] with i hi
  have g1 : 1 < |γ i| := (le_max_left _ _).trans_lt hi
  have gt := (le_max_right _ _).trans_lt hi
  have ab := abs_sub_abs_le_abs_sub t (γ i)
  have dist : |γ i|/2 ≤ |t-γ i| := by
    have h := abs_sub_abs_le_abs_sub (γ i) t
    rw [abs_sub_comm (γ i) t] at h
    linarith
  have g2 : 0<γ i^2 := by nlinarith [sq_pos_of_pos (show 0 < abs (γ i) by linarith),sq_abs (γ i)]
  have ds : γ i^2/4 ≤ (t-γ i)^2 := by
    have h := mul_self_le_mul_self (show 0 ≤ (abs (γ i))/2 by positivity) dist
    rw [←sq,←sq,div_pow,sq_abs,sq_abs] at h; linarith
  have ap : 0 < a-β i := by linarith [(strip i).2]
  have den : 0 < (a-β i)^2+(t-γ i)^2 := by positivity
  have bound : kernel a (β i) (t-γ i) ≤ 4*a/γ i^2 := by
    unfold kernel
    apply (div_le_div_of_nonneg_right (show a-β i ≤ a by linarith [(strip i).1]) den.le).trans
    rw [show 4*a/γ i^2=a/(γ i^2/4) by ring]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith [sq_nonneg (a-β i)])
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤kernel a (β i) (t-γ i) from div_nonneg ap.le den.le)]
  have h := mul_le_mul_of_nonneg_left (tail_compare (strip i).1 (strip i).2 g1.le)
    (show 0≤4*a by linarith)
  linarith [show 4*a/γ i^2=(4*a)*(1/γ i^2) by ring]

/-- A positive Hadamard sum at a fixed large real abscissa forces absolute
convergence of the basic kernel at three. -/
theorem basic_summable {ι : Type*} (β γ : ι→ℝ) (strip : ∀ i,0≤β i ∧ β i≤1)
    (ex : 1 < LiPoissonInputs.poisson β γ 1000 0) :
    Summable (fun i=>kernel 3 (β i) (γ i)) := by
  have b : Summable (fun i=>kernel 1000 (β i) (γ i)) := by
    by_contra h
    simp only [LiPoissonInputs.poisson,kernel,zero_sub,even_two.neg_pow] at ex
    unfold kernel at h
    rw [tsum_eq_zero_of_not_summable h] at ex
    linarith
  apply (b.mul_left (1000:ℝ)).of_nonneg_of_le
  · intro i; unfold kernel
    exact div_nonneg (by linarith [(strip i).2]) (by positivity)
  · intro i
    let small := 3-β i
    let big := 1000-β i
    have sp : 2≤small := by dsimp [small]; linarith [(strip i).2]
    have bp : 0<big := by dsimp [big]; linarith [(strip i).2]
    have sb : small≤big := by dsimp [small,big]; linarith
    have bmax : big ≤ 1000*small := by dsimp [big,small]; linarith [(strip i).2]
    have cmp : small/(small^2+γ i^2) ≤ (big/small)*(big/(big^2+γ i^2)) := by
      rw [div_mul_div_comm,div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg (γ i)) (sub_nonneg.mpr
        (mul_self_le_mul_self (show 0≤small by linarith) sb))]
    have scale : big/small≤1000 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    exact cmp.trans (mul_le_mul_of_nonneg_right scale (div_nonneg bp.le (by positivity)))

/-- The high real-axis lower bound excludes finite divisors, even if all zeros
were allowed arbitrary multiplicity. Hence there is a zero above every height. -/
theorem unbounded {ι : Type*} (β γ : ι→ℝ) (strip : ∀ i,0≤β i ∧ β i≤1)
    (positive : ∀ a:ℝ,1000≤a → 1<LiPoissonInputs.poisson β γ a 0) (T : ℝ) :
    ∃ i,T < |γ i| := by
  classical
  have b := basic_summable β γ strip (positive 1000 le_rfl)
  by_cases fin : Nonempty (Fintype ι)
  · letI : Fintype ι := fin.some
    let a : ℝ := 1000+Fintype.card ι
    have ah : 1000≤a := by dsimp [a]; linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)]
    have p := positive a ah
    simp only [LiPoissonInputs.poisson,tsum_fintype,zero_sub] at p
    have one (i : ι) : kernel a (β i) (-γ i) ≤ 1/(a-1) := by
      have ap : 0<a-β i := by linarith [(strip i).2]
      unfold kernel
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [mul_nonneg ap.le (sub_nonneg.mpr (strip i).2),sq_nonneg (γ i)]
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>one i)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
    have card : (Fintype.card ι:ℝ)*(1/(a-1))≤1 := by
      rw [mul_one_div,div_le_one (by linarith)]; dsimp [a]; linarith
    linarith
  · haveI : Infinite ι := not_finite_iff_infinite.mp (fun h=>fin ⟨Fintype.ofFinite ι⟩)
    exact (escapes β γ strip b T).exists

#print axioms li_far_bound
#print axioms escapes
#print axioms li_summable
#print axioms poisson_summable
#print axioms basic_summable
#print axioms unbounded

end LiDivisorConvergence
