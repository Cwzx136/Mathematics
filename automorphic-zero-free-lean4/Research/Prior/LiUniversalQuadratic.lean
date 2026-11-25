import Research.Prior.LiAllHeights
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! The all-height quadratic Li implication for a divisor with a Hadamard lower
bound at two real abscissas and upper bounds at the possible resonance centers. -/
namespace LiUniversalQuadratic
open Real LiAllHeights LiReflectedPair

theorem half_loss {v : ℝ} (hv : |v| ≤ 1/2) : cosh v-1 ≤ 0.128 := by
  have eq := cosh_two_mul (1/2 : ℝ)
  norm_num at eq
  have unit := cosh_sq_sub_sinh_sq (1/2 : ℝ)
  have ei : (exp 1)⁻¹ ≤ 0.3685 := (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by
    norm_num; linarith [exp_one_gt_d9])
  have ce : cosh 1 ≤ 1.544 := by
    rw [cosh_eq,exp_neg]
    linarith [exp_one_lt_d9]
  have half : cosh (1/2) ≤ 1.128 := by nlinarith
  have rel : cosh v ≤ cosh (1/2) := cosh_le_cosh.mpr (by simpa using hv)
  linarith

noncomputable def freq (k : ℕ) : ℝ := (k:ℝ)*(2*π)
noncomputable def centre (m : ℝ) (k : ℕ) : ℝ := m/freq k
noncomputable def cells (m : ℝ) : Finset ℕ := Finset.Icc 1 ⌊(√m+0.5)/(2*π)⌋₊

/-- The two signed Poisson weights for one possible resonance. -/
noncomputable def charge (m : ℝ) (k : ℕ) (β γ : ℝ) : ℝ :=
  (0.128/0.3)*(kernel 3 β (centre m k-γ) + kernel 3 β (-centre m k-γ))

private theorem kernel_nonneg {a β γ : ℝ} (h : 0 ≤ a-β) : 0 ≤ kernel a β γ := by
  unfold kernel; positivity

private theorem charge_nonneg (m : ℝ) (k : ℕ) {β γ : ℝ} (hb : β ≤ 1) :
    0 ≤ charge m k β γ := by
  unfold charge
  have p : 0 ≤ 3-β := by linarith
  exact mul_nonneg (by norm_num) (add_nonneg (kernel_nonneg p) (kernel_nonneg p))

private theorem charge_local (m : ℝ) (k : ℕ) {β γ : ℝ} (hb : 0 ≤ β) (hb' : β ≤ 1)
    (hc : abs (|γ| - centre m k) < 1) : 0.128 ≤ charge m k β γ := by
  have p : 0 ≤ 3-β := by linarith
  unfold charge
  rcases le_or_gt 0 γ with h|h
  · rw [abs_of_nonneg h,abs_sub_comm] at hc
    have f := local_kernel hb hb' hc.le
    have q : 0 ≤ kernel 3 β (-centre m k-γ) := kernel_nonneg p
    linarith
  · rw [abs_of_neg h] at hc
    have hc' : |-centre m k-γ| < 1 := by convert hc using 2; ring
    have f := local_kernel hb hb' hc'.le
    have q : 0 ≤ kernel 3 β (centre m k-γ) := kernel_nonneg p
    linarith

/-- Away from the critical-line part, all negative contributions are paid for
by the finite set of signed sampling windows determined solely by the index. -/
theorem negative_majorant {n : ℕ} {β γ : ℝ} (hm : 33 ≤ (n:ℝ)) (hb : 0 ≤ β) (hb' : β ≤ 1)
    (verified : |γ| ≤ √(n:ℝ) → β=1/2) :
    -(pairValue n β γ / 2) ≤ ∑ k ∈ cells n,charge n k β γ := by
  let m : ℝ := n
  let g := |γ|
  let F := pairValue n β γ/2
  have mp : 0 < m := by change 0 < (n:ℝ); linarith
  have ng : 0 ≤ ∑ k ∈ cells n,charge n k β γ := Finset.sum_nonneg (fun k _ => charge_nonneg _ _ hb')
  by_cases positive : 0 ≤ F
  · change -F ≤ _; linarith
  have ghigh : √m < g := by
    by_contra! h
    have l := line_nonneg n γ
    have e := verified h
    dsimp [F] at positive; rw [e] at positive; linarith
  have g5 : 5 ≤ g := by
    have s := sq_sqrt mp.le
    have nn := sqrt_nonneg m
    change 33 ≤ m at hm
    nlinarith
  have gp : 0 < g := by linarith
  let u := (log (g^2+(1-β)^2)-log (g^2+β^2))/2
  let θ := arctan (β/g) + arctan ((1-β)/g)
  have id : F=1-cosh (m*u)*cos (m*θ) := pair_polar n β γ gp
  have hu := modulus_bound gp hb hb'
  have hθ := phase_bounds gp hb hb'
  change |u| ≤ 1/(2*g^2) at hu
  change g/(1+g^2) ≤ θ ∧ θ ≤ 1/g at hθ
  have m2 : m ≤ g^2 := by
    nlinarith [sq_sqrt mp.le,mul_self_le_mul_self (sqrt_nonneg m) ghigh.le]
  have vu : |m*u| ≤ m/(2*g^2) := by
    rw [abs_mul,abs_of_pos mp]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hu mp.le
  have vh := vu.trans (show m/(2*g^2) ≤ 1/2 from (div_le_iff₀ (by positivity)).mpr (by linarith))
  have cut : |m*u| ≤ m*θ := by
    rw [abs_mul,abs_of_pos mp]
    apply mul_le_mul_of_nonneg_left _ mp.le
    apply hu.trans (le_trans _ hθ.1)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ g-5 by linarith) (sq_nonneg g)]
  have neg : 1 < cosh (m*u)*cos (m*θ) := by rw [id] at positive; linarith
  obtain ⟨k,hk,near⟩ := resonance cut neg
  have fp : 0 < freq k := by unfold freq; positivity
  have mg : m/g ≤ √m := by
    rw [div_le_iff₀ gp]
    nlinarith [sq_sqrt mp.le,mul_nonneg (sqrt_nonneg m) (sub_nonneg.mpr ghigh.le)]
  have xhi : m*θ ≤ √m := (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hθ.2 mp.le : m*θ ≤ m/g) |>.trans mg
  have kcap : (k:ℝ) ≤ (√m+0.5)/(2*π) := by
    have aux := (abs_le.mp (near.le.trans vh)).1
    rw [le_div_iff₀ (by positivity)]
    linarith
  have member : k ∈ cells n := Finset.mem_Icc.mpr ⟨hk,Nat.le_floor kcap⟩
  have near' : |m*θ-freq k| ≤ m/(2*g^2) := near.le.trans vu
  have loc := resonance_window mp g5 fp hθ.1 hθ.2 near'
  have bill : (0.128:ℝ) ≤ charge n k β γ := charge_local m k hb hb' loc
  have paid := Finset.single_le_sum (f := fun k => charge n k β γ)
    (fun k _ => charge_nonneg n k hb') member
  have cosbound := mul_le_mul_of_nonneg_left (cos_le_one (m*θ)) (cosh_pos (m*u)).le
  change -F ≤ _
  linarith [half_loss vh]

/-- A single zero at any ordinate satisfies one pointwise majorization. The
right and left real-axis kernels create positive mass beyond half the index. -/
theorem single {n : ℕ} {β γ : ℝ} (hm : 33 ≤ (n:ℝ)) (hb : 0 ≤ β) (hb' : β ≤ 1)
    (verified : |γ| ≤ √(n:ℝ) → β=1/2) :
    0.17*n*(kernel (2*n) β γ-0.481*kernel (n/2) β γ) -
      (∑ k ∈ cells n,charge n k β γ) ≤ pairValue n β γ/2 := by
  let m : ℝ := n
  change 33 ≤ m at hm
  have mp : 0 < m := by linarith
  change 0.17*m*(kernel (2*m) β γ-0.481*kernel (m/2) β γ)-_ ≤ _
  rcases le_or_gt |γ| (m/2) with h|h
  · have a := kernel_cancel (show 16.5 ≤ m/2 by linarith) hb hb' h
    rw [show 4*(m/2)=2*m by ring] at a
    have b := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 0.17*m by positivity) (sub_nonpos.mpr a)
    linarith [negative_majorant hm hb hb' verified]
  · have gp : 0 < |γ| := by linarith
    have g2 : 0 < γ^2 := by nlinarith [sq_pos_of_pos gp,sq_abs γ]
    have b : 0 < 2*m-β := by linarith
    have kr : kernel (2*m) β γ ≤ (2*m)/γ^2 := by
      unfold kernel
      calc
        _ ≤ (2*m-β)/γ^2 := div_le_div_of_nonneg_left b.le g2 (by nlinarith [sq_nonneg (2*m-β)])
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith) g2.le
    have kl : 0 ≤ kernel (m/2) β γ := kernel_nonneg (by linarith)
    have kc : 0.17*m*(kernel (2*m) β γ-0.481*kernel (m/2) β γ) ≤ 0.34*(m/|γ|)^2 := by
      have z := mul_le_mul_of_nonneg_left (show kernel (2*m) β γ-0.481*kernel (m/2) β γ ≤ 2*m/γ^2 by linarith) (show 0 ≤ 0.17*m by positivity)
      convert z using 1; rw [div_pow,sq_abs]; ring
    have p := phase_bounds gp hb hb'
    have actual := distant hm h.le p.1 p.2 (modulus_bound gp hb hb')
    rw [←pair_polar n β γ gp] at actual
    have zero : 0 ≤ ∑ k ∈ cells n,charge n k β γ := Finset.sum_nonneg (fun k _ => charge_nonneg _ _ hb')
    linarith

/-- The total resonance charge is controlled by the number of possible integer
frequencies. Each point lies in the divisor with its actual multiplicity. -/
theorem budget {ι : Type*} (β γ : ι → ℝ) {m D : ℝ} (_hm : 0 ≤ m) (hD : 0 ≤ D)
    (hs : ∀ k∈cells m,Summable (fun i => charge m k (β i) (γ i)))
    (localBound : ∀ k∈cells m,(∑' i,charge m k (β i) (γ i)) ≤ 1.17*D) :
    (∑' i,∑ k∈cells m,charge m k (β i) (γ i)) ≤ (1.17*(√m+0.5)/(2*π))*D := by
  rw [Summable.tsum_finsetSum hs]
  have cc : ((cells m).card:ℝ) ≤ (√m+0.5)/(2*π) := by
    simp only [cells,Nat.card_Icc,Nat.add_sub_cancel]
    apply Nat.floor_le
    positivity
  calc
    _ ≤ ∑ _k∈cells m,1.17*D := Finset.sum_le_sum localBound
    _ = ((cells m).card:ℝ)*(1.17*D) := by simp
    _ ≤ ((√m+0.5)/(2*π))*(1.17*D) :=
      mul_le_mul_of_nonneg_right cc (by positivity)
    _ = _ := by ring

/-- The original complex Li sum for all indices above 32. Its analytic inputs
are the actual summed Poisson estimate at two abscissas and the signed shifted
Poisson estimates at at most floor((√n+1/2)/(2π)) frequencies. -/
theorem positive_large {ι : Type*} (β γ : ι → ℝ) (reflect : ι ≃ ι) {n : ℕ} {D : ℝ}
    (hm : 33 ≤ (n:ℝ)) (hD : 0 < D) (strip : ∀ i,0 ≤ β i ∧ β i ≤ 1)
    (refRe : ∀ i,β (reflect i)=1-β i) (refIm : ∀ i,γ (reflect i)=γ i)
    (verified : ∀ i,|γ i| ≤ √(n:ℝ) → β i=1/2)
    (liSum : Summable (fun i => liTerm n (β i) (γ i)))
    (rightSum : Summable (fun i => kernel (2*n) (β i) (γ i)))
    (leftSum : Summable (fun i => kernel (n/2) (β i) (γ i)))
    (chargeSum : ∀ k∈cells n,Summable (fun i => charge n k (β i) (γ i)))
    (distantBound : 0.21*D ≤ (∑' i,kernel (2*n) (β i) (γ i))-0.481*(∑' i,kernel (n/2) (β i) (γ i)))
    (localBound : ∀ k∈cells n,(∑' i,charge n k (β i) (γ i)) ≤ 1.17*D) :
    0 < ∑' i,liTerm n (β i) (γ i) := by
  let f : ι → ℝ := fun i => liTerm n (β i) (γ i)
  have fs : Summable f := liSum
  have rs : Summable (fun i => f (reflect i)) := reflect.summable_iff.mpr fs
  have pair (i : ι) : pairValue n (β i) (γ i)=f i+f (reflect i) := by
    simp only [f,refRe,refIm,pairValue,liTerm,Complex.add_re]
  have ps : Summable (fun i => pairValue n (β i) (γ i)) := by simpa only [pair] using fs.add rs
  have pp := ps.mul_right (1/2:ℝ)
  simp only [←div_eq_mul_one_div] at pp
  let R : ι → ℝ := fun i => kernel (2*n) (β i) (γ i)
  let r : ι → ℝ := fun i => kernel (n/2) (β i) (γ i)
  have Rsum : Summable R := rightSum
  have rsum : Summable r := leftSum
  let v := fun i => 0.17*n*(R i-0.481*r i)
  have vs : Summable v := (Rsum.sub (rsum.mul_left 0.481)).mul_left _
  let e := fun i => ∑ k∈cells n,charge n k (β i) (γ i)
  have es : Summable e := summable_sum chargeSum
  have via := (vs.sub es).tsum_le_tsum (fun i => single hm (strip i).1 (strip i).2 (verified i)) pp
  rw [vs.tsum_sub es] at via
  have ident : (∑' i,v i)=0.17*n*((∑' i,R i)-0.481*(∑' i,r i)) := by
    change (∑' i,(0.17*(n:ℝ))*(R i-0.481*r i))=_
    rw [(Rsum.sub (rsum.mul_left 0.481)).tsum_mul_left (0.17*(n:ℝ)),
      Rsum.tsum_sub (rsum.mul_left 0.481),rsum.tsum_mul_left]
  rw [ident] at via
  have mpos : 0 ≤ (n:ℝ) := by positivity
  have mass := mul_le_mul_of_nonneg_left distantBound (show 0 ≤ 0.17*(n:ℝ) by positivity)
  have paid := budget β γ mpos hD.le chargeSum localBound
  change (∑' i,e i) ≤ _ at paid
  change 0.17*(n:ℝ)*(0.21*D) ≤ 0.17*n*((∑' i,R i)-0.481*(∑' i,r i)) at mass
  have hpos := total hm hD (show 0.0357*n*D ≤ 0.17*n*((∑' i,R i)-0.481*(∑' i,r i)) by linarith) paid via
  simp only [pair] at hpos
  rw [show (fun i => (f i+f (reflect i))/2)=(fun i => (f i+f (reflect i))*(1/2)) by funext i; ring,
      (fs.add rs).tsum_mul_right,fs.tsum_add rs,reflect.tsum_eq f] at hpos
  change 0 < ∑' i,f i
  linarith

/-- All smaller integer indices fall under the already proved linear criterion
at precisely the required verified height. -/
theorem small_cap {m : ℝ} (hm : 1 ≤ m) (h32 : m ≤ 32) : m ≤ 2*π*√m-π := by
  have s := sq_sqrt (show 0 ≤ m by linarith)
  have sp := sqrt_nonneg m
  have a : 1 ≤ √m := by nlinarith
  have b : √m ≤ 5.66 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr a) (sub_nonneg.mpr b),
    mul_nonneg sp (sub_nonneg.mpr pi_gt_d2.le),pi_lt_d2]

/-- The complete threshold-free quadratic-prefix theorem for a summable
reflected divisor, retaining the explicit Poisson bounds as analytic hypotheses. -/
theorem all_heights {ι : Type*} (β γ : ι → ℝ) (reflect : ι ≃ ι) {n : ℕ} {T : ℝ}
    (hn : 0<n) (hT : 0 ≤ T) (cap : (n:ℝ) ≤ T^2)
    (strip : ∀ i,0 ≤ β i ∧ β i ≤ 1)
    (refRe : ∀ i,β (reflect i)=1-β i) (refIm : ∀ i,γ (reflect i)=γ i)
    (verified : ∀ i,|γ i| ≤ T → β i=1/2) (higher : ∃ i,T < |γ i|)
    (liSum : Summable (fun i => liTerm n (β i) (γ i)))
    (poisson : 33 ≤ n → ∃ D:ℝ,0 < D ∧
      Summable (fun i => kernel (2*n) (β i) (γ i)) ∧
      Summable (fun i => kernel (n/2) (β i) (γ i)) ∧
      (∀ k∈cells n,Summable (fun i => charge n k (β i) (γ i))) ∧
      0.21*D ≤ (∑' i,kernel (2*n) (β i) (γ i))-0.481*(∑' i,kernel (n/2) (β i) (γ i)) ∧
      ∀ k∈cells n,(∑' i,charge n k (β i) (γ i)) ≤ 1.17*D) :
    0 < ∑' i,liTerm n (β i) (γ i) := by
  have sT : √(n:ℝ) ≤ T := by simpa [sqrt_sq hT] using sqrt_le_sqrt cap
  have line i (h : |γ i| ≤ √(n:ℝ)) := verified i (h.trans sT)
  rcases le_or_gt 33 n with h|h
  · obtain ⟨D,hD,rightSum,leftSum,charges,low,up⟩ := poisson h
    exact positive_large β γ reflect (by exact_mod_cast h) hD strip refRe refIm line liSum
      rightSum leftSum charges low up
  · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hn32 : (n:ℝ) ≤ 32 := by exact_mod_cast Nat.le_of_lt_succ h
    have sr : 1 ≤ √(n:ℝ) := by simpa using sqrt_le_sqrt hn1
    have high : ∃ i,√(n:ℝ) < |γ i| := higher.imp (fun _ hi => sT.trans_lt hi)
    exact li_positive β γ reflect sr (by positivity) (small_cap hn1 hn32) strip refRe refIm line high liSum

#print axioms half_loss
#print axioms negative_majorant
#print axioms single
#print axioms budget
#print axioms positive_large
#print axioms small_cap
#print axioms all_heights

end LiUniversalQuadratic
