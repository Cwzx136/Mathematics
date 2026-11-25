import Research.Prior.LiUniversalQuadratic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Conductor and gamma-parameter accounting for the two Poisson inequalities
in the threshold-free quadratic Li transfer. -/
namespace LiPoissonInputs
open Real LiAllHeights LiUniversalQuadratic

/-- Absolute value of one shifted real gamma argument, before division by 2π. -/
noncomputable def radius (μ : ℂ) (a t : ℝ) : ℝ := ‖(a:ℂ)+μ+(t:ℂ)*Complex.I‖

/-- The conductor and the logarithmic main terms of all real gamma factors. -/
noncomputable def scale {d : ℕ} (Q : ℝ) (μ : Fin d → ℂ) (a t : ℝ) : ℝ :=
  log Q + ∑ j,log (radius (μ j) a t/(2*π))

private theorem rad0_bound (μ : ℂ) {a : ℝ} (h : -1 ≤ μ.re) :
    a-1 ≤ radius μ a 0 := by
  have u := Complex.re_le_norm ((a:ℂ)+μ)
  simp [radius] at *
  linarith

private theorem rad_monotone (μ : ℂ) {a b : ℝ} (hμ : -1 ≤ μ.re) (ha : 1 ≤ a) (hab : a ≤ b) :
    radius μ a 0 ≤ radius μ b 0 := by
  simp only [radius,Complex.ofReal_zero,zero_mul,add_zero,Complex.norm_def]
  apply sqrt_le_sqrt
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_add]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ a+b+2*μ.re by linarith)]

private theorem rad_shift (μ : ℂ) (a t : ℝ) :
    radius μ a t ≤ radius μ a 0+|t| := by
  simpa [radius,norm_mul] using norm_add_le ((a:ℂ)+μ) ((t:ℂ)*Complex.I)

private theorem rad_pos (μ : ℂ) {a : ℝ} (t : ℝ) (hμ : -1 ≤ μ.re) (ha : 1 < a) :
    0 < radius μ a t := by
  have u := Complex.re_le_norm ((a:ℂ)+μ+(t:ℂ)*Complex.I)
  simp [Complex.mul_re] at u
  unfold radius
  linarith

private theorem scale_monotone {d : ℕ} (Q : ℝ) (μ : Fin d → ℂ) {a b : ℝ}
    (hμ : ∀ j,-1 ≤ (μ j).re) (ha : 1 < a) (hab : a ≤ b) :
    scale Q μ a 0 ≤ scale Q μ b 0 := by
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j _
  apply log_le_log (div_pos (rad_pos _ 0 (hμ j) ha) (by positivity))
  exact div_le_div_of_nonneg_right (rad_monotone _ (hμ j) ha.le hab) (by positivity)

/-- The smallest conductor scale is uniformly larger than 2.33 per real gamma
factor. The rational inequality of nineteenth powers certifies the logarithm. -/
theorem scale_lower {d : ℕ} {Q m : ℝ} (μ : Fin d → ℂ) (hQ : 1 ≤ Q)
    (hm : 33 ≤ m) (hμ : ∀ j,-1 ≤ (μ j).re) : 2.33*d ≤ scale Q μ (2*m) 0 := by
  have l := log_le_log (show (0:ℝ)<2^64 by positivity)
    (show (2:ℝ)^64 ≤ 10.34^19 by norm_num)
  rw [log_pow,log_pow] at l
  norm_num at l
  have lx : (2.33:ℝ) ≤ log 10.34 := by linarith [log_two_gt_d9]
  have one (j : Fin d) : (2.33:ℝ) ≤ log (radius (μ j) (2*m) 0/(2*π)) := by
    apply lx.trans (log_le_log (by norm_num) _)
    rw [le_div_iff₀ (by positivity)]
    linarith [rad0_bound (μ j) (a:=2*m) (hμ j),pi_lt_d4]
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => one j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at sum
  unfold scale
  linarith [log_nonneg hQ]

/-- A bounded imaginary displacement at real part three costs at most .081 per
archimedean gamma parameter compared to the high real abscissa. -/
theorem scale_shift {d : ℕ} (Q : ℝ) (μ : Fin d → ℂ) {m t : ℝ} (hm : 33 ≤ m)
    (ht : |t| ≤ m/(2*π)) (hμ : ∀ j,-1 ≤ (μ j).re) :
    scale Q μ 3 t ≤ scale Q μ (2*m) 0+0.081*d := by
  have one (j : Fin d) : log (radius (μ j) 3 t/(2*π)) ≤
      log (radius (μ j) (2*m) 0/(2*π))+0.081 := by
    let r := radius (μ j) (2*m) 0
    have low : 2*m-1 ≤ r := rad0_bound _ (hμ j)
    have rp : 0 < r := by linarith
    have ct : |t| ≤ 0.081*r := by
      apply ht.trans
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg rp.le (sub_nonneg.mpr pi_gt_d2.le)]
    have rr := rad_monotone (μ j) (a:=3) (b:=2*m) (hμ j) (by norm_num) (by linarith)
    have ratio : radius (μ j) 3 t/(2*π) ≤ (r/(2*π))*(1+0.081) := by
      rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right (by positivity)]
      change radius (μ j) 3 0 ≤ r at rr
      linarith [rad_shift (μ j) 3 t]
    have h := log_le_log (div_pos (rad_pos _ t (hμ j) (by norm_num)) (by positivity)) ratio
    rw [log_mul (by positivity) (by positivity)] at h
    have small := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1+0.081)
    dsimp [r] at *
    linarith
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => one j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at sum
  unfold scale
  linarith

/-- The large real-axis difference from the standard Hadamard, gamma and Euler
logarithmic derivative bounds. These real bounds include the cost of two poles. -/
theorem wide {d : ℕ} {m Q Sbig Ssmall : ℝ} (μ : Fin d → ℂ) (hQ : 1 ≤ Q) (hm : 33 ≤ m)
    (hd : 1 ≤ d) (hμ : ∀ j,-1 ≤ (μ j).re)
    (big : scale Q μ (2*m) 0/2 - d/(2*m-1)-0.001*d ≤ Sbig)
    (small : Ssmall ≤ scale Q μ (m/2) 0/2 + d/(m/2-1)+0.001*d+1/(m/2)+1/(m/2-1)) :
    0.21*scale Q μ (2*m) 0 ≤ Sbig-0.481*Ssmall := by
  have dd : 1 ≤ (d:ℝ) := by exact_mod_cast hd
  have base := scale_lower μ hQ hm hμ
  have mon := scale_monotone Q μ hμ (show 1<m/2 by linarith) (show m/2≤2*m by linarith)
  have h1 : (d:ℝ)/(2*m-1) ≤ d/65 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    linarith
  have h2 : (d:ℝ)/(m/2-1) ≤ 2*d/31 := by
    rw [show 2*(d:ℝ)/31=d/(31/2) by ring]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    linarith
  have h3 : 1/(m/2)+1/(m/2-1) ≤ 4/31 := by
    have a : (1:ℝ)/(m/2) ≤ 2/31 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have b : (1:ℝ)/(m/2-1) ≤ 2/31 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  linarith

/-- The two shifted logarithmic derivatives control the whole allowed loss at
one frequency. Both pole terms and the rounded-up .128 hyperbolic loss are paid. -/
theorem local_charge {d : ℕ} {m Q c Sp Sm : ℝ} (μ : Fin d → ℂ) (hQ : 1 ≤ Q) (hm : 33 ≤ m)
    (hd : 1 ≤ d) (hμ : ∀ j,-1 ≤ (μ j).re) (hc : |c| ≤ m/(2*π))
    (p : Sp ≤ scale Q μ 3 c/2 + d/2+0.65*d+5/6)
    (n : Sm ≤ scale Q μ 3 (-c)/2 + d/2+0.65*d+5/6) :
    (0.128/0.3)*(Sp+Sm) ≤ 1.17*scale Q μ (2*m) 0 := by
  have dd : 1 ≤ (d:ℝ) := by exact_mod_cast hd
  have base := scale_lower μ hQ hm hμ
  have ap := scale_shift Q μ hm hc hμ
  have an := scale_shift Q μ hm (t := -c) (by simpa using hc) hμ
  linarith

/-- The paired Hadamard kernel sum at a vertical point. -/
noncomputable def poisson {ι : Type*} (β γ : ι → ℝ) (a t : ℝ) : ℝ :=
  ∑' i,kernel a (β i) (t-γ i)

private theorem at_zero {ι : Type*} (β γ : ι → ℝ) (a : ℝ) :
    poisson β γ a 0 = ∑' i,kernel a (β i) (γ i) := by
  simp only [poisson,zero_sub,kernel,even_two.neg_pow]

/-- The final theorem, with the analytic hypotheses in the form of direct
Hadamard bounds on log derivatives. The finite shifts, conductor and degree
may vary freely; the high-abscissa error admits one reflected pair of poles. -/
theorem analytic_transfer {ι : Type*} {d : ℕ} (β γ : ι → ℝ) (reflect : ι ≃ ι)
    (μ : Fin d → ℂ) {Q T : ℝ} {n : ℕ} (hQ : 1 ≤ Q) (hd : 1 ≤ d) (hμ : ∀ j,-1 ≤ (μ j).re)
    (hn : 0<n) (hT : 0 ≤ T) (cap : (n:ℝ) ≤ T^2)
    (strip : ∀ i,0 ≤ β i ∧ β i ≤ 1)
    (refRe : ∀ i,β (reflect i)=1-β i) (refIm : ∀ i,γ (reflect i)=γ i)
    (verified : ∀ i,|γ i| ≤ T → β i=1/2) (higher : ∃ i,T < |γ i|)
    (liSum : Summable (fun i => LiReflectedPair.liTerm n (β i) (γ i)))
    (poissonSum : ∀ a:ℝ,3 ≤ a → ∀ t,Summable (fun i => kernel a (β i) (t-γ i)))
    (high : ∀ a:ℝ,16.5 ≤ a →
      scale Q μ a 0/2 - d/(a-1)-0.001*d ≤ poisson β γ a 0 ∧
      poisson β γ a 0 ≤ scale Q μ a 0/2 + d/(a-1)+0.001*d+1/a+1/(a-1))
    (three : ∀ t:ℝ,poisson β γ 3 t ≤ scale Q μ 3 t/2 + d/2+0.65*d+5/6) :
    0 < ∑' i,LiReflectedPair.liTerm n (β i) (γ i) := by
  have h0 (a : ℝ) (ha : 3 ≤ a) : Summable (fun i => kernel a (β i) (γ i)) := by
    simpa only [zero_sub,kernel,even_two.neg_pow] using poissonSum a ha 0
  have ch (k : ℕ) : Summable (fun i => charge n k (β i) (γ i)) := by
    exact ((poissonSum 3 le_rfl (centre n k)).add (poissonSum 3 le_rfl (-centre n k))).mul_left _
  apply all_heights β γ reflect hn hT cap strip refRe refIm verified higher liSum
  intro big
  have m : 33 ≤ (n:ℝ) := by exact_mod_cast big
  let D := scale Q μ (2*n) 0
  have pos : 0 < D := by
    have dd : 1 ≤ (d:ℝ) := by exact_mod_cast hd
    dsimp [D]; linarith [scale_lower μ hQ m hμ]
  refine ⟨D,pos,h0 _ (by linarith),h0 _ (by linarith),(fun k _ => ch k),?_,?_⟩
  · have lo := (high (2*n) (by linarith)).1
    have hi := (high (n/2) (by linarith)).2
    simpa only [at_zero] using wide μ hQ m hd hμ lo hi
  · intro k hk
    have kp : 0<k := (Finset.mem_Icc.mp hk).1
    have fp : 0 < freq k := by unfold freq; positivity
    have cpos : 0 ≤ centre n k := div_nonneg (by positivity) fp.le
    have hc : |centre n k| ≤ (n:ℝ)/(2*π) := by
      rw [abs_of_nonneg cpos]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have one : 1 ≤ (k:ℝ) := by exact_mod_cast kp
      unfold freq; nlinarith [mul_nonneg (sub_nonneg.mpr one) pi_pos.le]
    have bound := local_charge μ hQ m hd hμ hc (three _) (three _)
    change (∑' i,(0.128/0.3)*(kernel 3 (β i) (centre n k-γ i)+kernel 3 (β i) (-centre n k-γ i))) ≤ _
    rw [((poissonSum 3 le_rfl (centre n k)).add (poissonSum 3 le_rfl (-centre n k))).tsum_mul_left,
      (poissonSum 3 le_rfl (centre n k)).tsum_add (poissonSum 3 le_rfl (-centre n k))]
    exact bound

#print axioms scale_lower
#print axioms scale_shift
#print axioms wide
#print axioms local_charge
#print axioms analytic_transfer

end LiPoissonInputs
