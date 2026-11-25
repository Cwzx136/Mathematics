import Research.Prior.LiPoissonInputs
import Research.Prior.LiEulerGammaBounds

/-! The threshold-free Li implication from the actual real parts of gamma log
derivatives in the Hadamard formula and the Dirichlet-series Euler majorant. -/
namespace LiHadamardBase
open Real LiEulerGammaBounds LiPoissonInputs

noncomputable def arg (μ : ℂ) (a t : ℝ) : ℂ := ((a:ℂ)+μ+(t:ℂ)*Complex.I)/2
noncomputable def gammaTerm (μ : ℂ) (a t : ℝ) : ℝ := ((Complex.digamma (arg μ a t)).re-log π)/2

/-- Uniform error for one real gamma factor with its actual complex parameter. -/
theorem gamma_error (psi : ∀ z:ℂ,0<z.re → |(Complex.digamma z).re-log ‖z‖| ≤ 1/z.re) {μ : ℂ} {a t : ℝ} (hμ : -1≤μ.re) (ha : 3≤a) :
    |gammaTerm μ a t-log (radius μ a t/(2*π))/2| ≤ 1/(a-1) := by
  have e : (arg μ a t).re=(a+μ.re)/2 := by simp [arg,Complex.div_ofNat_re,Complex.mul_re]
  have h : 0 < (arg μ a t).re := by rw [e]; linarith
  have gp := psi _ h
  have r : 0 < radius μ a t := by
    have q := Complex.re_le_norm ((a:ℂ)+μ+(t:ℂ)*Complex.I)
    simp [Complex.mul_re] at q
    unfold radius; linarith
  have q : ‖arg μ a t‖=radius μ a t/2 := by simp [arg,radius,norm_div]
  rw [q,e,log_div r.ne' (by norm_num)] at gp
  have form : gammaTerm μ a t-log (radius μ a t/(2*π))/2 =
      ((Complex.digamma (arg μ a t)).re - (log (radius μ a t)-log 2))/2 := by
    unfold gammaTerm
    rw [log_div r.ne' (by positivity),log_mul (by norm_num) pi_pos.ne']; ring
  rw [form,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have bound := div_le_div_of_nonneg_right gp (by norm_num : (0:ℝ)≤2)
  apply bound.trans
  rw [div_div,show (a+μ.re)/2*2=a+μ.re by ring]
  exact div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)

noncomputable def pole (wherePole : Option ℝ) (a t : ℝ) : ℝ :=
  match wherePole with
  | none => 0
  | some τ => LiAllHeights.kernel a 0 (t-τ)+LiAllHeights.kernel a 1 (t-τ)

theorem pole_bound (which : Option ℝ) {a t : ℝ} (ha : 3≤a) :
    0 ≤ pole which a t ∧ pole which a t ≤ 1/a+1/(a-1) := by
  have ap : 0<a := by linarith
  have a1 : 0<a-1 := by linarith
  cases which with
  | none => simp only [pole]; exact ⟨le_rfl,by positivity⟩
  | some τ =>
    have k {u : ℝ} (h : 0<u) : 0 ≤ u/(u^2+(t-τ)^2) ∧ u/(u^2+(t-τ)^2) ≤ 1/u := by
      refine ⟨by positivity,?_⟩
      rw [div_le_div_iff₀ (by positivity) h]; nlinarith [sq_nonneg (t-τ)]
    simpa only [pole,LiAllHeights.kernel,sub_zero] using
      And.intro (add_nonneg (k ap).1 (k a1).1) (add_le_add (k ap).2 (k a1).2)

/-- Summed Hadamard error for a translated pair of optional poles and any gamma
array with Re μ≥−1. The finite Euler factor is bounded separately by its
Dirichlet majorant. -/
theorem error (psi : ∀ z:ℂ,0<z.re → |(Complex.digamma z).re-log ‖z‖| ≤ 1/z.re) {d : ℕ} (μ : Fin d → ℂ) {Q a t E S c : ℝ} (which : Option ℝ)
    (hμ : ∀ j,-1≤(μ j).re) (ha : 3≤a)
    (identity : S=log Q/2+(∑ j,gammaTerm (μ j) a t) + E + pole which a t)
    (he : |E|≤c*d) :
    scale Q μ a t/2 - d/(a-1)-c*d ≤ S ∧
    S ≤ scale Q μ a t/2 + d/(a-1)+c*d+1/a+1/(a-1) := by
  let M := fun j => log (radius (μ j) a t/(2*π))/2
  have lo := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => (abs_le.mp (gamma_error psi (t:=t) (hμ j) ha)).1)
  have hi := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => (abs_le.mp (gamma_error psi (t:=t) (hμ j) ha)).2)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_sub_distrib] at lo hi
  have sumM : (∑ j,M j)=(∑ j,log (radius (μ j) a t/(2*π)))/2 := by simp [M,Finset.sum_div]
  change _ ≤ (∑ j,gammaTerm (μ j) a t)-(∑ j,M j) at lo
  change (∑ j,gammaTerm (μ j) a t)-(∑ j,M j) ≤ _ at hi
  rw [sumM] at lo hi
  unfold scale
  constructor <;> linarith [(abs_le.mp he).1,(abs_le.mp he).2,(pole_bound (t:=t) which ha).1,
    (pole_bound (t:=t) which ha).2,show (d:ℝ)*(1/(a-1))=d/(a-1) by ring]

/-- Given the actual Hadamard-log-derivative identity and the universal Euler
coefficient majorant for a completed L-function, every verified height produces
its full quadratic prefix of positive real Li coefficients. -/
theorem positive (psi : ∀ z:ℂ,0<z.re → |(Complex.digamma z).re-log ‖z‖| ≤ 1/z.re) {ι : Type*} {d : ℕ} (β γ : ι → ℝ) (reflect : ι ≃ ι)
    (μ : Fin d → ℂ) {Q T : ℝ} {n : ℕ} (hQ : 1≤Q) (hd : 1≤d) (hμ : ∀ j,-1≤(μ j).re)
    (hn : 0<n) (hT : 0≤T) (cap : (n:ℝ) ≤ T^2) (strip : ∀ i,0≤β i ∧ β i≤1)
    (refRe : ∀ i,β (reflect i)=1-β i) (refIm : ∀ i,γ (reflect i)=γ i)
    (verified : ∀ i,|γ i| ≤ T → β i=1/2) (higher : ∃ i,T < |γ i|)
    (liSum : Summable (fun i => LiReflectedPair.liTerm n (β i) (γ i)))
    (poissonSum : ∀ a:ℝ,3≤a → ∀ t,Summable (fun i => LiAllHeights.kernel a (β i) (t-γ i)))
    (which : Option ℝ) (E : ℝ→ℝ→ℝ)
    (hadamard : ∀ a t:ℝ,3≤a → poisson β γ a t=log Q/2+(∑ j,gammaTerm (μ j) a t)+E a t+pole which a t)
    (euler : ∀ a t:ℝ,3≤a → |E a t|≤d*eulerRatio (a-1)) :
    0 < ∑' i,LiReflectedPair.liTerm n (β i) (γ i) := by
  apply analytic_transfer β γ reflect μ hQ hd hμ hn hT cap strip refRe refIm verified higher liSum poissonSum
  · intro a ha
    have a3 : 3≤a := by linarith
    have h := euler a 0 a3
    have k := mul_le_mul_of_nonneg_left (euler_high (s:=a-1) (by linarith)).le
      (show 0≤(d:ℝ) by positivity)
    exact error psi μ which hμ a3 (hadamard a 0 a3) (by linarith : |E a 0|≤0.001*d)
  · intro t
    have h := euler 3 t le_rfl
    norm_num at h
    have k := mul_le_mul_of_nonneg_left euler_at_two.le (show 0≤(d:ℝ) by positivity)
    have p := (error psi μ which hμ (a:=3) (by norm_num) (hadamard 3 t le_rfl)
      (by linarith : |E 3 t|≤0.65*d)).2
    linarith

#print axioms gamma_error
#print axioms pole_bound
#print axioms error
#print axioms positive

end LiHadamardBase
