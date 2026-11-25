import Research.Prior.LiHadamardTransfer
import Research.Prior.LiDivisorConvergence

namespace LiFullDivisorTransfer
open Real LiGammaRealPart LiHadamardBase LiHadamardTransfer LiPoissonInputs

/-- The full analytic endpoint. No separate convergence, zero-counting, or
existence-of-higher-zeros assumption is needed. The hypotheses consist of the
critical strip, horizontal reflection, the Euler coefficient bound, the exact
Hadamard identity, and the finite height being verified. -/
theorem from_hadamard {ι : Type*} {d : ℕ} (β γ : ι→ℝ) (reflect : ι≃ι)
    (μ : Fin d→ℂ) {Q T : ℝ} {n : ℕ} (hQ : 1≤Q) (hd : 1≤d) (hμ : ∀ j,-1≤(μ j).re)
    (hn : 0<n) (hT : 0≤T) (cap : (n:ℝ)≤T^2) (strip : ∀ i,0≤β i ∧ β i≤1)
    (refRe : ∀ i,β (reflect i)=1-β i) (refIm : ∀ i,γ (reflect i)=γ i)
    (verified : ∀ i,|γ i| ≤ T → β i=1/2) (which : Option ℝ) (coeff : ℕ→ℂ)
    (bound : ∀ k:ℕ,‖coeff k‖ ≤ d*k*ArithmeticFunction.vonMangoldt k)
    (hadamard : ∀ a t:ℝ,3≤a → poisson β γ a t=log Q/2+(∑ j,gammaTerm (μ j) a t)-
      (∑' k:ℕ,LiEulerCoefficients.term coeff a t k).re+pole which a t) :
    0 < ∑' i,LiReflectedPair.liTerm n (β i) (γ i) := by
  have hpos (a : ℝ) (ha : 1000≤a) : 1<poisson β γ a 0 := by
    have a3 : 3≤a := by linarith
    have E := (LiEulerCoefficients.majorant coeff bound 0 a3).2
    let u := (∑' k:ℕ,LiEulerCoefficients.term coeff a 0 k).re
    have ee : |-u| ≤ 0.001*d := by
      rw [abs_neg]
      have h := mul_le_mul_of_nonneg_left (LiEulerGammaBounds.euler_high (show 15≤a-1 by linarith)).le
        (show 0≤(d:ℝ) by positivity)
      dsimp [u]; linarith
    have lower := (LiHadamardBase.error (fun _ h=>real_digamma h) μ which hμ a3
      (by simpa only [sub_eq_add_neg] using hadamard a 0 a3) ee).1
    have hH := scale_lower μ hQ (show 33≤a/2 by linarith) hμ
    rw [show 2*(a/2)=a by ring] at hH
    have dd : 1≤(d:ℝ) := by exact_mod_cast hd
    have hsmall : (d:ℝ)/(a-1) ≤ d/999 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      linarith
    linarith
  have base := LiDivisorConvergence.basic_summable β γ strip (hpos 1000 le_rfl)
  exact coefficient_positive β γ reflect μ hQ hd hμ hn hT cap strip refRe refIm verified
    (LiDivisorConvergence.unbounded β γ strip hpos T) (LiDivisorConvergence.li_summable β γ strip base n)
    (fun _ ha t=>LiDivisorConvergence.poisson_summable β γ strip base ha t) which coeff bound hadamard

/-- The input is now the Hadamard identity and the actual finite Euler
factors, with residue degrees and repeated local parameters explicit. -/
theorem from_local_factors {ι : Type*} {d : ℕ} (β γ : ι→ℝ) (reflect : ι≃ι)
    (μ : Fin d→ℂ) {Q T : ℝ} {n : ℕ} (hQ : 1≤Q) (hd : 1≤d) (hμ : ∀ j,-1≤(μ j).re)
    (hn : 0<n) (hT : 0≤T) (cap : (n:ℝ)≤T^2) (strip : ∀ i,0≤β i ∧ β i≤1)
    (refRe : ∀ i,β (reflect i)=1-β i) (refIm : ∀ i,γ (reflect i)=γ i)
    (verified : ∀ i,|γ i| ≤ T → β i=1/2) (which : Option ℝ) (coeff : ℕ→ℂ)
    (places : ℕ→ℕ) (f l : (p:ℕ)→Fin (places p)→ℕ) (α : (p:ℕ)→(v:Fin (places p))→Fin (l p v)→ℂ)
    (rootBound : ∀ p:ℕ,p.Prime → ∀ v j,‖α p v j‖ ≤ (p:ℝ)^(f p v))
    (degree : ∀ p:ℕ,p.Prime → (∑ v,f p v*l p v)≤d)
    (support : ∀ k:ℕ,(¬∃p e:ℕ,p.Prime ∧ 0<e ∧ p^e=k) → coeff k=0)
    (localIdentity : ∀ p k:ℕ,p.Prime → 0<k → coeff (p^k)=
      ((log (p:ℝ):ℝ):ℂ)*(∑ v,if f p v ∣ k then (f p v:ℂ)*∑ j,(α p v j)^(k/f p v) else 0))
    (hadamard : ∀ a t:ℝ,3≤a → poisson β γ a t=log Q/2+(∑ j,gammaTerm (μ j) a t)-
      (∑' k:ℕ,LiEulerCoefficients.term coeff a t k).re+pole which a t) :
    0 < ∑' i,LiReflectedPair.liTerm n (β i) (γ i) :=
  from_hadamard β γ reflect μ hQ hd hμ hn hT cap strip refRe refIm verified which coeff
    (LiEulerCoefficients.rational_bound coeff places f l α rootBound degree support localIdentity) hadamard

#print axioms from_hadamard
#print axioms from_local_factors

end LiFullDivisorTransfer
