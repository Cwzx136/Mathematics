import Research.Prior.LiHadamardBase
import Research.Prior.LiGammaRealPart
import Research.Prior.LiEulerCoefficients

namespace LiHadamardTransfer
open Real LiGammaRealPart LiHadamardBase LiPoissonInputs

/-- Coefficient-level endpoint for applications. The arithmetic data are the
actual prime-power logarithmic derivative coefficients and their local norm
bound. The analytic identity includes every gamma factor and any pole pair. -/
theorem coefficient_positive {ι : Type*} {d : ℕ} (β γ : ι→ℝ) (reflect : ι≃ι)
    (μ : Fin d→ℂ) {Q T : ℝ} {n : ℕ} (hQ : 1≤Q) (hd : 1≤d) (hμ : ∀ j,-1≤(μ j).re)
    (hn : 0<n) (hT : 0≤T) (cap : (n:ℝ)≤T^2) (strip : ∀ i,0≤β i ∧ β i≤1)
    (refRe : ∀ i,β (reflect i)=1-β i) (refIm : ∀ i,γ (reflect i)=γ i)
    (verified : ∀ i,|γ i| ≤ T → β i=1/2) (higher : ∃ i,T < |γ i|)
    (liSum : Summable (fun i => LiReflectedPair.liTerm n (β i) (γ i)))
    (poissonSum : ∀ a:ℝ,3≤a → ∀ t,Summable (fun i => LiAllHeights.kernel a (β i) (t-γ i)))
    (which : Option ℝ) (coeff : ℕ→ℂ)
    (bound : ∀ k:ℕ,‖coeff k‖ ≤ d*k*ArithmeticFunction.vonMangoldt k)
    (hadamard : ∀ a t:ℝ,3≤a → poisson β γ a t=log Q/2+(∑ j,gammaTerm (μ j) a t)-
      (∑' k:ℕ,LiEulerCoefficients.term coeff a t k).re+pole which a t) :
    0 < ∑' i,LiReflectedPair.liTerm n (β i) (γ i) := by
  apply LiHadamardBase.positive (fun _ h => real_digamma h) β γ reflect μ hQ hd hμ hn hT cap strip refRe refIm verified higher liSum
    poissonSum which (fun a t=> -(∑' k:ℕ,LiEulerCoefficients.term coeff a t k).re)
  · intro a t h
    simpa only [sub_eq_add_neg] using hadamard a t h
  · intro a t h
    rw [abs_neg]
    exact (LiEulerCoefficients.majorant coeff bound t h).2

#print axioms coefficient_positive

end LiHadamardTransfer
