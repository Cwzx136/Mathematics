import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Tactic

/-! Absolute interchange and subtraction for countable real Hadamard zero kernels under an
actual finite signed measure. All analytic integrability hypotheses refer to its total variation. -/

open MeasureTheory
open scoped MeasureTheory
namespace ERH.SignedHadamard

/-- The signed integral here is mathlib's vector measure integral with its canonical real pairing. -/
noncomputable abbrev average {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) (f : X → ℝ) :=
  ∫ᵛ x, f x ∂<•ν

theorem average_jordan {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) (f : X → ℝ)
    (hi : Integrable f ν.totalVariation) :
    average ν f = (∫ x, f x ∂ν.toJordanDecomposition.posPart) -
      (∫ x, f x ∂ν.toJordanDecomposition.negPart) := by
  have h := integrable_add_measure.mp hi
  have hp : ν.toJordanDecomposition.posPart.toSignedMeasure.Integrable f := by
    simpa [VectorMeasure.Integrable] using h.1
  have hn : ν.toJordanDecomposition.negPart.toSignedMeasure.Integrable f := by
    simpa [VectorMeasure.Integrable] using h.2
  unfold average
  conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition, JordanDecomposition.toSignedMeasure]
  rw [VectorMeasure.integral_sub_vectorMeasure hp hn]
  simp

/-- Nonnegative zero summands and integrability of their total against `|ν|` justify
exchange with a signed ordinate shift, preserving convergence of the full unordered sum. -/
theorem interchange {ι X : Type*} [Countable ι] [MeasurableSpace X] (ν : SignedMeasure X)
    (K : ι → X → ℝ) (S : X → ℝ) (hK : ∀ i, Measurable (K i))
    (hpos : ∀ i x, 0 ≤ K i x) (hi : Integrable S ν.totalVariation)
    (hs : ∀ᵐ x ∂ν.totalVariation, HasSum (fun i => K i x) (S x)) :
    HasSum (fun i => average ν (K i)) (average ν S) := by
  rw [ν.totalVariation_eq_variation] at hi hs
  have htotal : Integrable (fun x => ∑' i, K i x) ν.variation := hi.congr
    (hs.mono (fun _ h => h.tsum_eq.symm))
  exact VectorMeasure.hasSum_integral_of_dominated_convergence (μ := ν) K
    (fun i => (hK i).aestronglyMeasurable) (fun i => .of_forall (fun x => by
      simp [Real.norm_eq_abs, abs_of_nonneg (hpos i x)]))
    (hs.mono (fun _ h => h.summable)) htotal hs

/-- A pointwise Hadamard identity, with a nonnegative zero sum controlled by the
difference of two integrable functions, can be integrated and subtracted from the original
identity at its center. The resulting kernel differences converge absolutely. -/
theorem difference {ι X : Type*} [Countable ι] [MeasurableSpace X] (ν : SignedMeasure X)
    (K : ι → X → ℝ) (B D : X → ℝ) (center : X) (hK : ∀ i, Measurable (K i))
    (hpos : ∀ i x, 0 ≤ K i x) (hB : Integrable B ν.totalVariation)
    (hD : Integrable D ν.totalVariation)
    (hshift : ∀ᵐ x ∂ν.totalVariation, HasSum (fun i => K i x) (B x-D x))
    (hcenter : HasSum (fun i => K i center) (B center-D center)) :
    Summable (fun i => |average ν (K i) - K i center|) ∧
    average ν D - D center = (average ν B - B center) -
      ∑' i, (average ν (K i) - K i center) := by
  have hp := (interchange ν K (fun x => B x-D x) hK hpos (hB.sub hD) hshift).sub hcenter
  refine ⟨hp.summable.abs, ?_⟩
  have hv := hp.tsum_eq
  change (∑' i, (average ν (K i)-K i center)) = average ν (fun x => B x-D x) -
    (B center-D center) at hv
  rw [hv]
  unfold average
  rw [ν.totalVariation_eq_variation] at hB hD
  rw [VectorMeasure.integral_fun_sub hB hD]
  ring

/-- The actual real part of the simple pole of a zero with real part `β` and
ordinate `γ`, at the shifted ordinate `y+a z`. -/
noncomputable def zeroKernel (s y a β γ z : ℝ) : ℝ :=
  (s-β) / ((s-β)^2 + (y+a*z-γ)^2)

theorem zeroKernel_difference {ι : Type*} [Countable ι] (ν : SignedMeasure ℝ)
    (β γ : ι → ℝ) (s y a : ℝ) (hβ : ∀ i, β i ≤ s) (B D : ℝ → ℝ)
    (hB : Integrable B ν.totalVariation) (hD : Integrable D ν.totalVariation)
    (hshift : ∀ᵐ z ∂ν.totalVariation, HasSum (fun i => zeroKernel s y a (β i) (γ i) z) (B z-D z))
    (hcenter : HasSum (fun i => zeroKernel s y a (β i) (γ i) 0) (B 0-D 0)) :
    Summable (fun i => |average ν (zeroKernel s y a (β i) (γ i)) -
      zeroKernel s y a (β i) (γ i) 0|) ∧
    average ν D - D 0 = (average ν B - B 0) -
      ∑' i, (average ν (zeroKernel s y a (β i) (γ i)) - zeroKernel s y a (β i) (γ i) 0) := by
  apply difference ν _ B D 0 _ _ hB hD hshift hcenter
  · intro i
    unfold zeroKernel
    fun_prop
  · exact fun i _ => div_nonneg (sub_nonneg.mpr (hβ i)) (add_nonneg (sq_nonneg _) (sq_nonneg _))

end ERH.SignedHadamard

#print axioms ERH.SignedHadamard.average_jordan
#print axioms ERH.SignedHadamard.zeroKernel_difference
