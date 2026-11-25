import Research.SquarePrior
import Research.TiltedGain
import Research.RankSelfTilt

/-! The direct symmetric-square certificate at its limiting displacement. -/
noncomputable section
namespace ERH.SquarePriorGain
open ERH.Bump ERH.TiltedGain MeasureTheory Set

def H (t : ℝ) := ∫ x in (0:ℝ)..1, h x * Real.exp (-(t*x))

theorem continuous_H : Continuous H := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  dsimp [Function.uncurry,h]
  fun_prop

theorem H_zero : H 0 = 315/796 := by
  simpa [H,major,upperMoment] using major_integral (0:ℝ)

theorem certified_prior {l : ℝ} (hl : 0 < l)
    (estimate : ∀ a ∈ Ioo (0:ℝ) l, ∀ W > 0,
      H ((l-a)/W)-(EllipticBernstein.SquarePrior.pole:ℝ)*H (-a/W) ≤
        W*(EllipticBernstein.SquarePrior.slope:ℝ)) :
    4239/50000 < l := by
  have P : (EllipticBernstein.SquarePrior.pole:ℝ) = 325909/500000 := by
    rw [EllipticBernstein.SquarePrior.coefficients.2.1]; norm_num
  have G : (EllipticBernstein.SquarePrior.slope:ℝ) = 139/186 := by
    rw [EllipticBernstein.SquarePrior.coefficients.2.2]; norm_num
  have hlim := ERH.RankSelfTilt.limiting_displacement continuous_H hl estimate (t:=83/100) (by norm_num)
  rw [H_zero,P,G] at hlim
  have u : H (-(83/100)) ≤ upperMoment (83/100) := by
    simpa [H] using (upper_laplace (by norm_num : 0 ≤ (83/100:ℝ)) (by norm_num))
  norm_num [upperMoment] at u
  linarith

#print axioms certified_prior
end ERH.SquarePriorGain
