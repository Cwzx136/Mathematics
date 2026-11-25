import Research.TiltedWidth

/-! Numerical margins for the two explicit tilted elliptic polynomials. -/
noncomputable section
namespace ERH.TiltedElliptic
open ERH.Bump ERH.TiltedGain ERH.TiltedWidth

theorem octic_zeros (F : ℂ → ℂ)
    (estimate : Budget F (5083/5000) (306229/500000) (82457203/186000000) (1079/20000) (1/(2363/400)))
    (reflect : ∀ β t : ℝ, 0 < β → β < 1 → F ⟨β,t⟩ = 0 → F ⟨1-β,t⟩ = 0) :
    ∃ H : ℝ, ∀ β t : ℝ, H ≤ Real.log |t| → 0 < β → β < 1 → F ⟨β,t⟩ = 0 →
      1/(2363/400) < Real.log |t| * min β (1-β) := by
  exact rational_transfer F (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [momentPolynomial,upperMoment]) estimate reflect

theorem degreeTwelve_zeros (F : ℂ → ℂ)
    (estimate : Budget F (639/625) (152703/250000) (41475929/93000000) (1079/20000) (1/(7359/1250)))
    (reflect : ∀ β t : ℝ, 0 < β → β < 1 → F ⟨β,t⟩ = 0 → F ⟨1-β,t⟩ = 0) :
    ∃ H : ℝ, ∀ β t : ℝ, H ≤ Real.log |t| → 0 < β → β < 1 → F ⟨β,t⟩ = 0 →
      1/(7359/1250) < Real.log |t| * min β (1-β) := by
  exact rational_transfer F (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [momentPolynomial,upperMoment]) estimate reflect

#print axioms degreeTwelve_zeros
end ERH.TiltedElliptic
