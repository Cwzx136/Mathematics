import Research.Stechkin

/-! Exact positive real-part certificates for admissible logarithmic derivative
polynomials in the Heath--Brown--Zaman convention. -/
namespace ERH.AdmissibleTaylor
noncomputable section

/-- On scaling w=u/z, the right half-plane Re(z)≥u enters the closed circle
|w−1/2|≤1/2. Lean's total inverse also gives the correct implication at u=z=0. -/
theorem scale_to_disk {u : ℝ} {z : ℂ} (hu : 0 ≤ u) (hz : u ≤ z.re) :
    Complex.normSq ((u:ℂ)/z) ≤ ((u:ℂ)/z).re := by
  simp only [Complex.normSq_div, Complex.normSq_ofReal, Complex.div_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz hu) (Complex.normSq_nonneg z)

def p2 (w : ℂ) := w+w^2

def p4 (w : ℂ) := w+w^2+((4/5:ℝ):ℂ)*w^3+((2/5:ℝ):ℂ)*w^4

def p8 (w : ℂ) := w+w^2+((12/13:ℝ):ℂ)*w^3+((10/13:ℝ):ℂ)*w^4+
  ((80/143:ℝ):ℂ)*w^5+((48/143:ℝ):ℂ)*w^6+((64/429:ℝ):ℂ)*w^7+((16/429:ℝ):ℂ)*w^8

private def gap (w : ℂ) := w.re-Complex.normSq w

theorem p2_certificate (w : ℂ) : (p2 w).re = 2*w.re^2+gap w := by
  simp [p2,gap,Complex.normSq_apply,Complex.mul_re,pow_two]
  ring

theorem p4_certificate (w : ℂ) :
    (p4 w).re = (16/5)*w.re^4 + (2/5)*(gap w)^2 +
       gap w*((16/5)*w.re^2+(8/5)*w.re+1) := by
  simp [p4,gap,Complex.normSq_apply,pow_succ,Complex.mul_re,Complex.mul_im]
  ring

theorem p8_certificate (w : ℂ) :
    (p8 w).re = (2048/429)*w.re^8 + (16/429)*(gap w)^4
      +(gap w)^3*((512/429)*w.re^2+(128/143)*w.re+48/143)
      +(gap w)^2*((2560/429)*w.re^4+(2048/429)*w.re^3+(448/143)*w.re^2+
                    (256/143)*w.re+10/13)
      +gap w*((4096/429)*w.re^6+(2048/429)*w.re^5+(1280/429)*w.re^4+
                (896/429)*w.re^3+(224/143)*w.re^2+(16/13)*w.re+1) := by
  simp [p8,gap,Complex.normSq_apply,pow_succ,Complex.mul_re,Complex.mul_im]
  ring

theorem p2_nonneg {w : ℂ} (hw : Complex.normSq w ≤ w.re) : 0 ≤ (p2 w).re := by
  have hg : 0 ≤ gap w := sub_nonneg.2 hw
  rw [p2_certificate]
  positivity

theorem p4_nonneg {w : ℂ} (hw : Complex.normSq w ≤ w.re) : 0 ≤ (p4 w).re := by
  have hg : 0 ≤ gap w := sub_nonneg.2 hw
  have ha : 0 ≤ w.re := (Complex.normSq_nonneg _).trans hw
  rw [p4_certificate]
  positivity

theorem p8_nonneg {w : ℂ} (hw : Complex.normSq w ≤ w.re) : 0 ≤ (p8 w).re := by
  have hg : 0 ≤ gap w := sub_nonneg.2 hw
  have ha : 0 ≤ w.re := (Complex.normSq_nonneg _).trans hw
  rw [p8_certificate]
  positivity

theorem scaled_polynomials_nonneg {u : ℝ} {z : ℂ} (hu : 0 ≤ u) (hz : u ≤ z.re) :
    0 ≤ (p2 ((u:ℂ)/z)).re ∧ 0 ≤ (p4 ((u:ℂ)/z)).re ∧ 0 ≤ (p8 ((u:ℂ)/z)).re := by
  have h := scale_to_disk hu hz
  exact ⟨p2_nonneg h,p4_nonneg h,p8_nonneg h⟩

end
end ERH.AdmissibleTaylor
