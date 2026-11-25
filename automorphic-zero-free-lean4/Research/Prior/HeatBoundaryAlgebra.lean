import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Algebraic gap estimates for the full height argument in Theorem hol:profile. -/
namespace HeatBoundaryAlgebra

/-- The difference of two products of squared distances to a reflected pair. -/
theorem reflected_pair_identity (r h b y : ℝ) :
    (((r+h)-b)^2+y^2)*(((r+h)+b)^2+y^2) -
      (((r-h)-b)^2+y^2)*(((r-h)+b)^2+y^2) =
          8*r*h*(y^2+r^2+h^2-b^2) := by ring

/-- The pair comparison used to exclude a zero in a deformed oldform. -/
theorem reflected_pair_positive {r h b y : ℝ} (hr : 0 < r) (hh : 0 < h)
    (hb : b^2 ≤ h^2) :
    (((r-h)-b)^2+y^2)*(((r-h)+b)^2+y^2) <
      (((r+h)-b)^2+y^2)*(((r+h)+b)^2+y^2) := by
  apply sub_pos.mp
  rw [reflected_pair_identity]
  have core : 0 < y^2+r^2+h^2-b^2 := by
    nlinarith only [sq_nonneg y, sq_pos_of_pos hr, hb]
  exact mul_pos (mul_pos (mul_pos (by norm_num) hr) hh) core

/-- Four times the positive heat parameter times the difference between
    the exponent at the high saddle and the low upper exponent at `v`. -/
def scaledGap (r a p q D v : ℝ) : ℝ :=
  (r+a*(p+q))^2 + v^2 - 2*(r+a*q)*v - 2*a*p*D

/-- Expansion around the unconstrained maximizer of the low parabola. -/
theorem gap_at_vertex (r a p q D v : ℝ) :
    scaledGap r a p q D v = (v-(r+a*q))^2 + a*p*(2*r+a*(p+2*q)-2*D) := by
  unfold scaledGap; ring

/-- Expansion around the endpoint D of the low interval. -/
theorem gap_at_endpoint (r a p q D v : ℝ) :
    scaledGap r a p q D v = (r+a*(p+q)-D)^2 +
                              (D-v)*(2*(r+a*q)-D-v) := by
  unfold scaledGap; ring

/-- A finite, uniform lower gap in the degree dichotomy, including conductor
    exponents close by `e` to their asymptotic thresholds. -/
theorem conductor_gap {r a p q D v m e η : ℝ}
    (ha : 0 < a) (hp : 0 ≤ p) (hq : 0 ≤ q) (hm : 0 < m)
    (hη : 0 < η) (he : e ≤ m) (hscale : a*e ≤ η/2)
    (hdich : m-e ≤ q ∨ 2*m-e ≤ p)
    (hmargin : D+η ≤ r+a*m) (hv : v ≤ D) :
    min (η^2/4) (a*m*η) ≤ scaledGap r a p q D v := by
  have hpq : m-e ≤ p+q := by rcases hdich with h|h <;> linarith
  have hdis : η/2 ≤ r+a*(p+q)-D := by
    have h := mul_le_mul_of_nonneg_left hpq ha.le
    nlinarith only [h, hmargin, hscale]
  by_cases hcenter : D ≤ r+a*q
  · apply le_trans (min_le_left _ _)
    rw [gap_at_endpoint]
    have first := mul_self_le_mul_self (show 0 ≤ η/2 by linarith) hdis
    have rest := mul_nonneg (sub_nonneg.mpr hv)
                             (show 0 ≤ 2*(r+a*q)-D-v by linarith)
    nlinarith only [first, rest]
  · apply le_trans (min_le_right _ _)
    have hbig : 2*m-e ≤ p := by
      rcases hdich with hsmall|hlarge
      · have h := mul_le_mul_of_nonneg_left hsmall ha.le
        exfalso
        apply hcenter
        nlinarith only [h, hscale, hmargin, hη]
      · exact hlarge
    have hpbig : m ≤ p := by linarith
    have hlin : η ≤ 2*r+a*(p+2*q)-2*D := by
      have h := mul_le_mul_of_nonneg_left hbig ha.le
      nlinarith only [h, mul_nonneg ha.le hq, hmargin, hscale, hη]
    rw [gap_at_vertex]
    have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hpbig ha.le) hlin hη.le
                              (mul_nonneg ha.le hp)
    linarith [sq_nonneg (v-(r+a*q))]

#print axioms reflected_pair_positive
#print axioms conductor_gap
end HeatBoundaryAlgebra
