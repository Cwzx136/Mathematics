import Research.CompactBump
import Mathlib.Tactic.FieldSimp

/-! Positivity identities and exact gain inequalities for general-rank trace tests.
The integral is the same genuine compact autocorrelation as in Research.CompactBump,
evaluated at the individual support and pole parameters of each theorem. -/

noncomputable section
namespace ERH.RankBump
open ERH.Bump

def gain (b p : ℝ) : ℝ := b*(∫ x in (0:ℝ)..1, h x*(Real.exp (-(b*x))-p))
def lower (b p : ℝ) : ℝ := b*(momentPolynomial b-(315/796)*p)

theorem lower_le (b p : ℝ) (hb : 0 ≤ b) : lower b p ≤ gain b p :=
  general_gain_lower b p hb

/-- The square remains nonnegative for unbounded real trace X. -/
theorem real_phase_square (A X y : ℝ) (hA : 0 < A) :
    0 ≤ A*X^2+X*y+y^2/(4*A) := by
  have H : A*X^2+X*y+y^2/(4*A) = (2*A*X+y)^2/(4*A) := by field_simp; ring
  rw [H]; positivity

theorem complex_trace_square (b x y : ℝ) (hb : 0 < b) :
    0 ≤ b/2+x+(x^2+y^2)/(4*b)+(x^2-y^2)/(4*b) := by
  have H : b/2+x+(x^2+y^2)/(4*b)+(x^2-y^2)/(4*b) = (b+x)^2/(2*b) := by
    field_simp; ring
  rw [H]; positivity

/-- α is the chosen real-trace quadratic coefficient.  In ranks 2 and 3, r
parametrizes the phase weight s=(1−r²)/(1+r²), making the scalar mean rational. -/
def phasePole (α r : ℝ) := α+(1+r^2)/(8*α*(1+r))
def phaseGrowth (n α s : ℝ) := (1+n*α*s)/4
def complexPole (b : ℝ) := b/2+1/(4*b)

theorem real_rank_two :
    phaseGrowth 2 (311/1000) (539/1261) <
     (5673/1000)*gain (89/100) (phasePole (311/1000) (19/30)+1/1000000) := by
  apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left (lower_le _ _ (by norm_num)) (by norm_num))
  norm_num [phaseGrowth,phasePole,lower,momentPolynomial]

theorem real_rank_three :
    phaseGrowth 3 (322/1000) (16/65) <
      (6178/1000)*gain (21/25) (phasePole (322/1000) (7/9)+1/1000000) := by
  apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left (lower_le _ _ (by norm_num)) (by norm_num))
  norm_num [phaseGrowth,phasePole,lower,momentPolynomial]

theorem real_all_ranks :
    (1/4 : ℝ) < (6348/1000)*gain (8/11) (phasePole (35/99) 1) := by
  apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left (lower_le _ _ (by norm_num)) (by norm_num))
  norm_num [phasePole,lower,momentPolynomial]

private theorem complex_aux (b B U V : ℝ) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (h₁ : 1/4 < U*lower B (complexPole b))
    (h₂ : 1/(16*b) < V*lower B (complexPole b)) {n : ℝ} (hn : 0 < n) :
    n/4+n^2/(16*b) < (U*n+V*n^2)*gain B (complexPole b) := by
  have hl := lower_le B (complexPole b) hB
  have a := mul_lt_mul_of_pos_right (lt_of_lt_of_le h₁ (mul_le_mul_of_nonneg_left hl hU)) hn
  have e := mul_lt_mul_of_pos_right (lt_of_lt_of_le h₂ (mul_le_mul_of_nonneg_left hl hV))
    (sq_pos_of_pos hn)
  calc n/4+n^2/(16*b) = (1/4)*n+(1/(16*b))*n^2 := by ring
       _ < (U*gain B (complexPole b))*n+(V*gain B (complexPole b))*n^2 := add_lt_add a e
       _ = _ := by ring

theorem general_first {n : ℝ} (hn : 0 < n) :
    n/4+n^2/(16*(3/4)) <
      ((6406/1000)*n+(2136/1000)*n^2)*gain (18/25) (complexPole (3/4)) := by
  apply complex_aux _ _ _ _ (by norm_num) (by norm_num) (by norm_num) _ _ hn <;>
    norm_num [complexPole,lower,momentPolynomial]

theorem general_second {n : ℝ} (hn : 0 < n) :
    n/4+n^2/(16*(4/5)) <
      ((6606/1000)*n+(2065/1000)*n^2)*gain (71/100) (complexPole (4/5)) := by
  apply complex_aux _ _ _ _ (by norm_num) (by norm_num) (by norm_num) _ _ hn <;>
    norm_num [complexPole,lower,momentPolynomial]

theorem general_third {n : ℝ} (hn : 0 < n) :
    n/4+n^2/(16*(17/20)) <
      ((6943/1000)*n+(2042/1000)*n^2)*gain (69/100) (complexPole (17/20)) := by
  apply complex_aux _ _ _ _ (by norm_num) (by norm_num) (by norm_num) _ _ hn <;>
    norm_num [complexPole,lower,momentPolynomial]

end ERH.RankBump
