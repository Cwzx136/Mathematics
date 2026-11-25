import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Quartic character square with the t-aspect Weyl saving.
The analytic inequality in `select` is the output of logarithmic Poisson--Jensen on
the three shifted degrees, together with the static pole. This module proves the
polynomial identity, positivity, exact costs and the final optimization implication. -/

noncomputable section
namespace ERH.WeylAmplifier

def U₁ (x : ℝ) : ℝ := 2*x
def U₂ (x : ℝ) : ℝ := 4*x^2-1
def U₃ (x : ℝ) : ℝ := 8*x^3-4*x
def U₄ (x : ℝ) : ℝ := 16*x^4-12*x^2+1
def T₂ (y : ℝ) : ℝ := 2*y^2-1
def T₃ (y : ℝ) : ℝ := 4*y^3-3*y
def T₄ (y : ℝ) : ℝ := 8*y^4-8*y^2+1

/-- The five symmetric coefficient polynomials are 30, 71 U₁, 86+42 U₂, 71 U₁, 30.
The cosine variable y is cos φ; for positivity it can be any real number. -/
def polynomial (x y : ℝ) : ℝ :=
  21042 + 19070 * U₂ x + 1764 * U₄ x
  + (44872 * U₁ x + 11928 * U₃ x) * y
  + (20402 + 15122 * U₂ x) * T₂ y
  + 8520 * U₁ x * T₃ y + 1800 * T₄ y

theorem character_identity (x y : ℝ) :
    polynomial x y = (60*T₂ y + 142*U₁ x*y + 86 + 42*U₂ x)^2 := by
  unfold polynomial U₁ U₂ U₃ U₄ T₂ T₃ T₄
  ring

theorem polynomial_nonneg (x y : ℝ) : 0 ≤ polynomial x y := by
  rw [character_identity]; positivity

/-- Coefficient of the unshifted trivial character after normalizing the target to one. -/
def pole : ℝ := 21042/44872

/-- Combined costs for the shifted GL₂, GL₃, and GL₄ terms. The shifted scalars
contribute o(log T), while the nontrivial unshifted terms cost O(1). -/
def gammaCost (g₂ g₃ g₄ : ℝ) : ℝ :=
  ((44872+8520)*g₂ + 15122*g₃ + 11928*g₄)/44872

def weyl : ℝ := gammaCost (1/3) (3/4) 1

def nelson : ℝ := gammaCost (1/3) ((3/4)*(1-2/558)) (1-2/2544)

theorem exact_costs :
    pole = 10521/22436 ∧ weyl = 246401/269232 ∧ nelson = 101085917/110587044 := by
  norm_num [pole, weyl, nelson, gammaCost]

/-- A rational substitute for the optimal abscissa choice (√P−P)/G.
The variable w here is (1−β) log |T|. -/
def abscissa : ℝ := 59/250

/-- This hypothesis uses a positive epsilon to permit the o(1) after dividing by log |T|. -/
def disk_bound (G w : ℝ) : Prop := 1/(abscissa+w) ≤ pole/abscissa + G + 1/10000000

private theorem select {G B w : ℝ} (hw : 0 ≤ w)
    (hp : 0 < pole/abscissa + G + 1/10000000)
    (hnum : (abscissa+B)*(pole/abscissa+G+1/10000000) < 1)
    (h : disk_bound G w) : B < w := by
  have hw' : 0 < abscissa+w := by unfold abscissa; linarith
  have hprod := (div_le_iff₀ hw').mp h
  by_contra! hbad
  have hle := mul_le_mul_of_nonneg_right
    (show abscissa+w ≤ abscissa+B by linarith) hp.le
  linarith [mul_comm (pole/abscissa+G+1/10000000) (abscissa+w)]

theorem weyl_selected {w : ℝ} (hw : 0 ≤ w) (h : disk_bound weyl w) :
    1/(92111/10000 : ℝ) < w := by
  apply select hw _ _ h <;> norm_num [weyl, gammaCost, pole, abscissa]

theorem nelson_selected {w : ℝ} (hw : 0 ≤ w) (h : disk_bound nelson w) :
    1/(919983/100000 : ℝ) < w := by
  apply select hw _ _ h <;> norm_num [nelson, gammaCost, pole, abscissa]

end ERH.WeylAmplifier
