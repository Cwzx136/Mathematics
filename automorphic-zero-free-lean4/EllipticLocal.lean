import EllipticWeights
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

namespace EllipticBernstein
theorem chebT_eq_standard (x : ℝ) (n : Nat) :
    chebT n x = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebT]
  | one => simp [chebT]
  | more n h₀ h₁ =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
    rw [chebT, Polynomial.Chebyshev.T_add_two, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, ← h₀, ← h₁]

theorem chebU_eq_standard (x : ℝ) (n : Nat) :
    chebU n x = (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebU]
  | one => simp [chebU]
  | more n h₀ h₁ =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
    rw [chebU, Polynomial.Chebyshev.U_add_two, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, ← h₀, ← h₁]

noncomputable def evalFourier (x θ : ℝ) : List Entry → ℝ
  | [] => 0
  | (l,j,c)::rest => c * (Polynomial.Chebyshev.U ℝ (j:ℤ)).eval x *
      Real.cos (l*θ) + evalFourier x θ rest

theorem fourier_eq (x θ : ℝ) (entries : List Entry) :
    evalFourier x θ entries = evalTable x (Real.cos θ) entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨l,j,c⟩ := entry
    simp [evalFourier, evalTable, chebU_eq_standard, chebT_eq_standard,
      Polynomial.Chebyshev.T_real_cos, ih]


/-- The exact unramified polynomial for arbitrary real half trace. -/
theorem fourier_nonneg (x θ : ℝ) : 0 ≤ evalFourier x θ reducedTable := by
  rw [fourier_eq]
  exact table_nonnegative x _ (Real.neg_one_le_cos θ) (Real.cos_le_one θ)

/-- The finitely averaged form applies directly to scaled inertia sums. -/
theorem inertia_average_nonneg {ι : Type} (s : Finset ι) (weight trace : ι → ℝ)
    (θ : ℝ) (hw : ∀ a ∈ s, 0 ≤ weight a) :
    0 ≤ ∑ a ∈ s, weight a * evalFourier (trace a) θ reducedTable := by
  exact Finset.sum_nonneg fun a ha => mul_nonneg (hw a ha) (fourier_nonneg _ _)

/-- Special (Steinberg) Euler coefficients with the signed local scalar b. -/
def specialEval (b y : ℝ) : List Entry → ℝ
  | [] => 0
  | (l,j,c)::rest => c * b^j * chebT l y + specialEval b y rest

/-- A quadratic ramified twist retains precisely the even indices. -/
def specialEven (b y : ℝ) : List Entry → ℝ
  | [] => 0
  | (l,j,c)::rest =>
      (if j%2=0 then c*b^j*chebT l y else 0) + specialEven b y rest

def specialNet : Net :=
  ⟨⟨3190845, 5967184, 2736013, (-1329800), (-460761), (-51976), 243663⟩, ⟨11471560, 14927664, (-1850024), (-12396256), (-3160968), 122800, 2038632⟩, ⟨17405221, 14045176, (-11859843), (-21764024), (-4891409), 2492928, 7380911⟩, ⟨14609968, 7041632, (-10259504), (-22462656), (-10259504), 7041632, 14609968⟩, ⟨7380911, 2492928, (-4891409), (-21764024), (-11859843), 14045176, 17405221⟩, ⟨2038632, 122800, (-3160968), (-12396256), (-1850024), 14927664, 11471560⟩, ⟨243663, (-51976), (-460761), (-1329800), 2736013, 5967184, 3190845⟩⟩

theorem special_identity (b y : ℝ) :
    netValue specialNet (b+1) (1-b) (y+1) (1-y) =
      4096 * (specialEval b y reducedTable - 50000) := by
  norm_num [specialNet, netValue, rowValue, map7, value, specialEval, reducedTable,
    originalTable, chebT]; ring

theorem special_involution (b y : ℝ) :
    specialEven b y reducedTable =
     (specialEval b y reducedTable + specialEval (-b) y reducedTable)/2 := by
  norm_num [specialEven, specialEval, reducedTable, originalTable, chebT]; ring

/-- The adjusted million-normalized polynomial contributes at least 1/20 at
every real Steinberg parameter of absolute value at most one. -/
theorem special_margin (b y : ℝ) (hb0 : -1 ≤ b) (hb1 : b ≤ 1)
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1) : 50000 ≤ specialEval b y reducedTable := by
  have hpos : positiveOn specialNet := cert_sound 4 true _ (by decide +kernel)
  have h := hpos (b+1) (1-b) (y+1) (1-y)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [special_identity] at h
  linarith

theorem special_even_margin (b y : ℝ) (hb0 : -1 ≤ b) (hb1 : b ≤ 1)
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1) : 50000 ≤ specialEven b y reducedTable := by
  rw [special_involution]
  have h₁ := special_margin b y hb0 hb1 hy0 hy1
  have h₂ := special_margin (-b) y (by linarith) (by linarith) hy0 hy1
  linarith

#print axioms fourier_nonneg
#print axioms special_margin
#print axioms special_even_margin
end EllipticBernstein
