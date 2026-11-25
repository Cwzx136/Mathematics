import Research.Prior.LiEulerGammaBounds
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! From a prime-power coefficient bound to the Euler estimates in the Li proof. -/
namespace LiEulerCoefficients
open Real LiEulerGammaBounds
open scoped ArithmeticFunction.vonMangoldt

private theorem shift_L (f : ℕ→ℝ) (s : ℝ)
    (hs : LSeriesSummable (fun n=>(f n:ℂ)) (s:ℂ)) :
    LSeries (fun n=>(f n:ℂ)) (s:ℂ) =
      ((∑' n:ℕ,f (n+1)/((n:ℝ)+1)^s : ℝ):ℂ) := by
  rw [LSeries,Complex.ofReal_tsum]
  have a := hs.tsum_eq_zero_add
  rw [a,LSeries.term_zero,zero_add]
  apply tsum_congr
  intro n
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),Complex.ofReal_div,
    Complex.ofReal_cpow (show 0 ≤ (n:ℝ)+1 by positivity)]
  simp

/-- Exact equality of the real Dirichlet quotient with the von Mangoldt sum
on the half-plane of absolute convergence. -/
theorem mangoldt {s : ℝ} (hs : 1<s) :
    (∑' n:ℕ,ArithmeticFunction.vonMangoldt (n+1)/((n:ℝ)+1)^s) = eulerRatio s := by
  have sr : 1<(s:ℂ).re := hs
  have absconv : LSeries.abscissaOfAbsConv (1:ℕ→ℂ)<(s:ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs
  have van := ArithmeticFunction.LSeries_vonMangoldt_eq sr
  rw [(LSeries_hasDerivAt absconv).deriv,neg_neg] at van
  have sm := ArithmeticFunction.LSeriesSummable_vonMangoldt sr
  have f1 : (fun _n:ℕ=>((1:ℝ):ℂ))=(1:ℕ→ℂ) := by funext n; simp
  have fl : (fun n:ℕ=>(log (n:ℝ):ℂ))=LSeries.logMul (1:ℕ→ℂ) := by
    funext n; simp only [LSeries.logMul,Pi.one_apply,mul_one,Complex.natCast_log]
  have one := shift_L (fun _=>1) s (by rw [f1]; exact LSeriesSummable_one_iff.mpr sr)
  have ml := shift_L (fun n => log (n:ℝ)) s (by rw [fl]; exact LSeriesSummable_logMul_of_lt_re absconv)
  have mg := shift_L ArithmeticFunction.vonMangoldt s sm
  rw [f1] at one
  rw [fl] at ml
  simp only [Nat.cast_add,Nat.cast_one] at ml
  apply Complex.ofReal_injective
  unfold eulerRatio eulerWeight logWeight
  rw [Complex.ofReal_div,←mg,←ml,←one]
  exact van

/-- The von Mangoldt majorant itself is absolutely summable at every σ>1. -/
theorem mang_summable {s : ℝ} (hs : 1<s) :
    Summable (fun n:ℕ=>ArithmeticFunction.vonMangoldt (n+1)/((n:ℝ)+1)^s) := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s:=(s:ℂ)) hs
  have ht := (summable_nat_add_iff 1).mpr h
  have normed := (summable_norm_iff.mpr ht)
  apply normed.congr
  intro n
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),norm_div,Complex.norm_natCast_cpow_of_pos (Nat.succ_pos _) _]
  simp [abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n:=n+1))]

noncomputable def term (c : ℕ→ℂ) (a t : ℝ) (n : ℕ) : ℂ :=
  c (n+1)/((n+1:ℕ):ℂ)^((a:ℂ)+(t:ℂ)*Complex.I)

/-- Euler bound at complex height from the usual compressed rational
prime-power coefficient inequality, including primes ramified over the base. -/
theorem majorant {d : ℕ} (c : ℕ→ℂ) (bounds : ∀ n:ℕ,‖c n‖ ≤ d*n*ArithmeticFunction.vonMangoldt n)
    {a : ℝ} (t : ℝ) (ha : 3≤a) :
    Summable (term c a t) ∧ |(∑' n,term c a t n).re| ≤ d*eulerRatio (a-1) := by
  have s : 1<a-1 := by linarith
  let M := fun n:ℕ => ArithmeticFunction.vonMangoldt (n+1)/((n:ℝ)+1)^(a-1)
  have sm : Summable M := mang_summable s
  have all (n : ℕ) : ‖term c a t n‖ ≤ d*M n := by
    unfold term M
    rw [norm_div,Complex.norm_natCast_cpow_of_pos (Nat.succ_pos _) _]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,
      Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,Nat.cast_succ]
    have np : 0 < (n:ℝ)+1 := by positivity
    have hb := bounds (n+1)
    push_cast at hb
    have pos : 0 ≤ ((n:ℝ)+1)^a := by positivity
    have r := div_le_div_of_nonneg_right hb pos
    apply r.trans_eq
    rw [rpow_sub np,rpow_one]
    field_simp
  have sn : Summable (fun n=>‖term c a t n‖) :=
    (sm.mul_left (d:ℝ)).of_nonneg_of_le (fun n=>norm_nonneg _) all
  have sc := summable_norm_iff.mp sn
  refine ⟨sc,?_⟩
  have cmp := sn.tsum_le_tsum all (sm.mul_left (d:ℝ))
  rw [sm.tsum_mul_left] at cmp
  change (∑' n,‖term c a t n‖) ≤ d*(∑' n:ℕ,ArithmeticFunction.vonMangoldt (n+1)/((n:ℝ)+1)^(a-1)) at cmp
  rw [mangoldt s] at cmp
  exact (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm sn).trans cmp)

/-- Grouping Euler factors over a rational prime. The residue degrees contribute
to the coefficient only when they divide the prime-power exponent. Ramification
only reduces the total available degree; repeated parameters keep their multiplicity. -/
theorem local_power {p k d : ℕ} (hp : p.Prime) (hk : 0<k)
    {ι : Type*} [Fintype ι] (f l : ι→ℕ) (α : (v:ι)→Fin (l v)→ℂ)
    (cap : ∀ v j,‖α v j‖ ≤ (p:ℝ)^(f v)) (degree : ∑ v,f v*l v ≤ d) :
    ‖((log (p:ℝ):ℝ):ℂ)*
      (∑ v, if f v ∣ k then (f v:ℂ)*∑ j,(α v j)^(k/f v) else 0)‖
      ≤ d*(p^k:ℕ)*ArithmeticFunction.vonMangoldt (p^k) := by
  classical
  let M (v : ι) := (f v:ℝ)*(l v)*(p:ℝ)^k
  have nn (v : ι) : 0≤M v := by dsimp [M]; positivity
  have atv (v : ι) :
      ‖if f v ∣ k then (f v:ℂ)*∑ j,(α v j)^(k/f v) else 0‖ ≤ M v := by
    by_cases fv : f v ∣ k
    · rw [ite_eq_left fv,norm_mul,Complex.norm_natCast]
      have each (j : Fin (l v)) : ‖(α v j)^(k/f v)‖ ≤ (p:ℝ)^k := by
        rw [norm_pow]
        have a := pow_le_pow_left₀ (norm_nonneg _) (cap v j) (k/f v)
        rwa [←pow_mul,Nat.mul_div_cancel' fv] at a
      have sum := (norm_sum_le (s:=Finset.univ) (f:=fun j:Fin (l v)=>(α v j)^(k/f v))).trans
        (Finset.sum_le_sum (fun j _ => each j))
      simp at sum
      dsimp [M]
      nlinarith [mul_le_mul_of_nonneg_left sum (Nat.cast_nonneg (α:=ℝ) (f v))]
    · rw [ite_eq_right fv,norm_zero]; exact nn v
  have all := (norm_sum_le (s:=Finset.univ) (f := fun v=>
    if f v ∣ k then (f v:ℂ)*∑ j,(α v j)^(k/f v) else 0)).trans (Finset.sum_le_sum (fun v _ => atv v))
  have diam : (∑ v,(f v:ℝ)*(l v)) ≤ d := by exact_mod_cast degree
  have ms : ∑ v,M v ≤ d*(p:ℝ)^k := by
    dsimp [M]; rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right diam (by positivity)
  have pos : 0≤log (p:ℝ) := log_nonneg (by exact_mod_cast hp.one_le)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg pos,ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp,Nat.cast_pow]
  nlinarith [mul_le_mul_of_nonneg_left (all.trans ms) pos]

/-- The global rational coefficient inequality follows prime by prime from
residue degrees, multiplicities, and the root bound at each finite place. -/
theorem rational_bound {d : ℕ} (c : ℕ→ℂ) (places : ℕ→ℕ)
    (f l : (p:ℕ)→Fin (places p)→ℕ)
    (α : (p:ℕ)→(v:Fin (places p))→Fin (l p v)→ℂ)
    (rootBound : ∀ p:ℕ,p.Prime → ∀ v j,‖α p v j‖ ≤ (p:ℝ)^(f p v))
    (degree : ∀ p:ℕ,p.Prime → (∑ v,f p v*l p v) ≤ d)
    (support : ∀ n:ℕ,(¬∃p k:ℕ,p.Prime ∧ 0<k ∧ p^k=n) → c n=0)
    (logDerivative : ∀ p k:ℕ,p.Prime → 0<k → c (p^k)=
      ((log (p:ℝ):ℝ):ℂ)*(∑ v,if f p v ∣ k then
        (f p v:ℂ)*∑ j,(α p v j)^(k/f p v) else 0)) :
    ∀ n:ℕ,‖c n‖ ≤ d*n*ArithmeticFunction.vonMangoldt n := by
  intro n
  by_cases h : ∃p k:ℕ,p.Prime ∧ 0<k ∧ p^k=n
  · obtain ⟨p,k,hp,hk,rfl⟩ := h
    rw [logDerivative p k hp hk]
    exact local_power hp hk (f p) (l p) (α p) (rootBound p hp) (degree p hp)
  · rw [support n h,norm_zero]
    exact mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg

#print axioms mangoldt
#print axioms mang_summable
#print axioms majorant
#print axioms local_power
#print axioms rational_bound

end LiEulerCoefficients
