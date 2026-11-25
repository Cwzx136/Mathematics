import Research.Resonance
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Rounding and finite-height transfer for the two analytic envelopes at conductor 11.
The coefficients of the envelopes are inputs from the digamma and Perron estimates.
The numerical conclusions below use rational arithmetic and proved exponential bounds. -/
namespace EffectiveEleven

noncomputable section
def delta (p : ℝ) := (1-Real.sqrt p)^2
def quarticPole : ℝ := 413/900
def sixthPole : ℝ := 115561/250000
def quarticSlope : ℝ := (322/643)*(9161/3600)
def sixthSlope : ℝ := (514/1027)*(2284863/1000000)
def scalarWeight : ℝ := 468083/1000000
def quarticBudget (t : ℝ) := quarticSlope*t-0.77425
def sixthBudget (t : ℝ) :=
  sixthSlope*t-0.638+scalarWeight*(2*Real.log (t+Real.log 6)+10/3)

private theorem delta_lower {p b d : ℝ} (hb : 0≤b) (hb' : b<1)
    (hp : p≤b^2) (hd : d ≤ (1-b)^2) : d ≤ delta p := by
  have H := (Real.sqrt_le_iff).2 ⟨hb,hp⟩
  refine hd.trans ?_
  unfold delta
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

theorem quartic_delta : 0.10406212 ≤ delta quarticPole := by
  apply delta_lower (b:=0.67741339) <;> norm_num [quarticPole]

theorem sixth_delta : 0.10247342 ≤ delta sixthPole := by
  apply delta_lower (b:=0.67988529) <;> norm_num [sixthPole]

/-- A short series at one eighth the argument, followed by three squarings. -/
private theorem log_cap {z u : ℝ} (hz : 0<z) (hu : 0≤u)
    (h : z ≤ (∑ i ∈ Finset.range 10, (u/8)^i/(i.factorial:ℝ))^8) :
    Real.log z ≤ u := by
  apply (Real.log_le_iff_le_exp hz).2
  refine h.trans ?_
  calc
    _ ≤ (Real.exp (u/8))^8 := by
      apply pow_le_pow_left₀
      · positivity
      · exact Real.sum_le_exp_of_nonneg (show 0≤u/8 by positivity) 10
    _ = _ := by rw [← Real.exp_nat_mul (u/8) 8]; congr 1; push_cast; ring

private theorem log_six : Real.log 6 ≤ 1.792 := by
  apply log_cap (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

private theorem log_at {s u : ℝ} (hs : 0<s)
    (hcap : Real.log (s+1.792) ≤ u) : Real.log (s+Real.log 6) ≤ u := by
  have hb : 0≤Real.log 6 := Real.log_nonneg (by norm_num)
  exact (Real.log_le_log (by linarith) (by linarith [log_six])).trans hcap

/-- The tangent majorant used at each of the four cutoffs. -/
theorem log_tangent {s u t : ℝ} (hs : 0<s) (ht : s≤t)
    (hu : Real.log (s+Real.log 6) ≤ u) :
    Real.log (t+Real.log 6) ≤ u+(t-s)/s := by
  let b := Real.log 6
  have hb : 0≤b := Real.log_nonneg (by norm_num)
  have ht' : 0<t+b := by linarith
  have hs' : 0<s+b := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos ht' hs')
  rw [Real.log_div ht'.ne' hs'.ne'] at h
  have href : (t+b)/(s+b)-1 ≤ (t-s)/s := by
    rw [div_sub_one hs'.ne']
    apply (div_le_div_iff₀ hs' hs).2
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hb]
  change Real.log (s+b) ≤ u at hu
  change Real.log (t+b) ≤ _
  linarith

private theorem sixth_below {s u C t : ℝ} (hs : 0<s) (ht : s≤t) (hC : 0<C)
    (hu : Real.log (s+Real.log 6) ≤ u)
    (hslope : sixthSlope+2*scalarWeight/s ≤ C*0.10247342)
    (hbase : sixthSlope*s-0.638+scalarWeight*(2*u+10/3) < C*0.10247342*s) :
    sixthBudget t < C*delta sixthPole*t := by
  have htan := log_tangent hs ht hu
  have hW : 0≤scalarWeight := by norm_num [scalarWeight]
  have hlog := mul_le_mul_of_nonneg_left (show 2*Real.log (t+Real.log 6)+10/3 ≤
      2*(u+(t-s)/s)+10/3 by linarith) hW
  have sl := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr ht)
  have hfix : scalarWeight*(2*((t-s)/s)) = (2*scalarWeight/s)*(t-s) := by ring
  have hpos : 0 ≤ t := hs.le.trans ht
  have hd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sixth_delta hC.le) hpos
  unfold sixthBudget
  nlinarith

theorem quartic_all {t : ℝ} (ht : 0<t) :
    quarticBudget t < 12.246*delta quarticPole*t := by
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left quartic_delta
    (by norm_num : (0:ℝ)≤12.246)) ht.le
  unfold quarticBudget quarticSlope
  linarith

theorem quartic_to_split {t : ℝ} (ht : 0<t) (hs : t≤48) :
    quarticBudget t < 12.091*delta quarticPole*t := by
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left quartic_delta
    (by norm_num : (0:ℝ)≤12.091)) ht.le
  unfold quarticBudget quarticSlope
  linarith

theorem sixth_from_split {t : ℝ} (ht : 48≤t) :
    sixthBudget t < 12.091*delta sixthPole*t := by
  apply sixth_below (s:=48) (u:=3.908) (by norm_num) ht (by norm_num)
  · apply log_at (by norm_num)
    apply log_cap (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  all_goals norm_num [sixthSlope,scalarWeight]

theorem sixth_from_200 {t : ℝ} (ht : 200≤t) :
    sixthBudget t < 11.447*delta sixthPole*t := by
  apply sixth_below (s:=200) (u:=5.308) (by norm_num) ht (by norm_num)
  · apply log_at (by norm_num)
    apply log_cap (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  all_goals norm_num [sixthSlope,scalarWeight]

theorem sixth_from_1000 {t : ℝ} (ht : 1000≤t) :
    sixthBudget t < 11.232*delta sixthPole*t := by
  apply sixth_below (s:=1000) (u:=6.910) (by norm_num) ht (by norm_num)
  · apply log_at (by norm_num)
    apply log_cap (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  all_goals norm_num [sixthSlope,scalarWeight]

theorem sixth_from_10000 {t : ℝ} (ht : 10000≤t) :
    sixthBudget t < 11.169*delta sixthPole*t := by
  apply sixth_below (s:=10000) (u:=9.211) (by norm_num) ht (by norm_num)
  · apply log_at (by norm_num)
    apply log_cap (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  all_goals norm_num [sixthSlope,scalarWeight]

/-- The target-budget hypothesis produced by the analytic comparison. -/
def TargetBudget (p B β : ℝ) : Prop :=
  1/2<β → ∀ u : ℝ, 0<u → u≤0.02 → 1/(1+u-β) ≤ p/u+B

/-- Finite optimizer and transfer from an analytic inequality valid on a bounded interval. -/
theorem finite_transfer {p B β C t : ℝ} (hp : 0<p) (hp' : p<1)
    (hβ : β≤1) (ht : 12≤t) (hC : 1≤C) (hB : 12.5≤B)
    (hr : B < C*delta p*t) (budget : TargetBudget p B β) :
    1/(C*t) < 1-β := by
  have hCt : 0<C*t := mul_pos (by linarith) (by linarith)
  by_cases hhalf : 1/2<β
  · let q := Real.sqrt p
    have hq : 0<q := Real.sqrt_pos.2 hp
    have hq' : q<1 := by
      have := Real.sq_sqrt hp.le
      change Real.sqrt p<1
      nlinarith [sq_nonneg (Real.sqrt p - 1)]
    have hqs : q^2=p := Real.sq_sqrt hp.le
    have hB' : 0<B := by linarith
    let v := q*(1-q)/B
    have hv : 0<v := div_pos (mul_pos hq (sub_pos.mpr hq')) hB'
    have hv' : v≤0.02 := by
      apply (div_le_iff₀ hB').2
      nlinarith [sq_nonneg (q-1/2)]
    have h := budget hhalf v hv hv'
    have hd : 0<1+v-β := by linarith
    have hsum : 0<p/v+B := by positivity
    have hopt : (v+delta p/B)*(p/v+B) = 1 := by
      have raw := EdgeDisks.general_barrier hq hq' hB'
      change (v+delta p/B)*(q^2/v+B)=1^2 at raw
      rw [hqs,one_pow] at raw
      exact raw
    have hwidth : delta p / B ≤ 1-β := by
      have hm := (div_le_iff₀ hd).mp h
      have hmul : (v+delta p/B)*(p/v+B) ≤ (1+v-β)*(p/v+B) := by
        rw [hopt]; linarith [mul_comm (p/v+B) (1+v-β)]
      linarith [(mul_le_mul_iff_left₀ hsum).mp hmul]
    refine lt_of_lt_of_le ?_ hwidth
    apply (div_lt_div_iff₀ hCt hB').2
    nlinarith
  · apply (div_lt_iff₀ hCt).2
    have hl : (12:ℝ)≤C*t := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (show 0≤t by linarith)]
    nlinarith [mul_nonneg (show 0≤(1-β)-1/2 by linarith) hCt.le]

theorem log_height {T : ℝ} (hT : 262144≤|T|) : 12≤Real.log |T| := by
  have h := Real.log_le_log (by norm_num : (0:ℝ)<262144) hT
  rw [show (262144:ℝ)=2^(18:ℕ) by norm_num, Real.log_pow] at h
  norm_cast at h
  linarith [Real.log_two_gt_d9]

private theorem quartic_big {t : ℝ} (ht : 12≤t) : 12.5≤quarticBudget t := by
  unfold quarticBudget quarticSlope
  linarith

private theorem sixth_big {t : ℝ} (ht : 12≤t) : 12.5≤sixthBudget t := by
  have h6 : 0≤Real.log 6 := Real.log_nonneg (by norm_num)
  have hl : 0≤Real.log (t+Real.log 6) := Real.log_nonneg (by linarith)
  unfold sixthBudget sixthSlope scalarWeight
  linarith

/-- Explicit unconditional coefficient from the quartic budget. -/
theorem quartic_exclusion {T β : ℝ} (hT : 262144≤|T|) (hβ : β≤1)
    (hb : TargetBudget quarticPole (quarticBudget (Real.log |T|)) β) :
    1/(12.246*Real.log |T|) < 1-β :=
  finite_transfer (by norm_num [quarticPole]) (by norm_num [quarticPole]) hβ
    (log_height hT) (by norm_num) (quartic_big (log_height hT))
    (quartic_all (by linarith [log_height hT])) hb

/-- The same unconditional envelope gives a sharper finite first octave. -/
theorem quartic_first_octave {T β : ℝ} (hT : 262144≤|T|) (hT' : |T|≤524288) (hβ : β≤1)
    (hb : TargetBudget quarticPole (quarticBudget (Real.log |T|)) β) :
    1/(11.682*Real.log |T|) < 1-β := by
  let t := Real.log |T|
  have ht : 12≤t := log_height hT
  have hmax := Real.log_le_log (show 0 < |T| by linarith) hT'
  rw [show (524288:ℝ)=2^(19:ℕ) by norm_num, Real.log_pow] at hmax
  norm_cast at hmax
  have hmax' : t≤13.170 := by
    dsimp [t]
    linarith [Real.log_two_lt_d9]
  apply finite_transfer (by norm_num [quarticPole]) (by norm_num [quarticPole]) hβ
      ht (by norm_num) (quartic_big ht) _ hb
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left quartic_delta
    (by norm_num : (0:ℝ)≤11.682)) (show 0≤t by linarith)
  unfold quarticBudget quarticSlope
  linarith

/-- With the extra scalar estimate at high heights, switch polynomials at log-height 48. -/
theorem joint_exclusion {T β : ℝ} (hT : 262144≤|T|) (hβ : β≤1)
    (h4 : TargetBudget quarticPole (quarticBudget (Real.log |T|)) β)
    (h6 : TargetBudget sixthPole (sixthBudget (Real.log |T|)) β) :
    1/(12.091*Real.log |T|) < 1-β := by
  have ht := log_height hT
  rcases le_total (Real.log |T|) 48 with h|h
  · exact finite_transfer (by norm_num [quarticPole]) (by norm_num [quarticPole]) hβ
      ht (by norm_num) (quartic_big ht) (quartic_to_split (by linarith) h) h4
  · exact finite_transfer (by norm_num [sixthPole]) (by norm_num [sixthPole]) hβ
      ht (by norm_num) (sixth_big ht) (sixth_from_split h) h6

theorem sixth_exclusion_200 {t β : ℝ} (ht : 200≤t) (hβ : β≤1)
    (h6 : TargetBudget sixthPole (sixthBudget t) β) : 1/(11.447*t) < 1-β :=
  finite_transfer (by norm_num [sixthPole]) (by norm_num [sixthPole]) hβ
    (by linarith) (by norm_num) (sixth_big (by linarith)) (sixth_from_200 ht) h6

theorem sixth_exclusion_1000 {t β : ℝ} (ht : 1000≤t) (hβ : β≤1)
    (h6 : TargetBudget sixthPole (sixthBudget t) β) : 1/(11.232*t) < 1-β :=
  finite_transfer (by norm_num [sixthPole]) (by norm_num [sixthPole]) hβ
    (by linarith) (by norm_num) (sixth_big (by linarith)) (sixth_from_1000 ht) h6

theorem sixth_exclusion_10000 {t β : ℝ} (ht : 10000≤t) (hβ : β≤1)
    (h6 : TargetBudget sixthPole (sixthBudget t) β) : 1/(11.169*t) < 1-β :=
  finite_transfer (by norm_num [sixthPole]) (by norm_num [sixthPole]) hβ
    (by linarith) (by norm_num) (sixth_big (by linarith)) (sixth_from_10000 ht) h6

#print axioms quartic_exclusion
#print axioms joint_exclusion
#print axioms sixth_exclusion_10000
end
end EffectiveEleven
