import Research.Stechkin

/-! Quantitative finite-height gain from the optimized Stechkin kernel.
The only analytic input to the last theorem is stated explicitly. -/
namespace ERH.Stechkin
noncomputable section

/-- Uniform quantitative gain in the range 1 < σ ≤ 1.02. -/
theorem weight_bounds_small {u : ℝ} (hu : 0 < u) (hsmall : u ≤ 1/50) :
    1/Real.sqrt 5 + u/3 ≤ (1/2+u)/optimalOuter (1/2+u) ∧
    (1/2+u)/optimalOuter (1/2+u) ≤ 23/50 := by
  let m : ℝ := 1/2+u
  let N := optimalOuter m
  let k := m/N
  let k₀ : ℝ := 1/Real.sqrt 5
  have hm : 1/2 < m := by dsimp [m]; linarith
  have hm' : m ≤ 13/25 := by dsimp [m]; linarith
  have hN : 0 < N := by linarith [show m < N from optimalOuter_gt hm]
  have hNs : N^2=2*m^2+m+1/4 := optimalOuter_sq hm
  have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have h5s := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hk₀sq : 5*k₀^2=1 := by dsimp [k₀]; rw [div_pow,h5s]; norm_num
  have hk₀p : 0 < k₀ := by dsimp [k₀]; positivity
  have hk₀hi : k₀ ≤ 9/20 := by
    apply le_of_sq_le_sq _ (by norm_num)
    nlinarith only [hk₀sq]
  have hm2 : m^2 ≤ (13/25:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hm') (show 0 ≤ 13/25+m by linarith)]
  have hNhi : N^2 ≤ 21/16 := by nlinarith
  have hkhi : k ≤ 23/50 := by
    apply (div_le_iff₀ hN).2
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, hNs]
    nlinarith
  have hp : 0 < 5*N^2 := by positivity
  have hfac : (5*N^2)*(k+k₀) < 6 := calc
    _ ≤ (5*N^2)*(23/50+9/20) := mul_le_mul_of_nonneg_left (add_le_add hkhi hk₀hi) (le_of_lt hp)
    _ < _ := by nlinarith
  have hi : (5*N^2)*(k+k₀)*(k-k₀) = 2*u+3*u^2 := calc
    _ = 5*(k*N)^2-(5*k₀^2)*N^2 := by ring
    _ = 2*u+3*u^2 := by
      change 5*((m/N)*N)^2-(5*k₀^2)*N^2=_
      rw [div_mul_cancel₀ _ (ne_of_gt hN),hk₀sq,hNs]
      dsimp [m]
      ring
  refine ⟨?_,hkhi⟩
  change k₀+u/3 ≤ k
  by_contra! hc
  have hkp : 0 < k := by dsimp [k]; exact div_pos (by linarith) hN
  have ht : 0 < (5*N^2)*(k+k₀) := by positivity
  have hbad := mul_lt_mul_of_pos_left (show k-k₀ < u/3 by linarith) ht
  have hshort := mul_lt_mul_of_pos_right hfac (show 0 < u/3 by linarith)
  nlinarith [sq_nonneg u]

private theorem linear_gain {u d q y : ℝ} (hu : 0 < u) (hq : 0 < q)
    (huδ : 0 < u+d) (hmain : u ≤ (q-y)*(u+d)) :
    u/q-u+u*y/q^2 ≤ d := by
  have hqy : 0 < q-y := by
    by_contra! h
    linarith [mul_nonpos_of_nonpos_of_nonneg h (le_of_lt huδ)]
  have hpoly : (u/q+u*y/q^2)*(q-y) ≤ u := by
    field_simp
    nlinarith [mul_nonneg (le_of_lt hu) (sq_nonneg y)]
  have hmain' : u ≤ (u+d)*(q-y) := by simpa only [mul_comm (u+d)] using hmain
  have h := (mul_le_mul_iff_left₀ hqy).mp (hpoly.trans hmain')
  linarith

/-- If the explicit-formula majorant has height cost (1−k)gL minus a nonnegative
constant c, its usual optimizing u=b/L gives a strictly controlled second-order term.
We allow any real c: the algebraic implication remains correct. -/
theorem gain_of_explicit_formula {u d p q g L c k k₀ b : ℝ}
    (hu : 0 < u) (hpos : 0 < u+d) (hq : 0 < q) (hg : 0 < g)
    (hL : 0 < L) (hb : u*L=b)
    (hopt : p+(1-k₀)*g*b=q)
    (hk : k₀+u/3 ≤ k)
    (hexp : 1/(u+d) ≤ p/u+(1-k)*g*L-c) :
    (b/q-b)/L + (b^2*(c+g*b/3)/q^2)/L^2 ≤ d := by
  have h1 : u ≤ ((p+(1-k)*g*(u*L))-u*c)*(u+d) := by
    have hh := (div_le_iff₀ hpos).1 hexp
    have hh' := mul_le_mul_of_nonneg_left hh (le_of_lt hu)
    have hid : u*((p/u+(1-k)*g*L-c)*(u+d)) =
        ((p+(1-k)*g*(u*L))-u*c)*(u+d) := by field_simp
    rw [hid] at hh'
    linarith
  rw [hb] at h1
  have hbp : 0 < b := by rw [← hb]; positivity
  have h2 : (p+(1-k)*g*b)-u*c ≤ q-u*(c+g*b/3) := by
    nlinarith [mul_le_mul_of_nonneg_right hk (show 0 ≤ g*b by positivity)]
  have h3 := h1.trans (mul_le_mul_of_nonneg_right h2 (le_of_lt hpos))
  have h4 := linear_gain hu hq hpos h3
  calc
    _ = u/q-u+u*(u*(c+g*b/3))/q^2 := by
      rw [← hb]
      field_simp
    _ ≤ _ := h4

/-- Rational data of the five-frequency conductor-eleven polynomial. -/
def pole : ℝ := 413/900
def gammaSlope : ℝ := 9161/3600
def testScale : ℝ := 15535/100000
private def baseWeight : ℝ := 44721359/100000000

private theorem baseWeight_le : baseWeight ≤ 1 / Real.sqrt 5 := by
  have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have h5s := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  apply (le_div_iff₀ h5).2
  apply le_of_sq_le_sq _ (by norm_num)
  rw [mul_pow, h5s]
  norm_num [baseWeight]

/-- The unreduced explicit-formula majorant. M denotes the fixed archimedean and
reference-conductor charge after subtracting g log(2π), with the archived +pole included in M.
The identity pole_cancellation removes this regular pole contribution. Establishing this analytic
inequality at an actual zero is an input, not a declaration about an L-function. -/
def OriginalMajorant (L d M : ℝ) : Prop :=
  let u := testScale/L
  let k := (1/2+u) / optimalOuter (1/2+u)
  1/(u+d) ≤ pole/u + (1-k)*gammaSlope*L + (1-k)*(M-pole) + 4/1000

/-- Concrete second-order gain for the conductor-eleven input. L=log|T| in applications. -/
theorem conductorEleven_width {L d M : ℝ} (hL : 8 ≤ L) (hd : 0 ≤ d)
    (hM : M ≤ -(357/500 : ℝ)) (hInput : OriginalMajorant L d M) :
    1/((13518/1000)*L) + 1/(25*L^2) < d := by
  let u := testScale/L
  let k := (1/2+u)/optimalOuter (1/2+u)
  let q := pole+(1-baseWeight)*gammaSlope*testScale
  have hb : 0 < testScale := by norm_num [testScale]
  have hg : 0 < gammaSlope := by norm_num [gammaSlope]
  have hp : 0 < L := by linarith
  have hu : 0 < u := div_pos hb hp
  have hs : u ≤ 1/50 := by
    apply (div_le_iff₀ hp).2
    dsimp [testScale]
    linarith
  have hq : 0 < q := by norm_num [q,pole,baseWeight,gammaSlope,testScale]
  obtain ⟨hweight,hkhi⟩ := weight_bounds_small hu hs
  change 1/Real.sqrt 5+u/3 ≤ k at hweight
  change k ≤ 23/50 at hkhi
  have hE : 1/(u+d) ≤ pole/u + (1-k)*gammaSlope*L-629/1000 := by
    change 1/(u+d) ≤ pole/u+(1-k)*gammaSlope*L+(1-k)*(M-pole)+4/1000 at hInput
    have hres := mul_le_mul_of_nonneg_left (sub_le_sub_right hM pole) (show 0 ≤ 1-k by linarith)
    unfold pole at hres hInput ⊢
    linarith
  have hh := gain_of_explicit_formula hu (by linarith : 0 < u+d) hq hg hp
    (show u*L=testScale from div_mul_cancel₀ _ (ne_of_gt hp))
    (show pole+(1-baseWeight)*gammaSlope*testScale=q from rfl)
    (show baseWeight+u/3 ≤ k by linarith [baseWeight_le]) hE
  have hc1 : (1:ℝ)/(13518/1000) < testScale/q-testScale := by
    norm_num [q,pole,baseWeight,gammaSlope,testScale]
  have hc2 : (1:ℝ)/25 < testScale^2*(629/1000+gammaSlope*testScale/3)/q^2 := by
    norm_num [q,pole,baseWeight,gammaSlope,testScale]
  apply lt_of_lt_of_le _ hh
  have h1 := div_lt_div_of_pos_right hc1 hp
  have h2 := div_lt_div_of_pos_right hc2 (show 0 < L^2 by positivity)
  calc
    _ = ((1:ℝ)/(13518/1000))/L+(1/25)/L^2 := by ring
    _ < _ := add_lt_add h1 h2

/-- Equivalent convenient single denominator throughout the audited high-height range. -/
theorem conductorEleven_shifted_denom {L d M : ℝ} (hL : 62/5 ≤ L) (hd : 0 ≤ d)
    (hM : M ≤ -(357/500 : ℝ)) (hInput : OriginalMajorant L d M) :
    1/((13518/1000)*L-7) < d := by
  have hb := conductorEleven_width (by linarith : 8 ≤ L) hd hM hInput
  apply lt_of_le_of_lt _ hb
  have hp : 0 < L := by linarith
  have hden : 0 < (13518/1000:ℝ)*L-7 := by linarith
  have hpos : 0 ≤ L*((((13518/1000:ℝ)^2)-175)*L-7*(13518/1000)) := by
    apply mul_nonneg (le_of_lt hp)
    linarith
  field_simp
  apply (div_le_iff₀ (show 0 < 13518*L-1000*7 by linarith)).2
  nlinarith only [hpos, hp, hL]

end
end ERH.Stechkin
