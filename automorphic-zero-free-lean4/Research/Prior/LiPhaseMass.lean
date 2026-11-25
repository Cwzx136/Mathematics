import Research.Prior.LiReflectedPair
import Research.Prior.LiMomentTail
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Positive-phase mass from a pair of finite ordinate bands. -/
namespace LiPhaseMass
open Real Set MeasureTheory

/-- On either ordinate band the Li phase contributes at least five quarters. -/
theorem phase_band {m g β : ℝ} (hm : 1605 ≤ m) (hlo : m/4 ≤ g) (hhi : g ≤ m/2)
    (hb : 0 ≤ β) (hb' : β ≤ 1) :
    5/4 ≤ 1-cos (m*(arctan (β/g)+arctan ((1-β)/g))) := by
  let x := m*(arctan (β/g)+arctan ((1-β)/g))
  have mg : 0 < g := by linarith
  have M : 0 < m := by linarith
  have lg : 20 ≤ g := by linarith
  have h := LiReflectedPair.phase_bounds mg hb hb'
  have low : (1.99:ℝ) ≤ x := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h.1 M.le)
    rw [←mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ m-2*g by linarith) mg.le,
      mul_nonneg (sub_nonneg.mpr lg) (show 0 ≤ g+20 by linarith)]
  have high : x ≤ 4 := by
    apply (mul_le_mul_of_nonneg_left h.2 M.le).trans
    rw [mul_one_div, div_le_iff₀ mg]; linarith
  have s2 : √(2:ℝ) ≤ 7/4 := by nlinarith [sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have s8 : (1:ℝ)/4 ≤ sin (π/8) := by
    rw [sin_pi_div_eight]
    nlinarith [sq_sqrt (show 0 ≤ 2-√(2:ℝ) by linarith),sqrt_nonneg (2-√(2:ℝ))]
  have edge : cos (5*π/8) ≤ -(1:ℝ)/4 := by
    rw [show 5*π/8=π/2+π/8 by ring, cos_add, cos_pi_div_two, sin_pi_div_two]
    linarith
  have bound (t : ℝ) (ht : 5*π/8 ≤ t) (ht' : t ≤ π) : cos t ≤ -(1:ℝ)/4 :=
    (cos_le_cos_of_nonneg_of_le_pi (by positivity) ht' ht).trans edge
  have hcos : cos x ≤ -(1:ℝ)/4 := by
    by_cases hp : x ≤ π
    · exact bound x (by linarith [pi_lt_d2]) hp
    · rw [←cos_two_pi_sub x]
      exact bound _ (by linarith [pi_gt_d2]) (by linarith)
  change 5/4 ≤ 1-cos x
  linarith

/-- The exact integral of the contribution of one zero on a signed window. -/
theorem poisson_integral {c : ℝ} (hc : 0 < c) (g a b : ℝ) :
    (∫ t in a..b, c/(c^2+(t-g)^2)) = arctan ((b-g)/c)-arctan ((a-g)/c) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => arctan ((t-g)/c))
  · intro t _
    convert (hasDerivAt_arctan ((t-g)/c)).comp t (((hasDerivAt_id t).sub_const g).div_const c) using 1
    · rfl
    · field_simp
  · apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) (fun t => ne_of_gt (by positivity))

/-- The whole-line integral bounds the mass from one zero on any chosen window. -/
theorem poisson_at_most_pi {c : ℝ} (hc : 0 < c) (g a b : ℝ) :
    (∫ t in a..b, c/(c^2+(t-g)^2)) ≤ π := by
  rw [poisson_integral hc]
  linarith [arctan_lt_pi_div_two ((b-g)/c),neg_pi_div_two_lt_arctan ((a-g)/c)]

/-- The remote Poisson tails are absolutely summable. The two unit intervals at
a given distance have total multiplicity at most seven times the indicated weight. -/
theorem remote {ι : Type*} (v : ι → ℝ) (bin : ι → ℕ) {y H d : ℝ}
    (hy : 780 ≤ y) (hd : 0 ≤ d) (hH : 0 < H) (hHd : d*log 25000 ≤ H)
    (nonnegative : ∀ i, 0 ≤ v i)
    (count : ∀ (s : Finset ι) (j : ℕ), ((s.filter (fun i => bin i=j)).card : ℝ) ≤
      7*(H+d*(log (y+j+1)-log y+log 3)))
    (weight : ∀ i, v i ≤ (5/2)/(y+(bin i:ℝ)+1)^2) :
    Summable v ∧ (∑' i, v i) < 0.0273*H := by
  have yp : 0 < y := by linarith
  have hlog10 : (10:ℝ) ≤ log 25000 := by
    have h := log_le_log (show 0 < (2:ℝ)^29 by positivity) (show (2:ℝ)^29 ≤ 25000^2 by norm_num)
    rw [log_pow, log_pow] at h
    norm_num at h
    linarith [log_two_gt_d9]
  have hlog3 : log (3:ℝ) ≤ 9/8 := by
    have h := log_le_log (show 0 < (3:ℝ)^5 by positivity) (show (3:ℝ)^5 ≤ 2^8 by norm_num)
    rw [log_pow,log_pow] at h
    norm_num at h
    linarith [log_two_lt_d9]
  have Hge : 10*d ≤ H := by nlinarith [mul_le_mul_of_nonneg_left hlog10 hd]
  let H' := H+d*(log 3-log 2)
  have hHd' : d ≤ H' := by
    have hlog := log_le_log (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≤3)
    dsimp [H']; nlinarith [mul_nonneg hd (sub_nonneg.mpr hlog)]
  let A (j : ℕ) := H+d*(log (y+j+1)-log y+log 3)
  have major (s : Finset ι) : ∑ i ∈ s,v i ≤ 17.5/y*(H+d*(log 3+1)) := by
    classical
    let K := s.sup bin+1
    have maps : ∀ i ∈ s, bin i ∈ Finset.range K := fun i hi =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := bin) hi))
    have onebin (j : ℕ) : (∑ i ∈ s with bin i=j,v i) ≤ 17.5*(A j/(y+j+1)^2) := by
      calc
        _ ≤ ∑ i ∈ s with bin i=j,(5/2:ℝ)/(y+j+1)^2 := Finset.sum_le_sum (fun i hi => by simpa [(Finset.mem_filter.mp hi).2] using weight i)
        _ = ((s.filter (fun i => bin i=j)).card : ℝ)*((5/2)/(y+j+1)^2) := by simp
        _ ≤ 7*A j*((5/2)/(y+j+1)^2) := mul_le_mul_of_nonneg_right (count s j) (by positivity)
        _ = _ := by ring
    have hg := LiMomentIntegral.grid yp hd hHd' 0 K
    have ha (j : ℕ) : A j = H'+d*(log (y+j+1)-log y+log 2) := by dsimp [A,H']; ring
    calc
      _ = ∑ j ∈ Finset.range K, ∑ i ∈ s with bin i=j,v i := (Finset.sum_fiberwise_of_maps_to maps _).symm
      _ ≤ ∑ j ∈ Finset.range K, 17.5*(A j/(y+j+1)^2) := Finset.sum_le_sum (fun j _ => onebin j)
      _ = 17.5*∑ j ∈ Finset.range K, (H'+d*(log (y+j+1)-log y+log 2))/(y+j+1)^2 := by rw [Finset.mul_sum]; simp only [ha]
      _ ≤ 17.5*((H'+d*log 2+d)/y) := by simpa using mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 17.5)
      _ = _ := by dsimp [H']; ring
  constructor
  · exact summable_of_sum_le nonnegative major
  · apply (Real.tsum_le_of_sum_le nonnegative major).trans_lt
    rw [div_mul_eq_mul_div, div_lt_iff₀ yp]
    have l := mul_le_mul_of_nonneg_left hlog3 hd
    nlinarith [mul_le_mul_of_nonneg_right hy hH.le]

/-- Convert the mean bound for a Hadamard sum and the outside-band leakage into
a lower count, using the exact Poisson integral for each of the finitely many retained zeros. -/
theorem band_count {ι : Type*} (c γ : ι → ℝ) (s : Finset ι) (raw : ℝ → ℝ)
    {a b H d : ℝ} (hab : a ≤ b) (_hd : 0 ≤ d) (hH : 0 < H) (hHd : 10*d ≤ H)
    (width : ∀ i, 0 < c i) (hr : IntervalIntegrable raw volume a b)
    (mean : (b-a)*(H/2-4.1*d) ≤ ∫ t in a..b, raw t)
    (leak : ∀ t ∈ Icc a b, raw t ≤ (∑ i ∈ s,c i/((c i)^2+(t-γ i)^2))+0.0273*H) :
    (b-a)*H/16 ≤ (s.card:ℝ)*π := by
  let K : ι → ℝ → ℝ := fun i t => c i/((c i)^2+(t-γ i)^2)
  have cc (i : ι) : Continuous (K i) := by
    apply continuous_const.div (by fun_prop)
    intro x; exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos (width i)) (sq_nonneg _))
  have kc (i : ι) : IntervalIntegrable (K i) volume a b := (cc i).intervalIntegrable _ _
  have fc : Continuous (fun x => ∑ i ∈ s,K i x) := continuous_finsetSum s (fun i _ => cc i)
  have fc' := fc.intervalIntegrable (μ:=volume) a b
  have cmp := intervalIntegral.integral_mono_on hab hr (fc'.add (intervalIntegrable_const (c:=0.0273*H))) leak
  rw [intervalIntegral.integral_add fc' intervalIntegrable_const,
      intervalIntegral.integral_finsetSum (fun i _ => kc i), intervalIntegral.integral_const,
      smul_eq_mul] at cmp
  have uk : (∑ i ∈ s, ∫ t in a..b, K i t) ≤ (s.card:ℝ)*π := by
    calc
      _ ≤ ∑ _i ∈ s,π := Finset.sum_le_sum (fun i _ => poisson_at_most_pi (width i) (γ i) a b)
      _ = _ := by simp
  have scalar : H/16 ≤ H/2-4.1*d-0.0273*H := by linarith
  nlinarith [mul_le_mul_of_nonneg_left scalar (sub_nonneg.mpr hab)]

/-- Two disjoint sign bands, each contributing the certified mean, supply the
uniform lower bound `mH/128` for the whole phase sum. -/
theorem from_bands {ι : Type*} [DecidableEq ι] (β γ : ι → ℝ) (pos neg : Finset ι) {m H : ℝ}
    (hm : 1605 ≤ m) (hH : 0 < H) (disjoint : Disjoint pos neg)
    (strip : ∀ i, 0 ≤ β i ∧ β i ≤ 1)
    (location : ∀ i ∈ pos ∪ neg,m/4 ≤ |γ i| ∧ |γ i| ≤ m/2)
    (card₁ : (3*m/16)*H/16 ≤ (pos.card:ℝ)*π)
    (card₂ : (3*m/16)*H/16 ≤ (neg.card:ℝ)*π)
    (summ : Summable (fun i : ι => 1-cos (m*(arctan (β i/|γ i|)+arctan ((1-β i)/|γ i|))))):
    m*H/128 ≤ ∑' i : ι, (1-cos (m*(arctan (β i/|γ i|)+arctan ((1-β i)/|γ i|)))) := by
  classical
  let f : ι → ℝ := fun i => 1-cos (m*(arctan (β i/|γ i|)+arctan ((1-β i)/|γ i|)))
  have fs : Summable f := summ
  have fc : ((pos∪neg).card:ℝ)*(5/4) ≤ (∑ i ∈ pos∪neg,f i) := by
    calc
      _ = ∑ _i ∈ pos∪neg,(5/4:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => phase_band hm (location i hi).1 (location i hi).2 (strip i).1 (strip i).2)
  have all := fs.sum_le_tsum (pos∪neg) (fun i _ => sub_nonneg.mpr (cos_le_one _))
  have cards : ((pos∪neg).card:ℝ) = (pos.card:ℝ)+(neg.card:ℝ) := by exact_mod_cast Finset.card_union_of_disjoint disjoint
  rw [cards] at fc
  apply le_trans _ (fc.trans all)
  have mh := mul_pos (show 0 < m by linarith) hH
  have counts : 3*m*H/128 ≤ ((pos.card:ℝ)+(neg.card:ℝ))*π := by linarith
  have pii : π ≤ 15/4 := by linarith [pi_lt_d2]
  have aux := mul_le_mul_of_nonneg_left pii (show 0 ≤ (pos.card:ℝ)+(neg.card:ℝ) by positivity)
  linarith

#print axioms phase_band
#print axioms poisson_integral
#print axioms remote
#print axioms band_count
#print axioms from_bands
end LiPhaseMass
