import Research.Prior.LiReflectedPair
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Real-variable kernel and resonance estimates for the all-height quadratic Li criterion. -/
namespace LiAllHeights
open Real

/-- A Taylor bound for the reflected log modulus. -/
theorem cosh_loss {v : ℝ} (h : |v| ≤ 1) : cosh v - 1 ≤ v^2 := by
  have a := (abs_le.mp (abs_exp_sub_one_sub_id_le h)).2
  have hn : |-v| ≤ 1 := by simpa using h
  have b := (abs_le.mp (abs_exp_sub_one_sub_id_le hn)).2
  rw [cosh_eq]
  nlinarith

/-- A quadratic angular minorant out to two radians. -/
theorem angle_mass {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 2) :
    (25/72:ℝ)*x^2 ≤ 1-cos x := by
  have h := sin_ge_sub_cube (show 0 ≤ x/2 by linarith)
  have h3 : (x/2)^3 ≤ x/2 := by
    nlinarith [mul_nonneg (show 0 ≤ (x/2)*(1-x/2) from mul_nonneg (by linarith) (by linarith))
      (show 0 ≤ 1+x/2 by linarith)]
  have hs : 5*x/12 ≤ sin (x/2) := by linarith
  have hs' := mul_self_le_mul_self (show 0 ≤ 5*x/12 by positivity) hs
  have id : cos x = 2*cos (x/2)^2-1 := by
    conv_lhs => rw [show x=2*(x/2) by ring, cos_two_mul]
  nlinarith [sin_sq_add_cos_sq (x/2)]

/-- Every sufficiently distant zero supplies its own definite quadratic mass,
including the full modulus error. -/
theorem distant {m g θ u : ℝ} (hm : 33 ≤ m) (hg : m/2 ≤ g)
    (hl : g/(1+g^2) ≤ θ) (hh : θ ≤ 1/g) (hu : |u| ≤ 1/(2*g^2)) :
    0.34*(m/g)^2 ≤ 1 - cosh (m*u) * cos (m*θ) := by
  have mp : 0 < m := by linarith
  have gp : 0 < g := by linarith
  have g16 : 16 ≤ g := by linarith
  have sg : 256 ≤ g^2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤16) g16]
  have xl : 0.995/g ≤ θ := by
    refine le_trans ?_ hl
    apply (div_le_div_iff₀ gp (by positivity)).mpr
    nlinarith
  have xlo := mul_le_mul_of_nonneg_left xl mp.le
  have xhi := mul_le_mul_of_nonneg_left hh mp.le
  have cap : m/g ≤ 2 := (div_le_iff₀ gp).mpr (by linarith)
  have x0 : 0 ≤ m*θ := mul_nonneg mp.le ((by positivity : (0:ℝ) ≤ 0.995/g).trans xl)
  have angle := angle_mass x0 (by simpa only [mul_one_div] using xhi.trans (by simpa only [mul_one_div] using cap))
  have u' : |m*u| ≤ (m/g)/32 := by
    rw [abs_mul,abs_of_pos mp]
    calc
      _ ≤ m*(1/(2*g^2)) := mul_le_mul_of_nonneg_left hu mp.le
      _ ≤ _ := by
        rw [mul_one_div, div_div]
        apply div_le_div_of_nonneg_left mp.le (by positivity)
        nlinarith [mul_nonneg gp.le (show 0 ≤ g-16 by linarith)]
  have cu := cosh_loss (u'.trans (by linarith))
  have sq' := mul_self_le_mul_self (abs_nonneg (m*u)) u'
  have usq : (m*u)^2 ≤ ((m/g)/32)^2 := by
    simpa only [←sq, sq_abs] using sq'
  have xlo' : 0.995*(m/g) ≤ m*θ := by convert xlo using 1; ring
  have xsq := mul_self_le_mul_self (show 0 ≤ 0.995*(m/g) by positivity) xlo'
  have err := mul_le_mul_of_nonneg_left (cos_le_one (m*θ)) (sub_nonneg.mpr (one_le_cosh (m*u)))
  nlinarith [sq_nonneg (m/g)]

/-- A negative reflected term is forced into a neighborhood of a strictly
positive multiple of the full period. -/
theorem resonance {x v : ℝ} (hv : |v| ≤ x) (hn : 1 < cosh v * cos x) :
    ∃ k : ℕ, 0 < k ∧ |x-(k:ℝ)*(2*π)| < |v| := by
  have xp : 0 ≤ x := (abs_nonneg v).trans hv
  have pp : 0 < 2*π := by positivity
  let k : ℕ := ⌊(x+π)/(2*π)⌋₊
  have lo : (k:ℝ)*(2*π) ≤ x+π := (le_div_iff₀ pp).mp (Nat.floor_le (by positivity))
  have hi : x+π < ((k:ℝ)+1)*(2*π) := (div_lt_iff₀ pp).mp (Nat.lt_floor_add_one _)
  let w := |x-(k:ℝ)*(2*π)|
  have wp : 0 ≤ w := abs_nonneg _
  have wcap : w ≤ π := abs_le.mpr ⟨by linarith,by linarith⟩
  have wc : cos w = cos x := by
    dsimp [w]; rw [cos_abs,cos_sub_nat_mul_two_pi]
  have wl : w < |v| := by
    by_contra! h
    by_cases z : w=0
    · have vz : v=0 := abs_nonpos_iff.mp (by linarith)
      rw [vz,cosh_zero,one_mul] at hn
      exact (cos_le_one x).not_gt hn
    · have hh := LiReflectedPair.edge (lt_of_le_of_ne wp (Ne.symm z)) wcap h
      rw [wc] at hh; linarith
  refine ⟨k,?_,wl⟩
  by_contra! h
  have ke : k=0 := Nat.eq_zero_of_le_zero h
  dsimp [w] at wl
  simp only [ke,Nat.cast_zero,zero_mul,sub_zero,abs_of_nonneg xp] at wl
  linarith

/-- A near-resonance at a strip-zero ordinate fits into the radius-one Poisson
window centered at the reciprocal frequency. -/
theorem resonance_window {m g θ f : ℝ} (hm : 0 < m) (hg : 5 ≤ g) (hf : 0 < f)
    (hl : g/(1+g^2) ≤ θ) (hh : θ ≤ 1/g) (hc : |m*θ-f| ≤ m/(2*g^2)) :
    |g-m/f| < 1 := by
  have gp : 0 < g := by linarith
  have mg : 0 < m/g := div_pos hm gp
  have delta : 1/g-θ ≤ (1/g^2)/5 := by
    calc
      _ ≤ 1/g-g/(1+g^2) := by linarith
      _ = 1/(g*(1+g^2)) := by field_simp; ring
      _ ≤ _ := by
        rw [div_div]
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        nlinarith [mul_nonneg gp.le (mul_nonneg gp.le (sub_nonneg.mpr hg))]
  have upper := mul_le_mul_of_nonneg_left hh hm.le
  have err := mul_le_mul_of_nonneg_left delta hm.le
  have cc := (abs_le.mp hc)
  have cuts := abs_le.mp hc
  rw [mul_one_div] at upper
  rw [mul_sub, mul_one_div] at err
  rw [show m*((1/g^2)/5)=(m/g^2)/5 by ring] at err
  rw [show m/(2*g^2)=(m/g^2)/2 by ring] at cuts
  have coarse : |m/g-f| ≤ 0.7*m/g^2 := by
    rw [abs_le,show 0.7*m/g^2=0.7*(m/g^2) by ring]
    constructor <;> linarith [cuts.1,cuts.2, show 0 ≤ m/g^2 by positivity]
  have scaled : |m-f*g| ≤ 0.7*(m/g) := by
    calc
      _ = |(m/g-f)*g| := by rw [sub_mul,div_mul_cancel₀ _ gp.ne']
      _ = |m/g-f| * g := by rw [abs_mul,abs_of_pos gp]
      _ ≤ (0.7*m/g^2)*g := mul_le_mul_of_nonneg_right coarse gp.le
      _ = _ := by field_simp
  have fbound : 0.8*(m/g) ≤ f := by
    have d : 0.7*m/g^2 ≤ 0.2*(m/g) := by
      have h : 0.7 ≤ 0.2*g := by linarith
      have hh' := mul_le_mul_of_nonneg_right h (show 0 ≤ m/g^2 by positivity)
      convert hh' using 1 <;> field_simp
    linarith [(abs_le.mp coarse).2]
  calc
    |g-m/f| = |-(m-f*g)/f| := by congr 1; field_simp; ring
    _ = |m-f*g| / f := by rw [abs_div,abs_neg,abs_of_pos hf]
    _ < 1 := (div_lt_iff₀ hf).mpr (by linarith)


/-- The individual Hadamard summand at real abscissa `a`. -/
noncomputable def kernel (a β g : ℝ) : ℝ := (a-β)/((a-β)^2+g^2)

private theorem kernel_alt {a β g : ℝ} (h : 0 < a-β) :
    kernel a β g = 1/((a-β)+g^2/(a-β)) := by
  unfold kernel
  field_simp

/-- The difference of real-axis Poisson kernels removes all low zeros at once. -/
theorem kernel_cancel {r β g : ℝ} (hr : 16.5 ≤ r) (hb : 0 ≤ β) (hb' : β ≤ 1)
    (hg : |g| ≤ r) : kernel (4*r) β g ≤ 0.481 * kernel r β g := by
  let a := r-β
  let b := 4*r-β
  have ap : 0 < a := by dsimp [a]; linarith
  have bp : 0 < b := by dsimp [b]; linarith
  have rp : 0 < r := by linarith
  have gp2 : g^2 ≤ r^2 := by simpa only [←sq,sq_abs] using mul_self_le_mul_self (abs_nonneg g) hg
  have hb2 : β^2 ≤ 1 := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hb')]
  have top : a+r^2/a ≤ 2*r+2/31 := by
    rw [show a+r^2/a=2*r+β^2/a by field_simp [ap.ne']; dsimp [a]; ring]
    apply add_le_add_right
    apply (div_le_iff₀ ap).mpr
    dsimp [a]; linarith
  have bot : 17*r/4-1 ≤ b+r^2/b := by
    have h : r/4 ≤ r^2/b := by
      rw [le_div_iff₀ bp]; dsimp [b]; nlinarith [mul_nonneg rp.le hb]
    dsimp [b] at *; linarith
  have cap : a+r^2/a ≤ 0.481*(b+r^2/b) := by linarith
  have coef : 0 ≤ 1/a-0.481/b := by
    rw [sub_nonneg,div_le_div_iff₀ bp ap]
    dsimp [a,b]; linarith
  have dec := mul_nonneg coef (sub_nonneg.mpr gp2)
  have hg' : a+g^2/a ≤ 0.481*(b+g^2/b) := by
    rw [div_eq_mul_inv (g^2) a, div_eq_mul_inv (g^2) b]
    rw [div_eq_mul_inv (r^2) a, div_eq_mul_inv (r^2) b] at cap
    rw [one_div, div_eq_mul_inv] at dec
    nlinarith
  rw [kernel_alt bp, kernel_alt ap,mul_one_div]
  apply (div_le_div_iff₀ (show 0 < b+g^2/b from add_pos_of_pos_of_nonneg bp (by positivity))
    (show 0 < a+g^2/a from add_pos_of_pos_of_nonneg ap (by positivity))).mpr
  simpa using hg'

/-- A radius-one signed window has Poisson weight at least three tenths per zero. -/
theorem local_kernel {β g : ℝ} (hb : 0 ≤ β) (hb' : β ≤ 1) (hg : |g| ≤ 1) :
    0.3 ≤ kernel 3 β g := by
  have b : 0 < 3-β := by linarith
  have g2 : g^2 ≤ 1 := by simpa only [←sq,sq_abs,one_pow] using mul_self_le_mul_self (abs_nonneg g) hg
  unfold kernel
  rw [le_div_iff₀ (add_pos_of_pos_of_nonneg (sq_pos_of_pos b) (sq_nonneg g))]
  nlinarith [mul_nonneg hb (sub_nonneg.mpr hb')]

/-- The final comparison for every (real) index above 33. -/
theorem margin {m : ℝ} (hm : 33 ≤ m) :
    1.17*(√m+0.5)/(2*π) < 0.0357*m := by
  have mp : 0 < m := by linarith
  have h0 := sq_sqrt mp.le
  have h1 := sqrt_nonneg m
  have hbase : 5.74 ≤ √m := by nlinarith
  have lin : 5.74*√m ≤ m := by nlinarith [mul_nonneg h1 (sub_nonneg.mpr hbase)]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [mul_nonneg mp.le (sub_nonneg.mpr pi_gt_d2.le)]

/-- Summable positive distant mass dominates every resonance loss when the
two analytic Poisson estimates of the manuscript hold. -/
theorem total {m D B E V : ℝ} (hm : 33 ≤ m) (hD : 0 < D)
    (base : 0.0357*m*D ≤ B) (loss : E ≤ (1.17*(√m+0.5)/(2*π))*D)
    (decompose : B-E ≤ V) : 0 < V := by
  have h := mul_lt_mul_of_pos_right (margin hm) hD
  linarith

#print axioms cosh_loss
#print axioms angle_mass
#print axioms distant
#print axioms resonance
#print axioms resonance_window
#print axioms kernel_cancel
#print axioms local_kernel
#print axioms margin
#print axioms total

end LiAllHeights
