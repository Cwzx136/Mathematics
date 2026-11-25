import Research.EdgeDisks
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Local zero repulsion in the coordinate L(1−β), L(γ−ℓT).
The analytic premise in the last theorem is the normalized upper budget
for the two selected zeros. All constants and finite geometric losses are proved here.
-/
namespace Resonance
open EdgeDisks

/-- Real part of a reciprocal at real horizontal distance a. -/
noncomputable def kernel (a y : ℝ) : ℝ := a/(a^2+y^2)

theorem kernel_axis {a : ℝ} (ha : 0 < a) : kernel a 0 = 1/a := by
  unfold kernel
  field_simp
  ring

theorem kernel_le_axis {a : ℝ} (ha : 0 < a) (y : ℝ) : kernel a y ≤ kernel a 0 := by
  rw [kernel_axis ha]
  unfold kernel
  apply (div_le_div_iff₀ (by positivity) ha).2
  nlinarith [sq_nonneg y]

/-- Moving the ordinate of the regular reflected kernel costs at most 8y². -/
theorem mirror_loss {a : ℝ} (ha : 1/2 ≤ a) (y : ℝ) :
    kernel a 0 - kernel a y ≤ 8*y^2 := by
  have hp : 0 < a := by linarith
  have hd : 0 < a^2+y^2 := by positivity
  have hdiff : kernel a 0-kernel a y = y^2/(a*(a^2+y^2)) := by
    rw [kernel_axis hp]
    unfold kernel
    field_simp
    ring
  have hcube : (1:ℝ)/8 ≤ a^3 := by
    calc (1:ℝ)/8 = (1/2:ℝ)^3 := by norm_num
         _ ≤ a^3 := pow_le_pow_left₀ (by norm_num) ha 3
  have hprod : 1/8 ≤ a*(a^2+y^2) := by
    nlinarith only [hcube, mul_nonneg hp.le (sq_nonneg y)]
  rw [hdiff]
  apply (div_le_iff₀ (mul_pos hp hd)).2
  nlinarith only [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hprod)]

/-- The surplus in the on-axis paired inequality implies its off-axis version.
Here b is the original distance to the reflected zero and c,d are the
two exterior distances in Stechkin's subtraction. -/
theorem off_axis_pair {a b c d k : ℝ} (hb : 1/2 ≤ b) (hc : 0 < c)
    (hd : 0 < d) (hk : 0 ≤ k) (axis : k*(kernel c 0+kernel d 0) ≤ kernel b 0)
    (y : ℝ) :
    kernel a y-8*y^2 ≤ kernel a y+kernel b y-k*(kernel c y+kernel d y) := by
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (kernel_le_axis hc y) (kernel_le_axis hd y)) hk
  linarith only [h, axis, mirror_loss hb y]

/-- Homogeneity in the local ordinate and edge distance. -/
theorem kernel_rescale {v x L : ℝ} (hL : 0 < L) (h : 0 < v+x) (y : ℝ) :
    kernel ((v+x)/L) (y/L) = L*poisson v x y := by
  have hd : 0 < (v+x)^2+y^2 := by positivity
  have hd' : 0 < ((v+x)/L)^2+(y/L)^2 := by positivity
  unfold kernel poisson
  field_simp

/-- On a rectangle the minimum is on the far vertical side when Y≤v. -/
theorem rectangle_lower {v X Y x y : ℝ} (hv : 0 < v) (hx : 0 ≤ x)
    (hxX : x ≤ X) (hy : |y| ≤ Y) (hY : Y ≤ v) :
    (v+X)/((v+X)^2+Y^2) ≤ poisson v x y := by
  have h0Y : 0 ≤ Y := (abs_nonneg y).trans hy
  have hu : 0 < v+x := by linarith
  have hU : 0 < v+X := by linarith
  have hy2 : y^2 ≤ Y^2 := by
    rw [← sq_abs y]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hprod : Y^2 ≤ (v+x)*(v+X) := by
    rw [pow_two]
    apply mul_le_mul (by linarith : Y ≤ v+x) (by linarith : Y ≤ v+X) h0Y hu.le
  unfold poisson
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [mul_nonneg (sub_nonneg.mpr hxX) (sub_nonneg.mpr hprod),
    mul_nonneg hU.le (sub_nonneg.mpr hy2)]

/-- The exact rational symmetric-square weight, static pole, and shifted half-degree. -/
noncomputable def weight : ℝ := 343537/1000000
noncomputable def pole : ℝ := 115561/250000
noncomputable def degreeCost : ℝ := 2284863/1000000
noncomputable def oldSlope : ℝ := (1-1/Real.sqrt 5)*degreeCost

theorem slope_upper : oldSlope ≤ (5/9)*degreeCost := by
  have hs : 0 < Real.sqrt 5 := by positivity
  have hs' : Real.sqrt 5 ≤ 9/4 := by
    nlinarith only [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), hs]
  have hk : (4:ℝ)/9 ≤ 1/Real.sqrt 5 := (le_div_iff₀ hs).2 (by linarith)
  unfold oldSlope
  exact mul_le_mul_of_nonneg_right (by linarith) (by norm_num [degreeCost])

/-- At the original height and at twice that height the two retained masses
exceed even the older Stechkin budget, with explicit slack 1/32. -/
theorem resonance_gap {x₁ x₂ y : ℝ}
    (h₁ : 0 ≤ x₁) (h₁' : x₁ ≤ 1/6) (h₂ : 0 ≤ x₂) (h₂' : x₂ ≤ 1/6)
    (hy : |y| ≤ 1/8) :
    pole/(1/4) + oldSlope + 1/32 <
      poisson (1/4) x₁ 0 + weight*poisson (1/4) x₂ y := by
  have s₁ := EdgeDisks.onAxis_lower (by norm_num : (0:ℝ)<1/4) h₁ h₁'
  have s₂ := rectangle_lower (v:=1/4) (by norm_num) h₂ h₂' hy (by norm_num)
  have sw := mul_le_mul_of_nonneg_left s₂ (by norm_num [weight] : 0 ≤ weight)
  have h := slope_upper
  norm_num [pole,weight,degreeCost] at s₁ sw h ⊢
  linarith only [s₁,sw,h]

/-- Quantitative rescaled loss, including the actual symmetric-square weight. -/
theorem weighted_loss {L y : ℝ} (hL : 2 ≤ L) (hy : |y| ≤ 1/8) :
    8*weight*(y/L)^2 ≤ L/64 := by
  have hp : 0 < L := by linarith
  have hdy : |y/L| ≤ 1/16 := by
    rw [abs_div, abs_of_pos hp]
    exact (div_le_iff₀ hp).2 (by linarith)
  have hds : (y/L)^2 ≤ (1/16:ℝ)^2 := by
    rw [← sq_abs (y/L)]
    exact pow_le_pow_left₀ (abs_nonneg _) hdy 2
  have hw : weight ≤ 1 := by norm_num [weight]
  have hp' := mul_le_mul_of_nonneg_right hw (sq_nonneg (y/L))
  nlinarith only [hp', hds, hL]

/-- Feed the unscaled Hadamard budget directly into the two-window proof.
The first mass is on axis; the second receives the loss proved in off_axis_pair. -/
theorem raw_resonance_impossible {L x₁ x₂ y m₁ m₂ : ℝ}
    (hL : 2 ≤ L)
    (hx₁ : 0 ≤ x₁) (hx₁' : x₁ ≤ 1/6)
    (hx₂ : 0 ≤ x₂) (hx₂' : x₂ ≤ 1/6) (hy : |y| ≤ 1/8)
    (target : L*poisson (1/4) x₁ 0 ≤ m₁)
    (partner : L*poisson (1/4) x₂ y-8*(y/L)^2 ≤ m₂)
    (budget : m₁+weight*m₂ ≤ L*(pole/(1/4)+oldSlope+1/64)) : False := by
  have hp : 0 < L := by linarith
  have gap := mul_lt_mul_of_pos_left (resonance_gap hx₁ hx₁' hx₂ hx₂' hy) hp
  have pw := mul_le_mul_of_nonneg_left partner (by norm_num [weight] : 0 ≤ weight)
  have loss := weighted_loss hL hy
  linarith only [gap, target, pw, loss, budget]

/-- Two original zeros in one rectangular window (indices may coincide
for a multiple zero) also exceed the height budget, with slack 1/64. -/
theorem two_zero_gap {x₁ x₂ y₁ y₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₁' : x₁ ≤ 1/5) (h₂ : 0 ≤ x₂) (h₂' : x₂ ≤ 1/5)
    (hy₁ : |y₁| ≤ 3/8) (hy₂ : |y₂| ≤ 3/8) :
    pole/(1/2) + oldSlope + 1/64 <
      poisson (1/2) x₁ y₁ + poisson (1/2) x₂ y₂ := by
  have s₁ := rectangle_lower (v:=1/2) (by norm_num) h₁ h₁' hy₁ (by norm_num)
  have s₂ := rectangle_lower (v:=1/2) (by norm_num) h₂ h₂' hy₂ (by norm_num)
  have h := slope_upper
  norm_num [pole,degreeCost] at s₁ s₂ h ⊢
  linarith only [s₁,s₂,h]

/-- The even forty-step mirror comparison has terminal coefficient 41/81.
This rational cost allows a wider resonant horizontal window. -/
theorem forty_step_resonance_gap {x₁ x₂ y : ℝ}
    (h₁ : 0 ≤ x₁) (h₁' : x₁ ≤ 3/16)
    (h₂ : 0 ≤ x₂) (h₂' : x₂ ≤ 3/16) (hy : |y| ≤ 1/8) :
    pole/(9/32)+(41/81)*degreeCost+1/64 <
      poisson (9/32) x₁ 0 + weight*poisson (9/32) x₂ y := by
  have s₁ := EdgeDisks.onAxis_lower (by norm_num : (0:ℝ)<9/32) h₁ h₁'
  have s₂ := rectangle_lower (v:=9/32) (by norm_num) h₂ h₂' hy (by norm_num)
  have sw := mul_le_mul_of_nonneg_left s₂ (by norm_num [weight] : 0 ≤ weight)
  norm_num [pole,weight,degreeCost] at s₁ sw ⊢
  linarith only [s₁,sw]

/-- For the same function a horizontal allowance of 1/4 (in units L)
still excludes a pair across the full height window of length 3/4. -/
theorem forty_step_two_zero_gap {x₁ x₂ y₁ y₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₁' : x₁ ≤ 1/4) (h₂ : 0 ≤ x₂) (h₂' : x₂ ≤ 1/4)
    (hy₁ : |y₁| ≤ 3/8) (hy₂ : |y₂| ≤ 3/8) :
    pole/(1/2)+(41/81)*degreeCost+1/32 <
      poisson (1/2) x₁ y₁ + poisson (1/2) x₂ y₂ := by
  have s₁ := rectangle_lower (v:=1/2) (by norm_num) h₁ h₁' hy₁ (by norm_num)
  have s₂ := rectangle_lower (v:=1/2) (by norm_num) h₂ h₂' hy₂ (by norm_num)
  norm_num [pole,degreeCost] at s₁ s₂ ⊢
  linarith only [s₁,s₂]

/-- Z₁, Z₂ are zero divisors represented by membership predicates. The
budget is over every signed center and every right-half-plane pair.
The quantified epsilon is absorbed by a fixed explicit rational slack. -/
theorem eventually_no_resonance
    (Z₁ Z₂ : ℝ → ℝ → Prop) (r : ℝ)
    (budget : ∀ e : ℝ, 0 < e → ∃ H : ℝ, ∀ T b b' g : ℝ, H ≤ |T| →
      Z₁ b T → Z₂ b' g → 1/2 < b → 1/2 < b' →
      let L := r*Real.log |T|
      |L*(g-2*T)| ≤ 1/8 →
      poisson (1/4) (L*(1-b)) 0 +
      weight*poisson (1/4) (L*(1-b')) (L*(g-2*T)) ≤ pole/(1/4)+oldSlope+e) :
    ∃ H : ℝ, ∀ T b b' g : ℝ, H ≤ |T| → Z₁ b T → Z₂ b' g →
      1/2 < b → 1/2 < b' →
      let L := r*Real.log |T|
      0 ≤ L*(1-b) → L*(1-b) ≤ 1/6 → 0 ≤ L*(1-b') → L*(1-b') ≤ 1/6 →
      1/8 < |L*(g-2*T)| := by
  obtain ⟨H,hH⟩ := budget (1/32) (by norm_num)
  refine ⟨H, ?_⟩
  intro T b b' g hT hz hz' hb hb'
  dsimp
  intro hx hx' hx₂ hx₂'
  by_contra! hy
  exact (not_le_of_gt (resonance_gap hx hx' hx₂ hx₂' hy))
    (hH T b b' g hT hz hz' hb hb' hy)

/-- The signed-height exclusion arising from the forty-step budget.
The physical ordinates T and g enter through g−2T. -/
theorem eventually_no_forty_step_resonance
    (Z₁ Z₂ : ℝ → ℝ → Prop) (r : ℝ)
    (budget : ∀ e : ℝ, 0 < e → ∃ H : ℝ, ∀ T b b' g : ℝ, H ≤ |T| →
      Z₁ b T → Z₂ b' g → 1/2 < b → 1/2 < b' →
      let L := r*Real.log |T|
      |L*(g-2*T)| ≤ 1/8 →
      poisson (9/32) (L*(1-b)) 0 +
      weight*poisson (9/32) (L*(1-b')) (L*(g-2*T)) ≤
      pole/(9/32)+(41/81)*degreeCost+e) :
    ∃ H : ℝ, ∀ T b b' g : ℝ, H ≤ |T| → Z₁ b T → Z₂ b' g →
      1/2 < b → 1/2 < b' →
      let L := r*Real.log |T|
      0 ≤ L*(1-b) → L*(1-b) ≤ 3/16 → 0 ≤ L*(1-b') → L*(1-b') ≤ 3/16 →
      1/8 < |L*(g-2*T)| := by
  obtain ⟨H,hH⟩ := budget (1/64) (by norm_num)
  refine ⟨H, ?_⟩
  intro T b b' g hT hz hz' hb hb'
  dsimp
  intro hx hx' hx₂ hx₂'
  by_contra! hy
  exact (not_le_of_gt (forty_step_resonance_gap hx hx' hx₂ hx₂' hy))
    (hH T b b' g hT hz hz' hb hb' hy)

#print axioms off_axis_pair
#print axioms kernel_rescale
#print axioms rectangle_lower
#print axioms resonance_gap
#print axioms weighted_loss
#print axioms raw_resonance_impossible
#print axioms two_zero_gap
#print axioms forty_step_resonance_gap
#print axioms forty_step_two_zero_gap
#print axioms eventually_no_forty_step_resonance
#print axioms eventually_no_resonance
end Resonance
