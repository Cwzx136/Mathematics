import EllipticLocal

/-! Rational polynomial for Weyl and Nelson height costs.
All coefficients are given in millionths. The exterior domain is covered as well. -/
namespace EllipticBernstein.Weyl

open EllipticBernstein

def table : List Entry :=
  [(0,0,469198), (0,2,417266), (0,4,33789), (0,6,1678), (1,1,1000000), (1,3,255287), (2,0,459526), (2,2,339719), (2,6,908), (3,1,194304), (3,3,2181), (4,0,38741), (6,0,1135), (6,2,477), (6,4,67)]

def interior : Net :=
  ⟨⟨6846848, 14557920, 9674528, (-2973632), 918976, (-75296), 9888⟩, ⟨10598016, (-5521152), (-46568448), (-43053056), (-3667584), (-375552), (-271872)⟩, ⟨3712672, (-38505184), (-48493696), 26281408, 63574688, 15685664, 2483776⟩, ⟨(-7865216), (-36240384), 36040064, 99396608, 36040064, (-36240384), (-7865216)⟩, ⟨2483776, 15685664, 63574688, 26281408, (-48493696), (-38505184), 3712672⟩, ⟨(-271872), (-375552), (-3667584), (-43053056), (-46568448), (-5521152), 10598016⟩, ⟨9888, (-75296), 918976, (-2973632), 9674528, 14557920, 6846848⟩⟩

def exterior : Net :=
  ⟨⟨9888, (-75296), 918976, (-2973632), 9674528, 14557920, 6846848⟩, ⟨165600, (-38112), 4590720, 12605632, 52307808, 46434336, 15241536⟩, ⟨997864, 4108496, 23924312, 49235552, 82366616, 51867344, 13356328⟩, ⟨2589600, 12654080, 34164256, 47098368, 53645024, 28573696, 6709088⟩, ⟨2817376, 10434752, 17205920, 16981632, 17205920, 10434752, 2817376⟩, ⟨993024, 3168768, 3737856, 3124224, 3737856, 3168768, 993024⟩, ⟨165504, 528128, 622976, 520704, 622976, 528128, 165504⟩⟩

theorem interior_identity (x y : ℝ) :
    netValue interior (x+1) (1-x) (y+1) (1-y) = 4096*evalTable x y table := by
  norm_num [interior, netValue, rowValue, map7, value, evalTable, table, chebU, chebT]
  ring

theorem exterior_identity (x y : ℝ) :
    netValue exterior (x-1) 1 (y+1) (1-y) = 64*evalTable x y table := by
  norm_num [exterior, netValue, rowValue, map7, value, evalTable, table, chebU, chebT]
  ring

theorem reflection (x y : ℝ) : evalTable (-x) (-y) table = evalTable x y table := by
  norm_num [table, evalTable, chebU, chebT]; ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem interior_certified : cert 14 true interior = true := by decide +kernel

theorem exterior_certified : cert 4 true exterior = true := by decide +kernel

theorem nonnegative (x y : ℝ) (hy0 : -1 ≤ y) (hy1 : y ≤ 1) : 0 ≤ evalTable x y table := by
  have ext (z t : ℝ) (hz : 1 ≤ z) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
      0 ≤ evalTable z t table := by
    have hp : positiveOn exterior := cert_sound 4 true _ exterior_certified
    have h := hp (z-1) 1 (t+1) (1-t)
      (by linarith) (by norm_num) (by linarith) (by linarith)
    rw [exterior_identity] at h
    linarith
  by_cases hx0 : -1 ≤ x
  · by_cases hx1 : x ≤ 1
    · have hp : positiveOn interior := cert_sound 14 true _ interior_certified
      have h := hp (x+1) (1-x) (y+1) (1-y)
        (by linarith) (by linarith) (by linarith) (by linarith)
      rw [interior_identity] at h
      linarith
    · exact ext x y (by linarith) hy0 hy1
  · have h := ext (-x) (-y) (by linarith) (by linarith) (by linarith)
    simpa only [reflection] using h

theorem fourier_nonnegative (x θ : ℝ) : 0 ≤ evalFourier x θ table := by
  rw [fourier_eq]
  exact nonnegative x _ (Real.neg_one_le_cos θ) (Real.cos_le_one θ)

/-- Charge one for the j=1 form at the Weyl exponent, and use Nelson's
dimension-dependent saving for the higher symmetric-power indices. -/
def degreeCost (j : Nat) : ℚ :=
  if j = 1 then 1/3 else
    let k : ℚ := j+1
    (k/4)*(1-2/(3*k^5-2*k^4-k^2))

def sumCost : List Entry → ℚ
  | [] => 0
  | (l,j,c)::rest => (if l=0 ∨ j=0 then 0 else c*degreeCost j) + sumCost rest

def slope : ℚ := sumCost table / weightAt 1 1 table
def pole : ℚ := (weightAt 0 0 table : ℚ) / weightAt 1 1 table

theorem weights_verified : weightAt 0 0 table = 469198 ∧ weightAt 1 1 table = 1000000 :=
  by decide +kernel

theorem slope_verified : slope = 33956950057987/37263240000000 := by decide +kernel
theorem pole_verified : pole = 469198/1000000 := by decide +kernel

/-- The certified archimedean cost-to-width ratio. The analytic estimate
supplying these costs for an L-function remains separate from this theorem. -/
theorem width_coefficient :
    (slope:ℝ)/(1-Real.sqrt (pole:ℝ))^2 < 918275/100000 := by
  rw [slope_verified, pole_verified]
  push_cast
  have hp : Real.sqrt (469198/1000000) ≤ (68498030/100000000:ℝ) := by
    apply (Real.sqrt_le_left (by norm_num)).2
    norm_num
  have hp' : 0 < 1-Real.sqrt (469198/1000000) := by linarith
  apply (div_lt_iff₀ (sq_pos_of_pos hp')).2
  have hsq : (1-(68498030/100000000:ℝ))^2 ≤ (1-Real.sqrt (469198/1000000))^2 := by
    apply (sq_le_sq₀ (by norm_num) hp'.le).2
    linarith
  calc
    (33956950057987/37263240000000:ℝ) <
      (918275/100000:ℝ)*(1-68498030/100000000)^2 := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by norm_num)

#print axioms fourier_nonnegative
#print axioms width_coefficient
end EllipticBernstein.Weyl
