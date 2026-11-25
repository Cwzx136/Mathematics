import Research.CompactBump
import Mathlib.Tactic

/-! An exact upper Taylor certificate and the gain at the limiting
self-dual displacement in the signed spectral test. -/
noncomputable section
namespace ERH.RankSelfTilt
open ERH.Bump MeasureTheory Set

def tilt : ℝ := 69/100
def pole : ℝ := 35/99+99/280
def supExp (y : ℝ) := taylor9 (-y)+1/1000000

theorem exp_le_sup {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : Real.exp y ≤ supExp y := by
  have H := Real.exp_bound' (n := 10) h0 h1 (by decide)
  have hi : y^10 ≤ 1 := pow_le_one₀ h0 h1
  have hs : (∑ m ∈ Finset.range 10, y^m / m.factorial) = taylor9 (-y) := by
    norm_num [Finset.sum_range_succ,Nat.factorial,taylor9,horner]
    ring
  rw [hs] at H
  norm_num [Nat.factorial] at H
  unfold supExp
  linarith

def gain : ℝ := ∫ x in (0:ℝ)..1, 4*tilt*h x*(1-pole*Real.exp (tilt*x))

theorem self_tilt_gain : (25/146:ℝ) < gain := by
  let q : List ℝ := [(0), (186736549177/231000000000), (-10368929/15400000), (-286424372639/191537500000), (254316385395283/122584000000000), (71695860476314887/61292000000000000), (-34722996246246177599/12258400000000000000), (149956850903759223381/175120000000000000000), (3095665787770614733051161/6864704000000000000000000), (-91439200145825366437341099/686470400000000000000000000), (-18190073520075796595706972499/294201600000000000000000000000), (2770100505021346694149391/755117440000000000000000000), (80668002516692716354440377/27458816000000000000000000000), (177966141203408226772731/227656000000000000000000000), (759168134108939426738931/5491763200000000000000000000), (6448732980224777172999027/343235200000000000000000000000), (2291063655020213378457/1098352640000000000000000000), (194039717614532275923/980672000000000000000000000), (953218619568079101/54917632000000000000000000), (65772084750197457969/52171750400000000000000000000)]
  have diff (x : ℝ) : HasDerivAt (horner q) (4*tilt*h x*(1-pole*supExp (tilt*x))) x := by
    convert horner_hasDerivAt q x using 1
    dsimp [q,tilt,pole,h,supExp,taylor9,derivHorner,horner]
    ring
  have cont : Continuous (fun x => 4*tilt*h x*(1-pole*supExp (tilt*x))) := by
    unfold tilt pole h supExp taylor9; dsimp [horner]; fun_prop
  have act : Continuous (fun x => 4*tilt*h x*(1-pole*Real.exp (tilt*x))) := by
    unfold tilt pole h; fun_prop
  have M := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (cont.intervalIntegrable (μ := volume) 0 1) (act.intervalIntegrable (μ := volume) 0 1)
    (fun x hx => mul_le_mul_of_nonneg_left
      (sub_le_sub_left (mul_le_mul_of_nonneg_left
        (exp_le_sup (mul_nonneg (by norm_num [tilt]) hx.1)
          (by unfold tilt; linarith [hx.2])) (by norm_num [pole])) 1)
      (mul_nonneg (by norm_num [tilt]) (h_nonneg hx)))
  have I := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun x _ => diff x) (cont.intervalIntegrable (μ := volume) 0 1)
  rw [I] at M
  exact lt_of_lt_of_le (by norm_num [q,horner]) M

/-- Closure at the limiting displacement.  The hypothesis is precisely the
one-parameter signed comparison for every strict prior and every scale. -/
theorem limiting_displacement {H : ℝ → ℝ} (hH : Continuous H)
    {l P G : ℝ} (hl : 0 < l)
    (hcomp : ∀ a ∈ Ioo 0 l, ∀ W > 0,
      H ((l-a)/W)-P*H (-a/W) ≤ W*G) {t : ℝ} (ht : 0 < t) :
    t*(H 0-P*H (-t)) ≤ l*G := by
  let W := l/t
  have hW : 0 < W := div_pos hl ht
  let f : ℝ → ℝ := fun a => H ((l-a)/W)-P*H (-a/W)
  have hf : Continuous f := by unfold f; fun_prop
  have hclosed : IsClosed {a : ℝ | f a ≤ W*G} := isClosed_le hf continuous_const
  have hsub : Ioo 0 l ⊆ {a : ℝ | f a ≤ W*G} := fun a ha => hcomp a ha W hW
  have hm : l ∈ closure (Ioo 0 l) := by
    rw [closure_Ioo hl.ne]
    exact ⟨hl.le,le_rfl⟩
  have he := closure_minimal hsub hclosed hm
  change H ((l-l)/(l/t))-P*H (-l/(l/t)) ≤ (l/t)*G at he
  have harg : -l/(l/t) = -t := by field_simp
  rw [sub_self,zero_div,harg] at he
  calc t*(H 0-P*H (-t)) ≤ t*((l/t)*G) := mul_le_mul_of_nonneg_left he ht.le
       _ = l*G := by field_simp

end ERH.RankSelfTilt
