import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact homogeneous subdivision. In a row the entry with index `i`
multiplies `x^i * y^(8-i)`. All coefficient arithmetic is over integers. -/
namespace EllipticBernstein.Octic

structure Nine (α : Type) where
  a : α
  b : α
  c : α
  d : α
  e : α
  f : α
  g : α
  h : α
  i : α

abbrev Row := Nine ℤ
abbrev Net := Nine Row

def map9 {α β : Type} (f : α → β) (r : Nine α) : Nine β :=
  ⟨f r.a, f r.b, f r.c, f r.d, f r.e, f r.f, f r.g, f r.h, f r.i⟩

def all9 {α : Type} (P : α → Prop) (r : Nine α) : Prop :=
  P r.a ∧ P r.b ∧ P r.c ∧ P r.d ∧ P r.e ∧ P r.f ∧ P r.g ∧ P r.h ∧ P r.i

instance {α : Type} (P : α → Prop) [DecidablePred P] (r : Nine α) : Decidable (all9 P r) := by
  unfold all9
  infer_instance

def value (r : Nine ℝ) (x y : ℝ) : ℝ :=
  r.a * x^0 * y^8 + r.b * x^1 * y^7 + r.c * x^2 * y^6 + r.d * x^3 * y^5 + r.e * x^4 * y^4 + r.f * x^5 * y^3 + r.g * x^6 * y^2 + r.h * x^7 * y^1 + r.i * x^8 * y^0

def rowValue (r : Row) (x y : ℝ) : ℝ :=
  value (map9 (fun a : ℤ => (a : ℝ)) r) x y

def netValue (n : Net) (x y u v : ℝ) : ℝ :=
  value (map9 (fun r => rowValue r u v) n) x y

def transpose (n : Net) : Net :=
  ⟨⟨n.a.a, n.b.a, n.c.a, n.d.a, n.e.a, n.f.a, n.g.a, n.h.a, n.i.a⟩, ⟨n.a.b, n.b.b, n.c.b, n.d.b, n.e.b, n.f.b, n.g.b, n.h.b, n.i.b⟩, ⟨n.a.c, n.b.c, n.c.c, n.d.c, n.e.c, n.f.c, n.g.c, n.h.c, n.i.c⟩, ⟨n.a.d, n.b.d, n.c.d, n.d.d, n.e.d, n.f.d, n.g.d, n.h.d, n.i.d⟩, ⟨n.a.e, n.b.e, n.c.e, n.d.e, n.e.e, n.f.e, n.g.e, n.h.e, n.i.e⟩, ⟨n.a.f, n.b.f, n.c.f, n.d.f, n.e.f, n.f.f, n.g.f, n.h.f, n.i.f⟩, ⟨n.a.g, n.b.g, n.c.g, n.d.g, n.e.g, n.f.g, n.g.g, n.h.g, n.i.g⟩, ⟨n.a.h, n.b.h, n.c.h, n.d.h, n.e.h, n.f.h, n.g.h, n.h.h, n.i.h⟩, ⟨n.a.i, n.b.i, n.c.i, n.d.i, n.e.i, n.f.i, n.g.i, n.h.i, n.i.i⟩⟩

def left (r : Row) : Row :=
  ⟨256 * r.a, 1024 * r.a + 128 * r.b, 1792 * r.a + 448 * r.b + 64 * r.c, 1792 * r.a + 672 * r.b + 192 * r.c + 32 * r.d, 1120 * r.a + 560 * r.b + 240 * r.c + 80 * r.d + 16 * r.e, 448 * r.a + 280 * r.b + 160 * r.c + 80 * r.d + 32 * r.e + 8 * r.f, 112 * r.a + 84 * r.b + 60 * r.c + 40 * r.d + 24 * r.e + 12 * r.f + 4 * r.g, 16 * r.a + 14 * r.b + 12 * r.c + 10 * r.d + 8 * r.e + 6 * r.f + 4 * r.g + 2 * r.h, r.a + r.b + r.c + r.d + r.e + r.f + r.g + r.h + r.i⟩

def right (r : Row) : Row :=
  ⟨r.a + r.b + r.c + r.d + r.e + r.f + r.g + r.h + r.i, 2 * r.b + 4 * r.c + 6 * r.d + 8 * r.e + 10 * r.f + 12 * r.g + 14 * r.h + 16 * r.i, 4 * r.c + 12 * r.d + 24 * r.e + 40 * r.f + 60 * r.g + 84 * r.h + 112 * r.i, 8 * r.d + 32 * r.e + 80 * r.f + 160 * r.g + 280 * r.h + 448 * r.i, 16 * r.e + 80 * r.f + 240 * r.g + 560 * r.h + 1120 * r.i, 32 * r.f + 192 * r.g + 672 * r.h + 1792 * r.i, 64 * r.g + 448 * r.h + 1792 * r.i, 128 * r.h + 1024 * r.i, 256 * r.i⟩


theorem left_value (r : Row) (x y : ℝ) :
    rowValue (left r) x y = rowValue r x (x + 2*y) := by
  simp [rowValue, value, map9, left]
  ring

theorem right_value (r : Row) (x y : ℝ) :
    rowValue (right r) x y = rowValue r (2*x+y) y := by
  simp [rowValue, value, map9, right]
  ring

theorem transpose_value (n : Net) (x y u v : ℝ) :
    netValue (transpose n) x y u v = netValue n u v x y := by
  simp only [netValue, rowValue, value, map9, transpose]
  ring

def splitYL (n : Net) : Net := map9 left n
def splitYR (n : Net) : Net := map9 right n
def splitXL (n : Net) : Net := transpose (splitYL (transpose n))
def splitXR (n : Net) : Net := transpose (splitYR (transpose n))

theorem splitYL_value (n : Net) (x y u v : ℝ) :
    netValue (splitYL n) x y u v = netValue n x y u (u+2*v) := by
  simp only [netValue, splitYL, map9, left_value]

theorem splitYR_value (n : Net) (x y u v : ℝ) :
    netValue (splitYR n) x y u v = netValue n x y (2*u+v) v := by
  simp only [netValue, splitYR, map9, right_value]

theorem splitXL_value (n : Net) (x y u v : ℝ) :
    netValue (splitXL n) x y u v = netValue n x (x+2*y) u v := by
  simp only [splitXL, transpose_value, splitYL_value]

theorem splitXR_value (n : Net) (x y u v : ℝ) :
    netValue (splitXR n) x y u v = netValue n (2*x+y) y u v := by
  simp only [splitXR, transpose_value, splitYR_value]

def rowGood (r : Row) := all9 (fun a : ℤ => 0 ≤ a) r
instance (r : Row) : Decidable (rowGood r) := by unfold rowGood; infer_instance
def netGood (n : Net) := all9 rowGood n
instance (n : Net) : Decidable (netGood n) := by unfold netGood; infer_instance

theorem value_nonneg (r : Nine ℝ) (h : all9 (fun a : ℝ => 0 ≤ a) r)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ value r x y := by
  rcases h with ⟨ha,hb,hc,hd,he,hf,hg,hh,hi⟩
  unfold value
  positivity

theorem rowValue_nonneg (r : Row) (h : rowGood r)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ rowValue r x y := by
  apply value_nonneg _ _ hx hy
  simp only [all9, map9]
  rcases h with ⟨ha,hb,hc,hd,he,hf,hg,hh,hi⟩
  exact ⟨by exact_mod_cast ha,by exact_mod_cast hb,by exact_mod_cast hc,
    by exact_mod_cast hd,by exact_mod_cast he,by exact_mod_cast hf,
    by exact_mod_cast hg, by exact_mod_cast hh, by exact_mod_cast hi⟩

def positiveOn (n : Net) : Prop :=
  ∀ x y u v : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ u → 0 ≤ v → 0 ≤ netValue n x y u v

theorem good_positive (n : Net) (h : netGood n) : positiveOn n := by
  intro x y u v hx hy hu hv
  apply value_nonneg _ _ hx hy
  rcases h with ⟨ha,hb,hc,hd,he,hf,hg,hh,hi⟩
  exact ⟨rowValue_nonneg _ ha hu hv, rowValue_nonneg _ hb hu hv,
    rowValue_nonneg _ hc hu hv, rowValue_nonneg _ hd hu hv,
    rowValue_nonneg _ he hu hv, rowValue_nonneg _ hf hu hv,
    rowValue_nonneg _ hg hu hv,rowValue_nonneg _ hh hu hv,rowValue_nonneg _ hi hu hv⟩

theorem glueX (n : Net) (hl : positiveOn (splitXL n)) (hr : positiveOn (splitXR n)) :
    positiveOn n := by
  intro x y u v hx hy hu hv
  by_cases h : x ≤ y
  · have hh := hl x ((y-x)/2) u v hx (by linarith) hu hv
    rw [splitXL_value, show x+2*((y-x)/2)=y by ring] at hh
    exact hh
  · have hh := hr ((x-y)/2) y u v (by linarith) hy hu hv
    rw [splitXR_value, show 2*((x-y)/2)+y=x by ring] at hh
    exact hh

theorem glueY (n : Net) (hl : positiveOn (splitYL n)) (hr : positiveOn (splitYR n)) :
    positiveOn n := by
  intro x y u v hx hy hu hv
  by_cases h : u ≤ v
  · have hh := hl x y u ((v-u)/2) hx hy hu (by linarith)
    rw [splitYL_value, show u+2*((v-u)/2)=v by ring] at hh
    exact hh
  · have hh := hr x y ((u-v)/2) v hx hy (by linarith) hv
    rw [splitYR_value, show 2*((u-v)/2)+v=u by ring] at hh
    exact hh

def cert : Nat → Bool → Net → Bool
  | 0, _, n => decide (netGood n)
  | k+1, b, n => if netGood n then true else
    if b then cert k false (splitXL n) && cert k false (splitXR n)
    else cert k true (splitYL n) && cert k true (splitYR n)

theorem cert_sound (k : Nat) (b : Bool) (n : Net) (h : cert k b n = true) :
    positiveOn n := by
  induction k generalizing b n with
  | zero => exact good_positive n (of_decide_eq_true h)
  | succ k ih =>
    by_cases hn : netGood n
    · exact good_positive n hn
    · cases b with
      | false =>
        simp [cert, hn] at h
        exact glueY n (ih _ _ h.1) (ih _ _ h.2)
      | true =>
        simp [cert, hn] at h
        exact glueX n (ih _ _ h.1) (ih _ _ h.2)

end EllipticBernstein.Octic
