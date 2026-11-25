import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact homogeneous subdivision. In a row the entry with index `i`
multiplies `x^i * y^(6-i)`. All coefficient arithmetic is over integers. -/
namespace EllipticBernstein

structure Seven (α : Type) where
  a : α
  b : α
  c : α
  d : α
  e : α
  f : α
  g : α

abbrev Row := Seven ℤ
abbrev Net := Seven Row

def map7 {α β : Type} (f : α → β) (r : Seven α) : Seven β :=
  ⟨f r.a, f r.b, f r.c, f r.d, f r.e, f r.f, f r.g⟩

def all7 {α : Type} (P : α → Prop) (r : Seven α) : Prop :=
  P r.a ∧ P r.b ∧ P r.c ∧ P r.d ∧ P r.e ∧ P r.f ∧ P r.g

instance {α : Type} (P : α → Prop) [DecidablePred P] (r : Seven α) : Decidable (all7 P r) := by
  unfold all7
  infer_instance

def value (r : Seven ℝ) (x y : ℝ) : ℝ :=
  r.a * x^0 * y^6 + r.b * x^1 * y^5 + r.c * x^2 * y^4 + r.d * x^3 * y^3 + r.e * x^4 * y^2 + r.f * x^5 * y^1 + r.g * x^6 * y^0

def rowValue (r : Row) (x y : ℝ) : ℝ :=
  value (map7 (fun a : ℤ => (a : ℝ)) r) x y

def netValue (n : Net) (x y u v : ℝ) : ℝ :=
  value (map7 (fun r => rowValue r u v) n) x y

def transpose (n : Net) : Net :=
  ⟨⟨n.a.a, n.b.a, n.c.a, n.d.a, n.e.a, n.f.a, n.g.a⟩, ⟨n.a.b, n.b.b, n.c.b, n.d.b, n.e.b, n.f.b, n.g.b⟩, ⟨n.a.c, n.b.c, n.c.c, n.d.c, n.e.c, n.f.c, n.g.c⟩, ⟨n.a.d, n.b.d, n.c.d, n.d.d, n.e.d, n.f.d, n.g.d⟩, ⟨n.a.e, n.b.e, n.c.e, n.d.e, n.e.e, n.f.e, n.g.e⟩, ⟨n.a.f, n.b.f, n.c.f, n.d.f, n.e.f, n.f.f, n.g.f⟩, ⟨n.a.g, n.b.g, n.c.g, n.d.g, n.e.g, n.f.g, n.g.g⟩⟩

def left (r : Row) : Row :=
  ⟨64 * r.a, 192 * r.a + 32 * r.b, 240 * r.a + 80 * r.b + 16 * r.c, 160 * r.a + 80 * r.b + 32 * r.c + 8 * r.d, 60 * r.a + 40 * r.b + 24 * r.c + 12 * r.d + 4 * r.e, 12 * r.a + 10 * r.b + 8 * r.c + 6 * r.d + 4 * r.e + 2 * r.f, r.a + r.b + r.c + r.d + r.e + r.f + r.g⟩

def right (r : Row) : Row :=
  ⟨r.a + r.b + r.c + r.d + r.e + r.f + r.g, 2 * r.b + 4 * r.c + 6 * r.d + 8 * r.e + 10 * r.f + 12 * r.g, 4 * r.c + 12 * r.d + 24 * r.e + 40 * r.f + 60 * r.g, 8 * r.d + 32 * r.e + 80 * r.f + 160 * r.g, 16 * r.e + 80 * r.f + 240 * r.g, 32 * r.f + 192 * r.g, 64 * r.g⟩


theorem left_value (r : Row) (x y : ℝ) :
    rowValue (left r) x y = rowValue r x (x + 2*y) := by
  simp [rowValue, value, map7, left]
  ring

theorem right_value (r : Row) (x y : ℝ) :
    rowValue (right r) x y = rowValue r (2*x+y) y := by
  simp [rowValue, value, map7, right]
  ring

theorem transpose_value (n : Net) (x y u v : ℝ) :
    netValue (transpose n) x y u v = netValue n u v x y := by
  simp only [netValue, rowValue, value, map7, transpose]
  ring

def splitYL (n : Net) : Net := map7 left n
def splitYR (n : Net) : Net := map7 right n
def splitXL (n : Net) : Net := transpose (splitYL (transpose n))
def splitXR (n : Net) : Net := transpose (splitYR (transpose n))

theorem splitYL_value (n : Net) (x y u v : ℝ) :
    netValue (splitYL n) x y u v = netValue n x y u (u+2*v) := by
  simp only [netValue, splitYL, map7, left_value]

theorem splitYR_value (n : Net) (x y u v : ℝ) :
    netValue (splitYR n) x y u v = netValue n x y (2*u+v) v := by
  simp only [netValue, splitYR, map7, right_value]

theorem splitXL_value (n : Net) (x y u v : ℝ) :
    netValue (splitXL n) x y u v = netValue n x (x+2*y) u v := by
  simp only [splitXL, transpose_value, splitYL_value]

theorem splitXR_value (n : Net) (x y u v : ℝ) :
    netValue (splitXR n) x y u v = netValue n (2*x+y) y u v := by
  simp only [splitXR, transpose_value, splitYR_value]

def rowGood (r : Row) := all7 (fun a : ℤ => 0 ≤ a) r
instance (r : Row) : Decidable (rowGood r) := by unfold rowGood; infer_instance
def netGood (n : Net) := all7 rowGood n
instance (n : Net) : Decidable (netGood n) := by unfold netGood; infer_instance

theorem value_nonneg (r : Seven ℝ) (h : all7 (fun a : ℝ => 0 ≤ a) r)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ value r x y := by
  rcases h with ⟨ha,hb,hc,hd,he,hf,hg⟩
  unfold value
  positivity

theorem rowValue_nonneg (r : Row) (h : rowGood r)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ rowValue r x y := by
  apply value_nonneg _ _ hx hy
  simp only [all7, map7]
  rcases h with ⟨ha,hb,hc,hd,he,hf,hg⟩
  exact ⟨by exact_mod_cast ha,by exact_mod_cast hb,by exact_mod_cast hc,
    by exact_mod_cast hd,by exact_mod_cast he,by exact_mod_cast hf,
    by exact_mod_cast hg⟩

def positiveOn (n : Net) : Prop :=
  ∀ x y u v : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ u → 0 ≤ v → 0 ≤ netValue n x y u v

theorem good_positive (n : Net) (h : netGood n) : positiveOn n := by
  intro x y u v hx hy hu hv
  apply value_nonneg _ _ hx hy
  rcases h with ⟨ha,hb,hc,hd,he,hf,hg⟩
  exact ⟨rowValue_nonneg _ ha hu hv, rowValue_nonneg _ hb hu hv,
    rowValue_nonneg _ hc hu hv, rowValue_nonneg _ hd hu hv,
    rowValue_nonneg _ he hu hv, rowValue_nonneg _ hf hu hv,
    rowValue_nonneg _ hg hu hv⟩

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

end EllipticBernstein
