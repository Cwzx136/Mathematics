import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact homogeneous subdivision. In a row the entry with index `i`
multiplies `x^i * y^(12-i)`. All coefficient arithmetic is over integers. -/
namespace EllipticBernstein.Degree12
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

structure Coeff13 (α : Type) where
  a : α
  b : α
  c : α
  d : α
  e : α
  f : α
  g : α
  h : α
  i : α
  j : α
  k : α
  l : α
  m : α

abbrev Row := Coeff13 ℤ
abbrev Net := Coeff13 Row

def mapC {α β : Type} (f : α → β) (r : Coeff13 α) : Coeff13 β :=
  ⟨f r.a, f r.b, f r.c, f r.d, f r.e, f r.f, f r.g, f r.h, f r.i, f r.j, f r.k, f r.l, f r.m⟩

def allC {α : Type} (P : α → Prop) (r : Coeff13 α) : Prop :=
  P r.a ∧ P r.b ∧ P r.c ∧ P r.d ∧ P r.e ∧ P r.f ∧ P r.g ∧ P r.h ∧ P r.i ∧ P r.j ∧ P r.k ∧ P r.l ∧ P r.m

instance {α : Type} (P : α → Prop) [DecidablePred P] (r : Coeff13 α) : Decidable (allC P r) := by
  unfold allC
  infer_instance

def value (r : Coeff13 ℝ) (x y : ℝ) : ℝ :=
  r.a * x^0 * y^12 + r.b * x^1 * y^11 + r.c * x^2 * y^10 + r.d * x^3 * y^9 + r.e * x^4 * y^8 + r.f * x^5 * y^7 + r.g * x^6 * y^6 + r.h * x^7 * y^5 + r.i * x^8 * y^4 + r.j * x^9 * y^3 + r.k * x^10 * y^2 + r.l * x^11 * y^1 + r.m * x^12 * y^0

def rowValue (r : Row) (x y : ℝ) : ℝ :=
  value (mapC (fun a : ℤ => (a : ℝ)) r) x y

def netValue (n : Net) (x y u v : ℝ) : ℝ :=
  value (mapC (fun r => rowValue r u v) n) x y

def transpose (n : Net) : Net :=
  ⟨⟨n.a.a, n.b.a, n.c.a, n.d.a, n.e.a, n.f.a, n.g.a, n.h.a, n.i.a, n.j.a, n.k.a, n.l.a, n.m.a⟩, ⟨n.a.b, n.b.b, n.c.b, n.d.b, n.e.b, n.f.b, n.g.b, n.h.b, n.i.b, n.j.b, n.k.b, n.l.b, n.m.b⟩, ⟨n.a.c, n.b.c, n.c.c, n.d.c, n.e.c, n.f.c, n.g.c, n.h.c, n.i.c, n.j.c, n.k.c, n.l.c, n.m.c⟩, ⟨n.a.d, n.b.d, n.c.d, n.d.d, n.e.d, n.f.d, n.g.d, n.h.d, n.i.d, n.j.d, n.k.d, n.l.d, n.m.d⟩, ⟨n.a.e, n.b.e, n.c.e, n.d.e, n.e.e, n.f.e, n.g.e, n.h.e, n.i.e, n.j.e, n.k.e, n.l.e, n.m.e⟩, ⟨n.a.f, n.b.f, n.c.f, n.d.f, n.e.f, n.f.f, n.g.f, n.h.f, n.i.f, n.j.f, n.k.f, n.l.f, n.m.f⟩, ⟨n.a.g, n.b.g, n.c.g, n.d.g, n.e.g, n.f.g, n.g.g, n.h.g, n.i.g, n.j.g, n.k.g, n.l.g, n.m.g⟩, ⟨n.a.h, n.b.h, n.c.h, n.d.h, n.e.h, n.f.h, n.g.h, n.h.h, n.i.h, n.j.h, n.k.h, n.l.h, n.m.h⟩, ⟨n.a.i, n.b.i, n.c.i, n.d.i, n.e.i, n.f.i, n.g.i, n.h.i, n.i.i, n.j.i, n.k.i, n.l.i, n.m.i⟩, ⟨n.a.j, n.b.j, n.c.j, n.d.j, n.e.j, n.f.j, n.g.j, n.h.j, n.i.j, n.j.j, n.k.j, n.l.j, n.m.j⟩, ⟨n.a.k, n.b.k, n.c.k, n.d.k, n.e.k, n.f.k, n.g.k, n.h.k, n.i.k, n.j.k, n.k.k, n.l.k, n.m.k⟩, ⟨n.a.l, n.b.l, n.c.l, n.d.l, n.e.l, n.f.l, n.g.l, n.h.l, n.i.l, n.j.l, n.k.l, n.l.l, n.m.l⟩, ⟨n.a.m, n.b.m, n.c.m, n.d.m, n.e.m, n.f.m, n.g.m, n.h.m, n.i.m, n.j.m, n.k.m, n.l.m, n.m.m⟩⟩

def left (r : Row) : Row :=
  ⟨4096 * r.a, 24576 * r.a + 2048 * r.b, 67584 * r.a + 11264 * r.b + 1024 * r.c, 112640 * r.a + 28160 * r.b + 5120 * r.c + 512 * r.d, 126720 * r.a + 42240 * r.b + 11520 * r.c + 2304 * r.d + 256 * r.e, 101376 * r.a + 42240 * r.b + 15360 * r.c + 4608 * r.d + 1024 * r.e + 128 * r.f, 59136 * r.a + 29568 * r.b + 13440 * r.c + 5376 * r.d + 1792 * r.e + 448 * r.f + 64 * r.g, 25344 * r.a + 14784 * r.b + 8064 * r.c + 4032 * r.d + 1792 * r.e + 672 * r.f + 192 * r.g + 32 * r.h, 7920 * r.a + 5280 * r.b + 3360 * r.c + 2016 * r.d + 1120 * r.e + 560 * r.f + 240 * r.g + 80 * r.h + 16 * r.i, 1760 * r.a + 1320 * r.b + 960 * r.c + 672 * r.d + 448 * r.e + 280 * r.f + 160 * r.g + 80 * r.h + 32 * r.i + 8 * r.j, 264 * r.a + 220 * r.b + 180 * r.c + 144 * r.d + 112 * r.e + 84 * r.f + 60 * r.g + 40 * r.h + 24 * r.i + 12 * r.j + 4 * r.k, 24 * r.a + 22 * r.b + 20 * r.c + 18 * r.d + 16 * r.e + 14 * r.f + 12 * r.g + 10 * r.h + 8 * r.i + 6 * r.j + 4 * r.k + 2 * r.l, r.a + r.b + r.c + r.d + r.e + r.f + r.g + r.h + r.i + r.j + r.k + r.l + r.m⟩

def right (r : Row) : Row :=
  ⟨r.a + r.b + r.c + r.d + r.e + r.f + r.g + r.h + r.i + r.j + r.k + r.l + r.m, 2 * r.b + 4 * r.c + 6 * r.d + 8 * r.e + 10 * r.f + 12 * r.g + 14 * r.h + 16 * r.i + 18 * r.j + 20 * r.k + 22 * r.l + 24 * r.m, 4 * r.c + 12 * r.d + 24 * r.e + 40 * r.f + 60 * r.g + 84 * r.h + 112 * r.i + 144 * r.j + 180 * r.k + 220 * r.l + 264 * r.m, 8 * r.d + 32 * r.e + 80 * r.f + 160 * r.g + 280 * r.h + 448 * r.i + 672 * r.j + 960 * r.k + 1320 * r.l + 1760 * r.m, 16 * r.e + 80 * r.f + 240 * r.g + 560 * r.h + 1120 * r.i + 2016 * r.j + 3360 * r.k + 5280 * r.l + 7920 * r.m, 32 * r.f + 192 * r.g + 672 * r.h + 1792 * r.i + 4032 * r.j + 8064 * r.k + 14784 * r.l + 25344 * r.m, 64 * r.g + 448 * r.h + 1792 * r.i + 5376 * r.j + 13440 * r.k + 29568 * r.l + 59136 * r.m, 128 * r.h + 1024 * r.i + 4608 * r.j + 15360 * r.k + 42240 * r.l + 101376 * r.m, 256 * r.i + 2304 * r.j + 11520 * r.k + 42240 * r.l + 126720 * r.m, 512 * r.j + 5120 * r.k + 28160 * r.l + 112640 * r.m, 1024 * r.k + 11264 * r.l + 67584 * r.m, 2048 * r.l + 24576 * r.m, 4096 * r.m⟩


theorem left_value (r : Row) (x y : ℝ) :
    rowValue (left r) x y = rowValue r x (x + 2*y) := by
  simp [rowValue, value, mapC, left]
  ring

theorem right_value (r : Row) (x y : ℝ) :
    rowValue (right r) x y = rowValue r (2*x+y) y := by
  simp [rowValue, value, mapC, right]
  ring

def coord {α : Type} (c : Coeff13 α) (i : Fin 13) : α :=
  match (i : Nat) with
  | 0 => c.a
  | 1 => c.b
  | 2 => c.c
  | 3 => c.d
  | 4 => c.e
  | 5 => c.f
  | 6 => c.g
  | 7 => c.h
  | 8 => c.i
  | 9 => c.j
  | 10 => c.k
  | 11 => c.l
  | _ => c.m

theorem coord_mapC {α β : Type} (f : α → β) (r : Coeff13 α) (i : Fin 13) :
    coord (mapC f r) i = f (coord r i) := by fin_cases i <;> rfl

def mon (x y : ℝ) (i : Fin 13) := x^(i:Nat) * y^(12-(i:Nat))

theorem value_sum (r : Coeff13 ℝ) (x y : ℝ) :
    value r x y = ∑ i : Fin 13, coord r i * mon x y i := by
  simp [value, coord, mon, Fin.sum_univ_succ, mul_assoc, add_assoc]

theorem coord_transpose (n : Net) (i j : Fin 13) :
    coord (coord (transpose n) i) j = coord (coord n j) i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem netValue_sum (n : Net) (x y u v : ℝ) :
    netValue n x y u v = ∑ i : Fin 13, ∑ j : Fin 13,
        ((coord (coord n i) j : ℤ) : ℝ) * mon u v j * mon x y i := by
  simp only [netValue, rowValue, value_sum, coord_mapC, Finset.sum_mul]

theorem transpose_value (n : Net) (x y u v : ℝ) :
    netValue (transpose n) x y u v = netValue n u v x y := by
  rw [netValue_sum, netValue_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [coord_transpose]
  ring

def splitYL (n : Net) : Net := mapC left n
def splitYR (n : Net) : Net := mapC right n
def splitXL (n : Net) : Net := transpose (splitYL (transpose n))
def splitXR (n : Net) : Net := transpose (splitYR (transpose n))

theorem splitYL_value (n : Net) (x y u v : ℝ) :
    netValue (splitYL n) x y u v = netValue n x y u (u+2*v) := by
  simp only [netValue, splitYL, mapC, left_value]

theorem splitYR_value (n : Net) (x y u v : ℝ) :
    netValue (splitYR n) x y u v = netValue n x y (2*u+v) v := by
  simp only [netValue, splitYR, mapC, right_value]

theorem splitXL_value (n : Net) (x y u v : ℝ) :
    netValue (splitXL n) x y u v = netValue n x (x+2*y) u v := by
  simp only [splitXL, transpose_value, splitYL_value]

theorem splitXR_value (n : Net) (x y u v : ℝ) :
    netValue (splitXR n) x y u v = netValue n (2*x+y) y u v := by
  simp only [splitXR, transpose_value, splitYR_value]

def rowGood (r : Row) := allC (fun a : ℤ => 0 ≤ a) r
instance (r : Row) : Decidable (rowGood r) := by unfold rowGood; infer_instance
def netGood (n : Net) := allC rowGood n
instance (n : Net) : Decidable (netGood n) := by unfold netGood; infer_instance

theorem value_nonneg (r : Coeff13 ℝ) (h : allC (fun a : ℝ => 0 ≤ a) r)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ value r x y := by
  rcases h with ⟨h_a,h_b,h_c,h_d,h_e,h_f,h_g,h_h,h_i,h_j,h_k,h_l,h_m⟩
  unfold value
  positivity

theorem rowValue_nonneg (r : Row) (h : rowGood r)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ rowValue r x y := by
  apply value_nonneg _ _ hx hy
  simp only [allC, mapC]
  rcases h with ⟨h_a,h_b,h_c,h_d,h_e,h_f,h_g,h_h,h_i,h_j,h_k,h_l,h_m⟩
  exact ⟨by exact_mod_cast h_a, by exact_mod_cast h_b, by exact_mod_cast h_c, by exact_mod_cast h_d, by exact_mod_cast h_e, by exact_mod_cast h_f, by exact_mod_cast h_g, by exact_mod_cast h_h, by exact_mod_cast h_i, by exact_mod_cast h_j, by exact_mod_cast h_k, by exact_mod_cast h_l, by exact_mod_cast h_m⟩

def positiveOn (n : Net) : Prop :=
  ∀ x y u v : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ u → 0 ≤ v → 0 ≤ netValue n x y u v

theorem good_positive (n : Net) (h : netGood n) : positiveOn n := by
  intro x y u v hx hy hu hv
  apply value_nonneg _ _ hx hy
  rcases h with ⟨h_a,h_b,h_c,h_d,h_e,h_f,h_g,h_h,h_i,h_j,h_k,h_l,h_m⟩
  exact ⟨rowValue_nonneg _ h_a hu hv, rowValue_nonneg _ h_b hu hv, rowValue_nonneg _ h_c hu hv, rowValue_nonneg _ h_d hu hv, rowValue_nonneg _ h_e hu hv, rowValue_nonneg _ h_f hu hv, rowValue_nonneg _ h_g hu hv, rowValue_nonneg _ h_h hu hv, rowValue_nonneg _ h_i hu hv, rowValue_nonneg _ h_j hu hv, rowValue_nonneg _ h_k hu hv, rowValue_nonneg _ h_l hu hv, rowValue_nonneg _ h_m hu hv⟩

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

end EllipticBernstein.Degree12
