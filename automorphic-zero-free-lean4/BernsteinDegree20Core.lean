import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact homogeneous subdivision. In a row the entry with index `i`
multiplies `x^i * y^(20-i)`. All coefficient arithmetic is over integers. -/
namespace EllipticBernstein.Degree20
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

structure Coeff21 (α : Type) where
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
  n : α
  o : α
  p : α
  q : α
  r : α
  s : α
  t : α
  u : α

abbrev Row := Coeff21 ℤ
abbrev Net := Coeff21 Row

def mapC {α β : Type} (f : α → β) (r : Coeff21 α) : Coeff21 β :=
  ⟨f r.a, f r.b, f r.c, f r.d, f r.e, f r.f, f r.g, f r.h, f r.i, f r.j, f r.k, f r.l, f r.m, f r.n, f r.o, f r.p, f r.q, f r.r, f r.s, f r.t, f r.u⟩

def allC {α : Type} (P : α → Prop) (r : Coeff21 α) : Prop :=
  P r.a ∧ P r.b ∧ P r.c ∧ P r.d ∧ P r.e ∧ P r.f ∧ P r.g ∧ P r.h ∧ P r.i ∧ P r.j ∧ P r.k ∧ P r.l ∧ P r.m ∧ P r.n ∧ P r.o ∧ P r.p ∧ P r.q ∧ P r.r ∧ P r.s ∧ P r.t ∧ P r.u

instance {α : Type} (P : α → Prop) [DecidablePred P] (r : Coeff21 α) : Decidable (allC P r) := by
  unfold allC
  infer_instance

def value (r : Coeff21 ℝ) (x y : ℝ) : ℝ :=
  r.a * x^0 * y^20 + r.b * x^1 * y^19 + r.c * x^2 * y^18 + r.d * x^3 * y^17 + r.e * x^4 * y^16 + r.f * x^5 * y^15 + r.g * x^6 * y^14 + r.h * x^7 * y^13 + r.i * x^8 * y^12 + r.j * x^9 * y^11 + r.k * x^10 * y^10 + r.l * x^11 * y^9 + r.m * x^12 * y^8 + r.n * x^13 * y^7 + r.o * x^14 * y^6 + r.p * x^15 * y^5 + r.q * x^16 * y^4 + r.r * x^17 * y^3 + r.s * x^18 * y^2 + r.t * x^19 * y^1 + r.u * x^20 * y^0

def rowValue (r : Row) (x y : ℝ) : ℝ :=
  value (mapC (fun a : ℤ => (a : ℝ)) r) x y

def netValue (n : Net) (x y u v : ℝ) : ℝ :=
  value (mapC (fun r => rowValue r u v) n) x y

def transpose (n : Net) : Net :=
  ⟨⟨n.a.a, n.b.a, n.c.a, n.d.a, n.e.a, n.f.a, n.g.a, n.h.a, n.i.a, n.j.a, n.k.a, n.l.a, n.m.a, n.n.a, n.o.a, n.p.a, n.q.a, n.r.a, n.s.a, n.t.a, n.u.a⟩, ⟨n.a.b, n.b.b, n.c.b, n.d.b, n.e.b, n.f.b, n.g.b, n.h.b, n.i.b, n.j.b, n.k.b, n.l.b, n.m.b, n.n.b, n.o.b, n.p.b, n.q.b, n.r.b, n.s.b, n.t.b, n.u.b⟩, ⟨n.a.c, n.b.c, n.c.c, n.d.c, n.e.c, n.f.c, n.g.c, n.h.c, n.i.c, n.j.c, n.k.c, n.l.c, n.m.c, n.n.c, n.o.c, n.p.c, n.q.c, n.r.c, n.s.c, n.t.c, n.u.c⟩, ⟨n.a.d, n.b.d, n.c.d, n.d.d, n.e.d, n.f.d, n.g.d, n.h.d, n.i.d, n.j.d, n.k.d, n.l.d, n.m.d, n.n.d, n.o.d, n.p.d, n.q.d, n.r.d, n.s.d, n.t.d, n.u.d⟩, ⟨n.a.e, n.b.e, n.c.e, n.d.e, n.e.e, n.f.e, n.g.e, n.h.e, n.i.e, n.j.e, n.k.e, n.l.e, n.m.e, n.n.e, n.o.e, n.p.e, n.q.e, n.r.e, n.s.e, n.t.e, n.u.e⟩, ⟨n.a.f, n.b.f, n.c.f, n.d.f, n.e.f, n.f.f, n.g.f, n.h.f, n.i.f, n.j.f, n.k.f, n.l.f, n.m.f, n.n.f, n.o.f, n.p.f, n.q.f, n.r.f, n.s.f, n.t.f, n.u.f⟩, ⟨n.a.g, n.b.g, n.c.g, n.d.g, n.e.g, n.f.g, n.g.g, n.h.g, n.i.g, n.j.g, n.k.g, n.l.g, n.m.g, n.n.g, n.o.g, n.p.g, n.q.g, n.r.g, n.s.g, n.t.g, n.u.g⟩, ⟨n.a.h, n.b.h, n.c.h, n.d.h, n.e.h, n.f.h, n.g.h, n.h.h, n.i.h, n.j.h, n.k.h, n.l.h, n.m.h, n.n.h, n.o.h, n.p.h, n.q.h, n.r.h, n.s.h, n.t.h, n.u.h⟩, ⟨n.a.i, n.b.i, n.c.i, n.d.i, n.e.i, n.f.i, n.g.i, n.h.i, n.i.i, n.j.i, n.k.i, n.l.i, n.m.i, n.n.i, n.o.i, n.p.i, n.q.i, n.r.i, n.s.i, n.t.i, n.u.i⟩, ⟨n.a.j, n.b.j, n.c.j, n.d.j, n.e.j, n.f.j, n.g.j, n.h.j, n.i.j, n.j.j, n.k.j, n.l.j, n.m.j, n.n.j, n.o.j, n.p.j, n.q.j, n.r.j, n.s.j, n.t.j, n.u.j⟩, ⟨n.a.k, n.b.k, n.c.k, n.d.k, n.e.k, n.f.k, n.g.k, n.h.k, n.i.k, n.j.k, n.k.k, n.l.k, n.m.k, n.n.k, n.o.k, n.p.k, n.q.k, n.r.k, n.s.k, n.t.k, n.u.k⟩, ⟨n.a.l, n.b.l, n.c.l, n.d.l, n.e.l, n.f.l, n.g.l, n.h.l, n.i.l, n.j.l, n.k.l, n.l.l, n.m.l, n.n.l, n.o.l, n.p.l, n.q.l, n.r.l, n.s.l, n.t.l, n.u.l⟩, ⟨n.a.m, n.b.m, n.c.m, n.d.m, n.e.m, n.f.m, n.g.m, n.h.m, n.i.m, n.j.m, n.k.m, n.l.m, n.m.m, n.n.m, n.o.m, n.p.m, n.q.m, n.r.m, n.s.m, n.t.m, n.u.m⟩, ⟨n.a.n, n.b.n, n.c.n, n.d.n, n.e.n, n.f.n, n.g.n, n.h.n, n.i.n, n.j.n, n.k.n, n.l.n, n.m.n, n.n.n, n.o.n, n.p.n, n.q.n, n.r.n, n.s.n, n.t.n, n.u.n⟩, ⟨n.a.o, n.b.o, n.c.o, n.d.o, n.e.o, n.f.o, n.g.o, n.h.o, n.i.o, n.j.o, n.k.o, n.l.o, n.m.o, n.n.o, n.o.o, n.p.o, n.q.o, n.r.o, n.s.o, n.t.o, n.u.o⟩, ⟨n.a.p, n.b.p, n.c.p, n.d.p, n.e.p, n.f.p, n.g.p, n.h.p, n.i.p, n.j.p, n.k.p, n.l.p, n.m.p, n.n.p, n.o.p, n.p.p, n.q.p, n.r.p, n.s.p, n.t.p, n.u.p⟩, ⟨n.a.q, n.b.q, n.c.q, n.d.q, n.e.q, n.f.q, n.g.q, n.h.q, n.i.q, n.j.q, n.k.q, n.l.q, n.m.q, n.n.q, n.o.q, n.p.q, n.q.q, n.r.q, n.s.q, n.t.q, n.u.q⟩, ⟨n.a.r, n.b.r, n.c.r, n.d.r, n.e.r, n.f.r, n.g.r, n.h.r, n.i.r, n.j.r, n.k.r, n.l.r, n.m.r, n.n.r, n.o.r, n.p.r, n.q.r, n.r.r, n.s.r, n.t.r, n.u.r⟩, ⟨n.a.s, n.b.s, n.c.s, n.d.s, n.e.s, n.f.s, n.g.s, n.h.s, n.i.s, n.j.s, n.k.s, n.l.s, n.m.s, n.n.s, n.o.s, n.p.s, n.q.s, n.r.s, n.s.s, n.t.s, n.u.s⟩, ⟨n.a.t, n.b.t, n.c.t, n.d.t, n.e.t, n.f.t, n.g.t, n.h.t, n.i.t, n.j.t, n.k.t, n.l.t, n.m.t, n.n.t, n.o.t, n.p.t, n.q.t, n.r.t, n.s.t, n.t.t, n.u.t⟩, ⟨n.a.u, n.b.u, n.c.u, n.d.u, n.e.u, n.f.u, n.g.u, n.h.u, n.i.u, n.j.u, n.k.u, n.l.u, n.m.u, n.n.u, n.o.u, n.p.u, n.q.u, n.r.u, n.s.u, n.t.u, n.u.u⟩⟩

def left (r : Row) : Row :=
  ⟨1048576 * r.a, 10485760 * r.a + 524288 * r.b, 49807360 * r.a + 4980736 * r.b + 262144 * r.c, 149422080 * r.a + 22413312 * r.b + 2359296 * r.c + 131072 * r.d, 317521920 * r.a + 63504384 * r.b + 10027008 * r.c + 1114112 * r.d + 65536 * r.e, 508035072 * r.a + 127008768 * r.b + 26738688 * r.c + 4456448 * r.d + 524288 * r.e + 32768 * r.f, 635043840 * r.a + 190513152 * r.b + 50135040 * r.c + 11141120 * r.d + 1966080 * r.e + 245760 * r.f + 16384 * r.g, 635043840 * r.a + 222265344 * r.b + 70189056 * r.c + 19496960 * r.d + 4587520 * r.e + 860160 * r.f + 114688 * r.g + 8192 * r.h, 515973120 * r.a + 206389248 * r.b + 76038144 * r.c + 25346048 * r.d + 7454720 * r.e + 1863680 * r.f + 372736 * r.g + 53248 * r.h + 4096 * r.i, 343982080 * r.a + 154791936 * r.b + 65175552 * r.c + 25346048 * r.d + 8945664 * r.e + 2795520 * r.f + 745472 * r.g + 159744 * r.h + 24576 * r.i + 2048 * r.j, 189190144 * r.a + 94595072 * r.b + 44808192 * r.c + 19914752 * r.d + 8200192 * r.e + 3075072 * r.f + 1025024 * r.g + 292864 * r.h + 67584 * r.i + 11264 * r.j + 1024 * r.k, 85995520 * r.a + 47297536 * r.b + 24893440 * r.c + 12446720 * r.d + 5857280 * r.e + 2562560 * r.f + 1025024 * r.g + 366080 * r.h + 112640 * r.i + 28160 * r.j + 5120 * r.k + 512 * r.l, 32248320 * r.a + 19348992 * r.b + 11202048 * r.c + 6223360 * r.d + 3294720 * r.e + 1647360 * r.f + 768768 * r.g + 329472 * r.h + 126720 * r.i + 42240 * r.j + 11520 * r.k + 2304 * r.l + 256 * r.m, 9922560 * r.a + 6449664 * r.b + 4073472 * r.c + 2489344 * r.d + 1464320 * r.e + 823680 * r.f + 439296 * r.g + 219648 * r.h + 101376 * r.i + 42240 * r.j + 15360 * r.k + 4608 * r.l + 1024 * r.m + 128 * r.n, 2480640 * r.a + 1736448 * r.b + 1188096 * r.c + 792064 * r.d + 512512 * r.e + 320320 * r.f + 192192 * r.g + 109824 * r.h + 59136 * r.i + 29568 * r.j + 13440 * r.k + 5376 * r.l + 1792 * r.m + 448 * r.n + 64 * r.o, 496128 * r.a + 372096 * r.b + 274176 * r.c + 198016 * r.d + 139776 * r.e + 96096 * r.f + 64064 * r.g + 41184 * r.h + 25344 * r.i + 14784 * r.j + 8064 * r.k + 4032 * r.l + 1792 * r.m + 672 * r.n + 192 * r.o + 32 * r.p, 77520 * r.a + 62016 * r.b + 48960 * r.c + 38080 * r.d + 29120 * r.e + 21840 * r.f + 16016 * r.g + 11440 * r.h + 7920 * r.i + 5280 * r.j + 3360 * r.k + 2016 * r.l + 1120 * r.m + 560 * r.n + 240 * r.o + 80 * r.p + 16 * r.q, 9120 * r.a + 7752 * r.b + 6528 * r.c + 5440 * r.d + 4480 * r.e + 3640 * r.f + 2912 * r.g + 2288 * r.h + 1760 * r.i + 1320 * r.j + 960 * r.k + 672 * r.l + 448 * r.m + 280 * r.n + 160 * r.o + 80 * r.p + 32 * r.q + 8 * r.r, 760 * r.a + 684 * r.b + 612 * r.c + 544 * r.d + 480 * r.e + 420 * r.f + 364 * r.g + 312 * r.h + 264 * r.i + 220 * r.j + 180 * r.k + 144 * r.l + 112 * r.m + 84 * r.n + 60 * r.o + 40 * r.p + 24 * r.q + 12 * r.r + 4 * r.s, 40 * r.a + 38 * r.b + 36 * r.c + 34 * r.d + 32 * r.e + 30 * r.f + 28 * r.g + 26 * r.h + 24 * r.i + 22 * r.j + 20 * r.k + 18 * r.l + 16 * r.m + 14 * r.n + 12 * r.o + 10 * r.p + 8 * r.q + 6 * r.r + 4 * r.s + 2 * r.t, r.a + r.b + r.c + r.d + r.e + r.f + r.g + r.h + r.i + r.j + r.k + r.l + r.m + r.n + r.o + r.p + r.q + r.r + r.s + r.t + r.u⟩

def right (r : Row) : Row :=
  ⟨r.a + r.b + r.c + r.d + r.e + r.f + r.g + r.h + r.i + r.j + r.k + r.l + r.m + r.n + r.o + r.p + r.q + r.r + r.s + r.t + r.u, 2 * r.b + 4 * r.c + 6 * r.d + 8 * r.e + 10 * r.f + 12 * r.g + 14 * r.h + 16 * r.i + 18 * r.j + 20 * r.k + 22 * r.l + 24 * r.m + 26 * r.n + 28 * r.o + 30 * r.p + 32 * r.q + 34 * r.r + 36 * r.s + 38 * r.t + 40 * r.u, 4 * r.c + 12 * r.d + 24 * r.e + 40 * r.f + 60 * r.g + 84 * r.h + 112 * r.i + 144 * r.j + 180 * r.k + 220 * r.l + 264 * r.m + 312 * r.n + 364 * r.o + 420 * r.p + 480 * r.q + 544 * r.r + 612 * r.s + 684 * r.t + 760 * r.u, 8 * r.d + 32 * r.e + 80 * r.f + 160 * r.g + 280 * r.h + 448 * r.i + 672 * r.j + 960 * r.k + 1320 * r.l + 1760 * r.m + 2288 * r.n + 2912 * r.o + 3640 * r.p + 4480 * r.q + 5440 * r.r + 6528 * r.s + 7752 * r.t + 9120 * r.u, 16 * r.e + 80 * r.f + 240 * r.g + 560 * r.h + 1120 * r.i + 2016 * r.j + 3360 * r.k + 5280 * r.l + 7920 * r.m + 11440 * r.n + 16016 * r.o + 21840 * r.p + 29120 * r.q + 38080 * r.r + 48960 * r.s + 62016 * r.t + 77520 * r.u, 32 * r.f + 192 * r.g + 672 * r.h + 1792 * r.i + 4032 * r.j + 8064 * r.k + 14784 * r.l + 25344 * r.m + 41184 * r.n + 64064 * r.o + 96096 * r.p + 139776 * r.q + 198016 * r.r + 274176 * r.s + 372096 * r.t + 496128 * r.u, 64 * r.g + 448 * r.h + 1792 * r.i + 5376 * r.j + 13440 * r.k + 29568 * r.l + 59136 * r.m + 109824 * r.n + 192192 * r.o + 320320 * r.p + 512512 * r.q + 792064 * r.r + 1188096 * r.s + 1736448 * r.t + 2480640 * r.u, 128 * r.h + 1024 * r.i + 4608 * r.j + 15360 * r.k + 42240 * r.l + 101376 * r.m + 219648 * r.n + 439296 * r.o + 823680 * r.p + 1464320 * r.q + 2489344 * r.r + 4073472 * r.s + 6449664 * r.t + 9922560 * r.u, 256 * r.i + 2304 * r.j + 11520 * r.k + 42240 * r.l + 126720 * r.m + 329472 * r.n + 768768 * r.o + 1647360 * r.p + 3294720 * r.q + 6223360 * r.r + 11202048 * r.s + 19348992 * r.t + 32248320 * r.u, 512 * r.j + 5120 * r.k + 28160 * r.l + 112640 * r.m + 366080 * r.n + 1025024 * r.o + 2562560 * r.p + 5857280 * r.q + 12446720 * r.r + 24893440 * r.s + 47297536 * r.t + 85995520 * r.u, 1024 * r.k + 11264 * r.l + 67584 * r.m + 292864 * r.n + 1025024 * r.o + 3075072 * r.p + 8200192 * r.q + 19914752 * r.r + 44808192 * r.s + 94595072 * r.t + 189190144 * r.u, 2048 * r.l + 24576 * r.m + 159744 * r.n + 745472 * r.o + 2795520 * r.p + 8945664 * r.q + 25346048 * r.r + 65175552 * r.s + 154791936 * r.t + 343982080 * r.u, 4096 * r.m + 53248 * r.n + 372736 * r.o + 1863680 * r.p + 7454720 * r.q + 25346048 * r.r + 76038144 * r.s + 206389248 * r.t + 515973120 * r.u, 8192 * r.n + 114688 * r.o + 860160 * r.p + 4587520 * r.q + 19496960 * r.r + 70189056 * r.s + 222265344 * r.t + 635043840 * r.u, 16384 * r.o + 245760 * r.p + 1966080 * r.q + 11141120 * r.r + 50135040 * r.s + 190513152 * r.t + 635043840 * r.u, 32768 * r.p + 524288 * r.q + 4456448 * r.r + 26738688 * r.s + 127008768 * r.t + 508035072 * r.u, 65536 * r.q + 1114112 * r.r + 10027008 * r.s + 63504384 * r.t + 317521920 * r.u, 131072 * r.r + 2359296 * r.s + 22413312 * r.t + 149422080 * r.u, 262144 * r.s + 4980736 * r.t + 49807360 * r.u, 524288 * r.t + 10485760 * r.u, 1048576 * r.u⟩


theorem left_value (r : Row) (x y : ℝ) :
    rowValue (left r) x y = rowValue r x (x + 2*y) := by
  simp [rowValue, value, mapC, left]
  ring

theorem right_value (r : Row) (x y : ℝ) :
    rowValue (right r) x y = rowValue r (2*x+y) y := by
  simp [rowValue, value, mapC, right]
  ring

def coord {α : Type} (c : Coeff21 α) (i : Fin 21) : α :=
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
  | 12 => c.m
  | 13 => c.n
  | 14 => c.o
  | 15 => c.p
  | 16 => c.q
  | 17 => c.r
  | 18 => c.s
  | 19 => c.t
  | _ => c.u

theorem coord_mapC {α β : Type} (f : α → β) (r : Coeff21 α) (i : Fin 21) :
    coord (mapC f r) i = f (coord r i) := by fin_cases i <;> rfl

def mon (x y : ℝ) (i : Fin 21) := x^(i:Nat) * y^(20-(i:Nat))

theorem value_sum (r : Coeff21 ℝ) (x y : ℝ) :
    value r x y = ∑ i : Fin 21, coord r i * mon x y i := by
  simp [value, coord, mon, Fin.sum_univ_succ, mul_assoc, add_assoc]

theorem coord_transpose (n : Net) (i j : Fin 21) :
    coord (coord (transpose n) i) j = coord (coord n j) i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem netValue_sum (n : Net) (x y u v : ℝ) :
    netValue n x y u v = ∑ i : Fin 21, ∑ j : Fin 21,
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

theorem value_nonneg (r : Coeff21 ℝ) (h : allC (fun a : ℝ => 0 ≤ a) r)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ value r x y := by
  rcases h with ⟨h_a,h_b,h_c,h_d,h_e,h_f,h_g,h_h,h_i,h_j,h_k,h_l,h_m,h_n,h_o,h_p,h_q,h_r,h_s,h_t,h_u⟩
  unfold value
  positivity

theorem rowValue_nonneg (r : Row) (h : rowGood r)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ rowValue r x y := by
  apply value_nonneg _ _ hx hy
  simp only [allC, mapC]
  rcases h with ⟨h_a,h_b,h_c,h_d,h_e,h_f,h_g,h_h,h_i,h_j,h_k,h_l,h_m,h_n,h_o,h_p,h_q,h_r,h_s,h_t,h_u⟩
  exact ⟨by exact_mod_cast h_a, by exact_mod_cast h_b, by exact_mod_cast h_c, by exact_mod_cast h_d, by exact_mod_cast h_e, by exact_mod_cast h_f, by exact_mod_cast h_g, by exact_mod_cast h_h, by exact_mod_cast h_i, by exact_mod_cast h_j, by exact_mod_cast h_k, by exact_mod_cast h_l, by exact_mod_cast h_m, by exact_mod_cast h_n, by exact_mod_cast h_o, by exact_mod_cast h_p, by exact_mod_cast h_q, by exact_mod_cast h_r, by exact_mod_cast h_s, by exact_mod_cast h_t, by exact_mod_cast h_u⟩

def positiveOn (n : Net) : Prop :=
  ∀ x y u v : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ u → 0 ≤ v → 0 ≤ netValue n x y u v

theorem good_positive (n : Net) (h : netGood n) : positiveOn n := by
  intro x y u v hx hy hu hv
  apply value_nonneg _ _ hx hy
  rcases h with ⟨h_a,h_b,h_c,h_d,h_e,h_f,h_g,h_h,h_i,h_j,h_k,h_l,h_m,h_n,h_o,h_p,h_q,h_r,h_s,h_t,h_u⟩
  exact ⟨rowValue_nonneg _ h_a hu hv, rowValue_nonneg _ h_b hu hv, rowValue_nonneg _ h_c hu hv, rowValue_nonneg _ h_d hu hv, rowValue_nonneg _ h_e hu hv, rowValue_nonneg _ h_f hu hv, rowValue_nonneg _ h_g hu hv, rowValue_nonneg _ h_h hu hv, rowValue_nonneg _ h_i hu hv, rowValue_nonneg _ h_j hu hv, rowValue_nonneg _ h_k hu hv, rowValue_nonneg _ h_l hu hv, rowValue_nonneg _ h_m hu hv, rowValue_nonneg _ h_n hu hv, rowValue_nonneg _ h_o hu hv, rowValue_nonneg _ h_p hu hv, rowValue_nonneg _ h_q hu hv, rowValue_nonneg _ h_r hu hv, rowValue_nonneg _ h_s hu hv, rowValue_nonneg _ h_t hu hv, rowValue_nonneg _ h_u hu hv⟩

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

end EllipticBernstein.Degree20
