import Std

/-!
Counting step for a finite zero certificate. Each box lists the multiplicities
of the zeros it contains. A separate list records every other zero. These are
analytic inputs. The theorem below rules out multiple or missing zeros when
the total winding count equals the number of disjoint boxes with sign changes.
-/
namespace BracketExhaustion

def Positive (xs : List Nat) : Prop := ∀ m ∈ xs, 0 < m

def GoodBoxes : List (List Nat) → Prop
  | [] => True
  | b :: bs => b ≠ [] ∧ Positive b ∧ GoodBoxes bs

def BoxMass : List (List Nat) → Nat
  | [] => 0
  | b :: bs => b.sum + BoxMass bs

def AllSimple : List (List Nat) → Prop
  | [] => True
  | b :: bs => b = [1] ∧ AllSimple bs

theorem positive_length_le_sum (xs : List Nat) (hp : Positive xs) :
    xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hp a (List.mem_cons_self ..)
    have htail : Positive xs := fun m hm => hp m (List.mem_cons_of_mem _ hm)
    have h := ih htail
    simp only [List.length_cons, List.sum_cons]
    omega

theorem nonempty_positive_sum {b : List Nat} (hne : b ≠ []) (hp : Positive b) :
    1 ≤ b.sum := by
  have hlen := positive_length_le_sum b hp
  cases b with
  | nil => exact False.elim (hne rfl)
  | cons a b => simp only [List.length_cons] at hlen; omega

theorem sum_one_singleton {b : List Nat} (hne : b ≠ []) (hp : Positive b)
    (hs : b.sum = 1) : b = [1] := by
  have hlen := positive_length_le_sum b hp
  cases b with
  | nil => exact False.elim (hne rfl)
  | cons a b =>
    simp only [List.length_cons] at hlen
    have h0 : b.length = 0 := by omega
    have he := List.eq_nil_of_length_eq_zero h0
    subst b
    simp at hs
    simp [hs]

theorem box_count_le_mass (bs : List (List Nat)) (hg : GoodBoxes bs) :
    bs.length ≤ BoxMass bs := by
  induction bs with
  | nil => simp [BoxMass]
  | cons b bs ih =>
    obtain ⟨hb, hp, ht⟩ := hg
    have h := ih ht
    have h1 := nonempty_positive_sum hb hp
    simp only [List.length_cons, BoxMass]
    omega

theorem equal_box_mass_simple (bs : List (List Nat)) (hg : GoodBoxes bs)
    (he : BoxMass bs = bs.length) : AllSimple bs := by
  induction bs with
  | nil => trivial
  | cons b bs ih =>
    obtain ⟨hb,hp,ht⟩ := hg
    simp only [List.length_cons, BoxMass] at he
    have h1 := nonempty_positive_sum hb hp
    have htail := box_count_le_mass bs ht
    exact ⟨sum_one_singleton hb hp (by omega), ih ht (by omega)⟩

theorem exhaust (boxes : List (List Nat)) (outside : List Nat)
    (hboxes : GoodBoxes boxes) (hout : Positive outside)
    (winding_eq : BoxMass boxes + outside.sum = boxes.length) :
    AllSimple boxes ∧ outside = [] := by
  have hmin := box_count_le_mass boxes hboxes
  have hlen := positive_length_le_sum outside hout
  exact ⟨equal_box_mass_simple boxes hboxes (by omega),
         List.eq_nil_of_length_eq_zero (by omega)⟩

/-- An ordered integer grid certificate. A common endpoint is allowed. -/
def GridOK (prev : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (lo,hi) :: rest => decide (prev ≤ lo) && decide (lo < hi) && GridOK hi rest

/-- Every later left endpoint is at or beyond the preceding certified endpoint. -/
theorem GridOK.lower {prev : Nat} {boxes : List (Nat × Nat)}
    (h : GridOK prev boxes = true) :
    ∀ b ∈ boxes, prev ≤ b.1 := by
  induction boxes generalizing prev with
  | nil => simp
  | cons b boxes ih =>
    obtain ⟨lo, hi⟩ := b
    simp [GridOK] at h
    intro u hu
    rcases List.mem_cons.mp hu with he | ht
    · subst u; exact h.1.1
    · have hs := ih h.2 u ht
      omega

/-- Two distinct listed open grid intervals have no common interior point:
the lemma gives the ordering for the first interval against every later one. -/
theorem separated {prev lo hi : Nat} {rest : List (Nat × Nat)}
    (h : GridOK prev ((lo,hi)::rest) = true) :
    ∀ b ∈ rest, hi ≤ b.1 := by
  simp [GridOK] at h
  exact GridOK.lower h.2


/-- Literal indices of the level-144, height-32 tilted certificate. -/
def level144Height32 : List (Nat × Nat) :=
  [(15,16), (32,33), (42,43), (53,54), (64,65),
   (69,70), (82,83), (89,90), (96,97), (105,106),
   (113,114), (120,121), (127,128), (137,138), (141,142),
   (149,150), (156,157), (165,166), (170,171), (175,176),
   (186,187), (190,191), (197,198), (203,204), (210,211),
   (218,219), (223,224), (227,228), (237,238), (242,243),
   (248,249), (253,254)]

/-- The last integer inequality uses the classical bound pi < 22/7 in
the application: one grid unit is 2*pi*81/4096. -/
theorem level144_grid :
    GridOK 0 level144Height32 = true ∧
    level144Height32.length = 32 ∧
    level144Height32.all (fun b => decide (b.2 * 2 * 22 * 81 < 7 * 4096 * 32)) = true := by
  decide

end BracketExhaustion

#print axioms BracketExhaustion.exhaust
#print axioms BracketExhaustion.separated

#print axioms BracketExhaustion.level144_grid
