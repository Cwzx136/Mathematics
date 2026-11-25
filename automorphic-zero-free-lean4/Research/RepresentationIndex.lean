import Mathlib.RepresentationTheory.Irreducible
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! A dimension bound underlying the signed tensor induction argument. -/

namespace RepresentationIndex

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- In an irreducible representation, the orbit of a nonzero vector spans. -/
theorem spanOrbit (ρ : Representation k G V) [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) :
    Submodule.span k (Set.range (fun g : G => ρ g v)) = ⊤ := by
  let U := Submodule.span k (Set.range (fun g : G => ρ g v))
  let W : Subrepresentation ρ := {
    toSubmodule := U
    apply_mem_toSubmodule := by
      intro g w hw
      have hle : U ≤ U.comap (ρ g) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨h, rfl⟩
        change ρ g (ρ h v) ∈ U
        exact Submodule.subset_span ⟨g * h, by simp⟩
      exact hle hw }
  have hvmem : v ∈ W := Submodule.subset_span ⟨1, by simp⟩
  rcases eq_bot_or_eq_top W with h|h
  · rw [h] at hvmem
    exact (hv ((Submodule.mem_bot k).mp hvmem)).elim
  · exact congrArg Subrepresentation.toSubmodule h

/-- An irreducible representation containing an eigenline for a subgroup has
rank at most the subgroup index. This only requires a finite coset space. -/
theorem finrank_le_index (ρ : Representation k G V) [ρ.IsIrreducible]
    (H : Subgroup G) [Finite (G ⧸ H)] {v : V} (hv : v ≠ 0)
    (eigenline : ∀ h : H, ∃ c : k, ρ h.val v = c • v) : Module.finrank k V ≤ H.index := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let b : (G ⧸ H) → V := fun t => ρ t.out v
  have generates : Submodule.span k (Set.range b) = ⊤ := by
    apply top_unique
    rw [← spanOrbit ρ hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    obtain ⟨c, hc⟩ := eigenline h⁻¹
    let t := (QuotientGroup.mk g : G ⧸ H)
    have hg : g = t.out * ((h⁻¹ : H) : G) := by simp [t, hh]
    have heq : ρ g v = c • b t := by
      calc
        ρ g v = ρ t.out (ρ ((h⁻¹ : H) : G) v) := by
          conv_lhs => rw [hg, map_mul]
          rfl
        _ = c • b t := by rw [hc, map_smul]
    change ρ g v ∈ Submodule.span k (Set.range b)
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  have bound := finrank_range_le_card (R := k) b
  change Module.finrank k (Submodule.span k (Set.range b)) ≤ _ at bound
  rw [generates, finrank_top] at bound
  rwa [Subgroup.index_eq_card, Nat.card_eq_fintype_card]

#print axioms spanOrbit
#print axioms finrank_le_index

end RepresentationIndex
