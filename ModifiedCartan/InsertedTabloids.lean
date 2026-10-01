import ModifiedCartan.RemovedPermutations

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngRemoval_row_relation_iff (μ : YoungDiagram) (b : YoungCorner μ)
    (g h : Equiv.Perm (YoungBoxes (removePartitionBox μ b))) :
    (youngRemovalPermutationEquiv μ b g).val⁻¹ * (youngRemovalPermutationEquiv μ b h).val ∈
      youngRowSubgroup μ ↔ g⁻¹ * h ∈ youngRowSubgroup (removePartitionBox μ b) := by
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using
    youngRemovalPermutation_row_iff μ b (g⁻¹ * h)

/-- Insert a fixed letter in its corner row in an actual tabloid. -/
def youngTabloidInsert (μ : YoungDiagram) (b : YoungCorner μ) :
    YoungTabloid (removePartitionBox μ b) → YoungTabloid μ :=
  Quotient.lift (fun g => youngTabloid μ (youngRemovalPermutationEquiv μ b g).val) (by
    intro g h hgh
    apply (young_tabloid_eq_iff μ _ _).mpr
    exact (youngRemoval_row_relation_iff μ b g h).mpr (QuotientGroup.leftRel_apply.mp hgh))

@[simp] theorem youngTabloidInsert_mk (μ : YoungDiagram) (b : YoungCorner μ)
    (g : Equiv.Perm (YoungBoxes (removePartitionBox μ b))) :
    youngTabloidInsert μ b (youngTabloid (removePartitionBox μ b) g) =
      youngTabloid μ (youngRemovalPermutationEquiv μ b g).val := rfl

theorem youngTabloidInsert_injective (μ : YoungDiagram) (b : YoungCorner μ) :
    Function.Injective (youngTabloidInsert μ b) := by
  intro t u he
  induction t using Quotient.inductionOn with | h g =>
    induction u using Quotient.inductionOn with | h h =>
      apply (young_tabloid_eq_iff (removePartitionBox μ b) g h).mpr
      apply (youngRemoval_row_relation_iff μ b g h).mp
      exact (young_tabloid_eq_iff μ _ _).mp he

theorem youngTabloidInsert_action (μ : YoungDiagram) (b : YoungCorner μ)
    (g : Equiv.Perm (YoungBoxes (removePartitionBox μ b)))
    (t : YoungTabloid (removePartitionBox μ b)) :
    youngTabloidInsert μ b (g • t) =
      (youngRemovalPermutationEquiv μ b g).val • youngTabloidInsert μ b t := by
  induction t using Quotient.inductionOn with | h h =>
    change youngTabloid μ (youngRemovalPermutationEquiv μ b (g * h)).val = _
    rw [map_mul, Subgroup.coe_mul]
    rfl

theorem youngTabloidInsert_row (μ : YoungDiagram) (b : YoungCorner μ)
    (t : YoungTabloid (removePartitionBox μ b)) :
    youngTabloidRows μ (youngTabloidInsert μ b t) b.val = b.val.val.1 := by
  induction t using Quotient.inductionOn with | h g =>
    change ((youngRemovalPermutationEquiv μ b g).val⁻¹ b.val).val.1 = b.val.val.1
    have hg : (youngRemovalPermutationEquiv μ b g).val⁻¹ b.val = b.val :=
      youngLetterStabilizer_fixes μ b.val (youngRemovalPermutationEquiv μ b g)⁻¹
    rw [hg]

theorem youngTabloidInsert_surjective_row (μ : YoungDiagram) (b : YoungCorner μ)
    (t : YoungTabloid μ) (ht : youngTabloidRows μ t b.val = b.val.val.1) :
    ∃ s : YoungTabloid (removePartitionBox μ b), youngTabloidInsert μ b s = t := by
  induction t using Quotient.inductionOn with | h g =>
    change (g⁻¹ b.val).val.1 = b.val.val.1 at ht
    let d : Equiv.Perm (YoungBoxes μ) := Equiv.swap (g⁻¹ b.val) b.val
    have hd : d ∈ youngRowSubgroup μ :=
      permutationFiberSubgroup_swap_mem (fun a : YoungBoxes μ => a.val.1) ht
    have hfix : (g * d) b.val = b.val := by
      change g (Equiv.swap (g⁻¹ b.val) b.val b.val) = b.val
      rw [Equiv.swap_apply_right]
      exact g.apply_symm_apply b.val
    let h : youngLetterStabilizer μ b.val := ⟨g * d, by
      intro a ha
      have hab : a = b.val := by simpa using ha
      subst a
      exact hfix⟩
    refine ⟨youngTabloid (removePartitionBox μ b) ((youngRemovalPermutationEquiv μ b).symm h), ?_⟩
    rw [youngTabloidInsert_mk, MulEquiv.apply_symm_apply]
    symm
    apply (young_tabloid_eq_iff μ g (g * d)).mpr
    rw [inv_mul_cancel_left]
    exact hd

def youngTabloidInsertEquiv (μ : YoungDiagram) (b : YoungCorner μ) :
    YoungTabloid (removePartitionBox μ b) ≃
      {t : YoungTabloid μ // youngTabloidRows μ t b.val = b.val.val.1} :=
  Equiv.ofBijective (fun t => ⟨youngTabloidInsert μ b t, youngTabloidInsert_row μ b t⟩)
    ⟨fun t u h => youngTabloidInsert_injective μ b (congrArg Subtype.val h), by
      intro t
      obtain ⟨s, hs⟩ := youngTabloidInsert_surjective_row μ b t.val t.property
      exact ⟨s, Subtype.ext hs⟩⟩

end
end ModifiedCartan


