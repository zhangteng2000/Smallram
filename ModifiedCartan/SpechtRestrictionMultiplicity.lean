import ModifiedCartan.MultiplicityOneIsotypic
import ModifiedCartan.SpechtRestrictionPairing
import ModifiedCartan.SpechtFiniteAlphabetRepresentation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def subsetPermutationInclusion (I : Finset A) : Equiv.Perm I →* Equiv.Perm A :=
  (supportedPermutationSubgroup I).subtype.comp (supportedPermutationEquiv I).toMonoidHom

def eraseRestrictedSpecht (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) (a : A) :
    Representation ℂ (Equiv.Perm (↥(Finset.univ.erase a))) (YoungSpechtModule μ) :=
  (spechtRepresentationOn μ h).comp (subsetPermutationInclusion (Finset.univ.erase a))

theorem eraseRestrictedSpecht_character (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (a : A) (g : Equiv.Perm (↥(Finset.univ.erase a))) :
    (eraseRestrictedSpecht μ h a).character g =
      spechtCharacterOn μ h (fixedPointPermutationEquiv a g).val := rfl

theorem specht_restriction_isotypic_finrank (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (a : A) (b : YoungCorner μ) :
    Module.finrank ℂ (representationIsotypicSubmodule
      (spechtRepresentationOn (removePartitionBox μ b) (card_erase_eq_partition_remove μ h a b))
      (eraseRestrictedSpecht μ h a)) = Module.finrank ℂ (YoungSpechtModule (removePartitionBox μ b)) := by
  let ρ := spechtRepresentationOn (removePartitionBox μ b) (card_erase_eq_partition_remove μ h a b)
  letI := spechtRepresentationOn_irreducible (removePartitionBox μ b) (card_erase_eq_partition_remove μ h a b)
  have hcard : Fintype.card A = partitionSize (removePartitionBox μ b) + 1 :=
    h.trans (partitionSize_removePartitionBox_add_one μ b).symm
  have hp := specht_restriction_pairing (removePartitionBox μ b) μ hcard h a
  have hc : PartitionCovers μ (removePartitionBox μ b) :=
    (partitionCovers_iff_corner_removal (removePartitionBox μ b) μ).mpr ⟨b, rfl⟩
  rw [ite_eq_left hc] at hp
  have hr := isotypic_finrank_of_character_pairing ρ (eraseRestrictedSpecht μ h a) 1
    (by simpa only [ρ, spechtRepresentationOn_character, eraseRestrictedSpecht_character, Nat.cast_one] using hp)
  simpa only [mul_one] using hr

/-- The actual restriction contains one injective copy of each corner-removal
Specht module, whose image is its full isotypic subspace. -/
theorem exists_specht_restriction_embedding (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (a : A) (b : YoungCorner μ) :
    ∃ f : Representation.IntertwiningMap
        (spechtRepresentationOn (removePartitionBox μ b) (card_erase_eq_partition_remove μ h a b))
        (eraseRestrictedSpecht μ h a),
      Function.Injective f ∧ LinearMap.range f.toLinearMap = representationIsotypicSubmodule
        (spechtRepresentationOn (removePartitionBox μ b) (card_erase_eq_partition_remove μ h a b))
        (eraseRestrictedSpecht μ h a) := by
  letI := spechtRepresentationOn_irreducible (removePartitionBox μ b) (card_erase_eq_partition_remove μ h a b)
  exact exists_intertwiner_range_of_isotypic_finrank _ _ (specht_restriction_isotypic_finrank μ h a b)

end
end ModifiedCartan


