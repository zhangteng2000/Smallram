import ModifiedCartan.SpechtPredecessorsFromCharacters
import ModifiedCartan.SpechtShapeReconstruction

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

universe u

/-- Actual Specht characters of distinct Young diagrams are distinct.
The separation input in the pairing helpers is discharged by this strong induction. -/
theorem spechtCharacterOn_shape_injective {A : Type u} [Fintype A] [DecidableEq A]
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ) (hν : Fintype.card A = partitionSize ν)
    (he : spechtCharacterOn μ hμ = spechtCharacterOn ν hν) : μ = ν := by
  suffices hmain : ∀ n : ℕ, ∀ (B : Type u) [Fintype B] [DecidableEq B],
      Fintype.card B = n → ∀ (ξ ζ : YoungDiagram) (hξ : Fintype.card B = partitionSize ξ)
      (hζ : Fintype.card B = partitionSize ζ),
      spechtCharacterOn ξ hξ = spechtCharacterOn ζ hζ → ξ = ζ from
    hmain (Fintype.card A) A rfl μ ν hμ hν he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B _ _ hn ξ ζ hξ hζ heq
    by_cases hz : n = 0
    · have hξz : partitionSize ξ = 0 := hξ.symm.trans (hn.trans hz)
      have hζz : partitionSize ζ = 0 := hζ.symm.trans (hn.trans hz)
      exact (partition_eq_bot_of_size_zero ξ hξz).trans (partition_eq_bot_of_size_zero ζ hζz).symm
    have hpos : 0 < Fintype.card B := by omega
    obtain ⟨a⟩ := Fintype.card_pos_iff.mp hpos
    have hsmall : Fintype.card (↥(Finset.univ.erase a)) < n := by
      rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hn]
      omega
    have hsep := ih _ hsmall (↥(Finset.univ.erase a)) rfl
    exact partition_eq_of_predecessors_and_character ξ ζ hξ hζ
      (youngPredecessors_eq_of_character_eq a hsep ξ ζ hξ hζ heq) heq

theorem spechtRepresentationOn_equiv_shape {A : Type*} [Fintype A] [DecidableEq A]
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ) (hν : Fintype.card A = partitionSize ν)
    (e : (spechtRepresentationOn μ hμ).Equiv (spechtRepresentationOn ν hν)) : μ = ν :=
  spechtCharacterOn_shape_injective μ ν hμ hν (Representation.char_iso e)

/-- The unconditional orthogonality formula for the constructed Specht characters. -/
theorem spechtCharacterOn_orthogonality {A : Type*} [Fintype A] [DecidableEq A]
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ) (hν : Fintype.card A = partitionSize ν) :
    (Nat.card (Equiv.Perm A) : ℂ)⁻¹ *
      ∑ g : Equiv.Perm A, spechtCharacterOn μ hμ g * spechtCharacterOn ν hν g⁻¹ =
      if μ = ν then 1 else 0 :=
  spechtCharacterOn_pairing_of_separation (fun ξ ζ hξ hζ he =>
    spechtCharacterOn_shape_injective ξ ζ hξ hζ he) μ ν hμ hν

end
end ModifiedCartan


