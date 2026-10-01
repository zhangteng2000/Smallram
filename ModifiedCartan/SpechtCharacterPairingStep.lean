import ModifiedCartan.SpechtFiniteAlphabetRepresentation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Induction helper: a proved character-separation statement gives the exact pairing formula. -/
theorem spechtCharacterOn_pairing_of_separation {A : Type*} [Fintype A] [DecidableEq A]
    (hsep : ∀ (ξ ζ : YoungDiagram) (hξ : Fintype.card A = partitionSize ξ)
      (hζ : Fintype.card A = partitionSize ζ),
      spechtCharacterOn ξ hξ = spechtCharacterOn ζ hζ → ξ = ζ)
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ) (hν : Fintype.card A = partitionSize ν) :
    (Nat.card (Equiv.Perm A) : ℂ)⁻¹ *
      ∑ g : Equiv.Perm A, spechtCharacterOn μ hμ g * spechtCharacterOn ν hν g⁻¹ =
      if μ = ν then 1 else 0 := by
  have hG : (Nat.card (Equiv.Perm A) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_ne_zero (α := Equiv.Perm A))
  letI : Invertible (Nat.card (Equiv.Perm A) : ℂ) := invertibleOfNonzero hG
  letI := spechtRepresentationOn_irreducible μ hμ
  letI := spechtRepresentationOn_irreducible ν hν
  have ho := Representation.char_orthonormal (spechtRepresentationOn μ hμ) (spechtRepresentationOn ν hν)
  change (Nat.card (Equiv.Perm A) : ℂ)⁻¹ *
    ∑ g : Equiv.Perm A, spechtCharacterOn μ hμ g * spechtCharacterOn ν hν g⁻¹ = _ at ho
  by_cases he : μ = ν
  · subst ν
    have hi : Nonempty ((spechtRepresentationOn μ hν).Equiv (spechtRepresentationOn μ hμ)) :=
      ⟨Representation.Equiv.refl _⟩
    simpa [hi] using ho
  · have hi : ¬ Nonempty ((spechtRepresentationOn ν hν).Equiv (spechtRepresentationOn μ hμ)) := by
      rintro ⟨e⟩
      apply he
      exact (hsep ν μ hν hμ (Representation.char_iso e)).symm
    simpa only [ite_eq_right hi, ite_eq_right he, Nat.cast_zero] using ho

theorem sum_spechtCharacterOn_pairing_of_separation {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I]
    (hsep : ∀ (ξ ζ : YoungDiagram) (hξ : Fintype.card A = partitionSize ξ)
      (hζ : Fintype.card A = partitionSize ζ),
      spechtCharacterOn ξ hξ = spechtCharacterOn ζ hζ → ξ = ζ)
    (shapes : I → YoungDiagram) (hs : ∀ i, Fintype.card A = partitionSize (shapes i))
    (ν : YoungDiagram) (hν : Fintype.card A = partitionSize ν) :
    (Nat.card (Equiv.Perm A) : ℂ)⁻¹ * ∑ g : Equiv.Perm A,
      (∑ i : I, spechtCharacterOn (shapes i) (hs i) g) * spechtCharacterOn ν hν g⁻¹ =
      ∑ i : I, if shapes i = ν then (1 : ℂ) else 0 := by
  calc
    _ = ∑ i : I, (Nat.card (Equiv.Perm A) : ℂ)⁻¹ * ∑ g : Equiv.Perm A,
        spechtCharacterOn (shapes i) (hs i) g * spechtCharacterOn ν hν g⁻¹ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm, Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact spechtCharacterOn_pairing_of_separation hsep (shapes i) ν (hs i) hν

end
end ModifiedCartan


