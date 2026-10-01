import ModifiedCartan.SpechtInductionPairing
import ModifiedCartan.SpechtClassExpansion

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The one-box induction identity used in LaTeX `eq:KP-translation`, for
the actual partition-indexed Specht characters. -/
theorem inducedSpechtCharacter_eq_sum_covers {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (hμ : Fintype.card A = partitionSize μ + 1) (g : Equiv.Perm A) :
    inducedSpechtCharacter μ hμ g =
      ∑ ν : SizedYoungDiagram (Fintype.card A),
        if PartitionCovers ν.val μ then spechtCharacterOn ν.val ν.property.symm g else 0 := by
  rw [specht_class_function_expansion _ (inducedSpechtCharacter_conjugationInvariant μ hμ)]
  apply Finset.sum_congr rfl
  intro ν _
  change ((Nat.card (Equiv.Perm A) : ℂ)⁻¹ * ∑ h : Equiv.Perm A,
      inducedSpechtCharacter μ hμ h⁻¹ * spechtCharacterOn ν.val ν.property.symm h) *
        spechtCharacterOn ν.val ν.property.symm g = _
  rw [inducedSpechtCharacter_pairing μ ν.val hμ ν.property.symm]
  by_cases hc : PartitionCovers ν.val μ <;> simp only [hc, ite_true, ite_false, one_mul, zero_mul]

end
end ModifiedCartan


