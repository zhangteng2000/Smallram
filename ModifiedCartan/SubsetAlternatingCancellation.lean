import ModifiedCartan.SupportedPermutations
import ModifiedCartan.SubgroupAlternation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem youngSubsetAlternatingOperator_kills_collision (μ : YoungDiagram)
    (S : Finset (YoungBoxes μ)) (t : YoungTabloid μ) (a b : YoungBoxes μ)
    (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b)
    (hr : youngTabloidRows μ t a = youngTabloidRows μ t b) :
    youngSubgroupAlternatingOperator μ (supportedPermutationSubgroup S)
      (MonoidAlgebra.single t 1) = 0 := by
  let d : supportedPermutationSubgroup S :=
    ⟨Equiv.swap a b, swap_mem_supportedPermutationSubgroup S ha hb⟩
  apply youngSubgroupAlternatingOperator_zero_of_odd_stabilizer μ _ d
  · change Representation.ofMulAction ℂ (Equiv.Perm (YoungBoxes μ)) (YoungTabloid μ)
      (Equiv.swap a b) (MonoidAlgebra.single t 1) = _
    rw [Representation.ofMulAction_single, young_swap_fixes_tabloid μ t a b hr]
  · exact youngPermutationSign_swap μ a b hne

/-- More letters than available rows force a repeated row and hence cancellation. -/
theorem youngSubsetAlternatingOperator_zero_of_row_bound (μ : YoungDiagram)
    (S : Finset (YoungBoxes μ)) (t : YoungTabloid μ) (r : ℕ)
    (hrow : ∀ a ∈ S, youngTabloidRows μ t a < r) (hcard : r < S.card) :
    youngSubgroupAlternatingOperator μ (supportedPermutationSubgroup S)
      (MonoidAlgebra.single t 1) = 0 := by
  let f : S → Fin r := fun a => ⟨youngTabloidRows μ t a.val, hrow a.val a.property⟩
  have hf : ¬ Function.Injective f := by
    intro hi
    have hc := Fintype.card_le_of_injective f hi
    rw [Fintype.card_coe, Fintype.card_fin] at hc
    omega
  change ¬ ∀ a b : S, f a = f b → a = b at hf
  push Not at hf
  obtain ⟨a, b, hab, hne⟩ := hf
  apply youngSubsetAlternatingOperator_kills_collision μ S t a.val b.val a.property b.property
  · intro he
    exact hne (Subtype.ext he)
  · exact congrArg Fin.val hab

end
end ModifiedCartan


