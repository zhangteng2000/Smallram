import ModifiedCartan.CyclicSpechtCharacters
import ModifiedCartan.YoungColumnAlternation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem young_tabloid_eq_of_single_row (μ : YoungDiagram)
    (hr : ∀ a : YoungBoxes μ, a.val.1 = 0) (g h : Equiv.Perm (YoungBoxes μ)) :
    youngTabloid μ g = youngTabloid μ h := by
  apply (young_tabloid_eq_iff μ g h).mpr
  intro a
  exact (hr _).trans (hr _).symm

theorem youngPolytabloid_single_row_action (μ : YoungDiagram)
    (hr : ∀ a : YoungBoxes μ, a.val.1 = 0) (g : Equiv.Perm (YoungBoxes μ)) :
    youngTabloidRepresentation μ g (youngPolytabloid μ) = youngPolytabloid μ := by
  unfold youngPolytabloid
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [youngTabloidRepresentation_single]
  rw [young_tabloid_eq_of_single_row μ hr (g * c.val) c.val]

theorem youngSpecht_character_single_row (μ : YoungDiagram)
    (hr : ∀ a : YoungBoxes μ, a.val.1 = 0) (g : Equiv.Perm (YoungBoxes μ)) :
    (youngSpechtRepresentation μ).character g = 1 := by
  apply youngSpecht_character_of_polytabloid_scalars μ (fun _ => 1)
  intro h
  simpa only [one_smul] using youngPolytabloid_single_row_action μ hr h

theorem youngPolytabloid_single_column_action (μ : YoungDiagram)
    (hc : ∀ a : YoungBoxes μ, a.val.2 = 0) (g : Equiv.Perm (YoungBoxes μ)) :
    youngTabloidRepresentation μ g (youngPolytabloid μ) = youngPermutationSign μ g • youngPolytabloid μ := by
  have hg : g ∈ youngColumnSubgroup μ := by
    intro a
    exact (hc _).trans (hc _).symm
  exact youngPolytabloid_column_action μ ⟨g, hg⟩

theorem youngSpecht_character_single_column (μ : YoungDiagram)
    (hc : ∀ a : YoungBoxes μ, a.val.2 = 0) (g : Equiv.Perm (YoungBoxes μ)) :
    (youngSpechtRepresentation μ).character g = youngPermutationSign μ g :=
  youngSpecht_character_of_polytabloid_scalars μ (youngPermutationSign μ)
    (youngPolytabloid_single_column_action μ hc) g

end
end ModifiedCartan


