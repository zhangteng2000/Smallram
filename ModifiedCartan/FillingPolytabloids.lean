import ModifiedCartan.YoungFillings
import ModifiedCartan.SpechtRepresentation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def youngFillingPermutation (μ : YoungDiagram) (T : YoungFilling μ) :
    Equiv.Perm (YoungBoxes μ) := T.trans (youngBoxNumbering μ).symm

theorem youngFillingPermutation_surjective (μ : YoungDiagram) :
    Function.Surjective (youngFillingPermutation μ) := by
  intro g
  refine ⟨g.trans (youngBoxNumbering μ), ?_⟩
  apply Equiv.ext
  intro b
  exact (youngBoxNumbering μ).symm_apply_apply (g b)

def youngFillingPolytabloid (μ : YoungDiagram) (T : YoungFilling μ) : YoungPermutationModule μ :=
  youngTabloidRepresentation μ (youngFillingPermutation μ T) (youngPolytabloid μ)

theorem youngFillingPolytabloid_mem (μ : YoungDiagram) (T : YoungFilling μ) :
    youngFillingPolytabloid μ T ∈ youngSpechtSubrepresentation μ :=
  (youngSpechtSubrepresentation μ).apply_mem_toSubmodule _ (youngPolytabloid_mem_specht μ)

theorem youngFillingPolytabloids_span (μ : YoungDiagram) :
    Submodule.span ℂ (Set.range (youngFillingPolytabloid μ)) =
      (youngSpechtSubrepresentation μ).toSubmodule := by
  change Submodule.span ℂ (Set.range (youngFillingPolytabloid μ)) =
    Submodule.span ℂ (Set.range fun g => youngTabloidRepresentation μ g (youngPolytabloid μ))
  congr 1
  apply Set.ext
  intro v
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨youngFillingPermutation μ T, rfl⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨T, rfl⟩ := youngFillingPermutation_surjective μ g
    exact ⟨T, rfl⟩

theorem youngFillingPermutation_column (μ : YoungDiagram) (T : YoungFilling μ)
    (c : youngColumnSubgroup μ) :
    youngFillingPermutation μ (c.val.trans T) = youngFillingPermutation μ T * c.val := by
  apply Equiv.ext
  intro b
  rfl

/-- Permuting positions within columns only changes a polytabloid by a sign. -/
theorem youngFillingPolytabloid_column (μ : YoungDiagram) (T : YoungFilling μ)
    (c : youngColumnSubgroup μ) :
    youngFillingPolytabloid μ (c.val.trans T) =
      youngPermutationSign μ c.val • youngFillingPolytabloid μ T := by
  unfold youngFillingPolytabloid
  rw [youngFillingPermutation_column, map_mul, Module.End.mul_apply,
    youngPolytabloid_column_action, map_smul]

end
end ModifiedCartan


