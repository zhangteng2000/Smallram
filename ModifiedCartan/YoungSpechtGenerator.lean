import ModifiedCartan.SpechtRepresentation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def youngSpechtGenerator (μ : YoungDiagram) : YoungSpechtModule μ :=
  ⟨youngPolytabloid μ, youngPolytabloid_mem_specht μ⟩

theorem youngSpechtGenerator_ne_zero (μ : YoungDiagram) : youngSpechtGenerator μ ≠ 0 := by
  intro h
  exact youngPolytabloid_ne_zero μ (congrArg (fun v : YoungSpechtModule μ => v.val) h)

theorem youngSpechtGenerator_column (μ : YoungDiagram) (c : youngColumnSubgroup μ) :
    youngSpechtRepresentation μ c.val (youngSpechtGenerator μ) =
      youngPermutationSign μ c.val • youngSpechtGenerator μ := by
  apply Subtype.ext
  exact youngPolytabloid_column_action μ c

theorem youngSpechtIntertwiner_generator_column {V : Type*} [AddCommGroup V] [Module ℂ V]
    (μ : YoungDiagram) (ρ : Representation ℂ (Equiv.Perm (YoungBoxes μ)) V)
    (F : Representation.IntertwiningMap (youngSpechtRepresentation μ) ρ)
    (c : youngColumnSubgroup μ) :
    ρ c.val (F (youngSpechtGenerator μ)) =
      youngPermutationSign μ c.val • F (youngSpechtGenerator μ) := by
  rw [← F.isIntertwining, youngSpechtGenerator_column, map_smul]

theorem youngSpechtIntertwiner_eq_zero_of_generator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (μ : YoungDiagram) (ρ : Representation ℂ (Equiv.Perm (YoungBoxes μ)) V)
    (F : Representation.IntertwiningMap (youngSpechtRepresentation μ) ρ)
    (hF : F (youngSpechtGenerator μ) = 0) : F = 0 := by
  letI := youngSpechtRepresentation_irreducible μ
  rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
  · exact (youngSpechtGenerator_ne_zero μ (hi (hF.trans (map_zero F).symm))).elim
  · exact hz

end
end ModifiedCartan


