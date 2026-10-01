import ModifiedCartan.YoungSpechtSubmoduleTheorem

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

/-- The ambient image of an invariant subspace inside an invariant subspace. -/
def nestedSubrepresentationImage {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (S : Subrepresentation ρ)
    (U : Subrepresentation S.toRepresentation) : Subrepresentation ρ where
  toSubmodule := U.toSubmodule.map S.toSubmodule.subtype
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨S.toRepresentation g v, U.apply_mem_toSubmodule g hv, rfl⟩

/-- Irreducibility of the polytabloid Specht representation over the complex numbers. -/
theorem youngSpechtRepresentation_irreducible (μ : YoungDiagram) :
    Representation.IsIrreducible (youngSpechtRepresentation μ) := by
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro h
    let v : YoungSpechtModule μ := ⟨youngPolytabloid μ, youngPolytabloid_mem_specht μ⟩
    have hv : v ∈ (⊤ : Subrepresentation (youngSpechtRepresentation μ)) := by trivial
    rw [← h] at hv
    change v = 0 at hv
    exact youngPolytabloid_ne_zero μ (congrArg (fun w : YoungSpechtModule μ => w.val) hv)
  · intro U
    let S := youngSpechtSubrepresentation μ
    let U' := nestedSubrepresentationImage (youngTabloidRepresentation μ) S U
    obtain hc | ho := young_specht_submodule_theorem μ U'
    · right
      apply top_unique
      intro v _
      obtain ⟨w, hw, hweq⟩ := hc v.property
      have he : w = v := Subtype.ext hweq
      exact he ▸ hw
    · left
      apply bot_unique
      intro v hv
      change v = 0
      apply Subtype.ext
      have hi : v.val ∈ U' := ⟨v, hv, rfl⟩
      have hvorth := ho hi
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      exact (S.toSubmodule.mem_orthogonal v.val).mp hvorth v.val v.property

end
end ModifiedCartan


