import ModifiedCartan.CharacterProjectorFixed

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W]

def subrepresentationInclusion (σ : Representation ℂ G W) (S : Subrepresentation σ) :
    Representation.IntertwiningMap S.toRepresentation σ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' g := by apply LinearMap.ext; intro v; rfl

set_option backward.isDefEq.respectTransparency false in
def intertwinerToRange (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (f : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap ρ (Representation.IntertwiningMap.range ρ σ f).toRepresentation where
  toLinearMap := f.toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining ρ σ f g v

set_option backward.isDefEq.respectTransparency false in
theorem nonempty_equiv_intertwiner_range (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (f : Representation.IntertwiningMap ρ σ)
    (hf : Function.Injective f) :
    Nonempty (Representation.Equiv ρ
      (Representation.IntertwiningMap.range ρ σ f).toRepresentation) := by
  apply Nonempty.intro
  apply (intertwinerToRange ρ σ f).ofBijective
  constructor
  · intro v w h
    apply hf
    exact congrArg (fun z : (Representation.IntertwiningMap.range ρ σ f).toSubmodule => z.val) h
  · rintro ⟨w, ⟨v, hv⟩⟩
    exact ⟨v, Subtype.ext hv⟩

/-- Literal sum of all invariant subspaces isomorphic to the fixed representation. -/
def irreducibleCopiesSubmodule (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Submodule ℂ W :=
  ⨆ S : Subrepresentation σ, ⨆ (_ : Nonempty (Representation.Equiv ρ S.toRepresentation)),
    S.toSubmodule

set_option backward.isDefEq.respectTransparency false in
theorem representationIsotypic_eq_sum_copies (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] :
    representationIsotypicSubmodule ρ σ = irreducibleCopiesSubmodule ρ σ := by
  apply le_antisymm
  · apply iSup_le
    intro f
    rcases Representation.IsIrreducible.injective_or_eq_zero f with hf | hf
    · exact le_iSup_of_le (Representation.IntertwiningMap.range ρ σ f)
        (le_iSup_of_le (nonempty_equiv_intertwiner_range ρ σ f hf) le_rfl)
    · subst f
      simp [Representation.IntertwiningMap.zero_toLinearMap]
  · apply iSup_le
    intro S
    apply iSup_le
    rintro ⟨e⟩ v hv
    have hm := intertwiner_apply_mem_isotypic ρ σ
      ((subrepresentationInclusion σ S).comp e.toIntertwiningMap) (e.symm ⟨v, hv⟩)
    change (e (e.symm ⟨v, hv⟩)).val ∈ representationIsotypicSubmodule ρ σ at hm
    simpa only [Representation.Equiv.apply_symm_apply] using hm

end
end ModifiedCartan


