import ModifiedCartan.CharacterOrthogonalInvariant

open scoped Classical

namespace ModifiedCartan
noncomputable section

def representationReindexSubspaces {G H V : Type*} [Monoid G] [Monoid H]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (e : G ≃* H) :
    Subrepresentation (ρ.comp e.toMonoidHom) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g := by
        obtain ⟨h, rfl⟩ := e.surjective g
        exact S.apply_mem_toSubmodule h }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g := S.apply_mem_toSubmodule (e g) }
  left_inv S := by apply Subrepresentation.toSubmodule_injective; rfl
  right_inv S := by apply Subrepresentation.toSubmodule_injective; rfl
  map_rel_iff' := Iff.rfl

theorem representation_irreducible_reindex {G H V : Type*} [Monoid G] [Monoid H]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (e : G ≃* H)
    [Representation.IsIrreducible ρ] : Representation.IsIrreducible (ρ.comp e.toMonoidHom) :=
  (representationReindexSubspaces ρ e).isSimpleOrder_iff.mpr inferInstance

theorem unitary_representation_reindex {G H V : Type*} [Group G] [Group H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : Representation ℂ H V) (e : G ≃* H) (hρ : IsUnitaryRepresentation ρ) :
    IsUnitaryRepresentation (ρ.comp e.toMonoidHom) := by
  intro g v w
  exact hρ (e g) v w

end
end ModifiedCartan


