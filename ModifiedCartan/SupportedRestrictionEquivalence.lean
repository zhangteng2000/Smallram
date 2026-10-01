import ModifiedCartan.SupportedPermutationRestrictions

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem supportedPermutationRestriction_eq_symm {A : Type*}
    (X : Finset A) (π : Equiv.Perm A) (hπ : π ∈ supportedPermutationSubgroup X) :
    supportedPermutationRestriction X π hπ = (supportedPermutationEquiv X).symm ⟨π, hπ⟩ := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  rfl

end
end ModifiedCartan

