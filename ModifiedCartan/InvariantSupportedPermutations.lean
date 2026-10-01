import ModifiedCartan.SupportedPermutations

open scoped Classical

namespace ModifiedCartan
noncomputable section

def invariantSupportedPermutation {A : Type*} (θ : Equiv.Perm A) (D : Finset A)
    (hD : ∀ x, θ x ∈ D ↔ x ∈ D) : Equiv.Perm A :=
  Equiv.Perm.ofSubtype (θ.subtypePerm hD)

theorem invariantSupportedPermutation_mem {A : Type*} (θ : Equiv.Perm A) (D : Finset A)
    (hD : ∀ x, θ x ∈ D ↔ x ∈ D) :
    invariantSupportedPermutation θ D hD ∈ supportedPermutationSubgroup D := by
  intro x hx
  exact Equiv.Perm.ofSubtype_apply_of_not_mem (θ.subtypePerm hD) hx

theorem invariantSupportedPermutation_apply {A : Type*} (θ : Equiv.Perm A) (D : Finset A)
    (hD : ∀ x, θ x ∈ D ↔ x ∈ D) (x : A) (hx : x ∈ D) :
    invariantSupportedPermutation θ D hD x = θ x :=
  Equiv.Perm.ofSubtype_subtypePerm_of_mem (g := θ) hD hx

end
end ModifiedCartan

