import ModifiedCartan.SupportedPermutations

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem supportedPermutation_mem_iff {A : Type*} [DecidableEq A] (S : Finset A) (π : Equiv.Perm A)
    (hπ : π ∈ supportedPermutationSubgroup S) (x : A) : π x ∈ S ↔ x ∈ S := by
  constructor
  · intro hx
    have h := supportedPermutation_apply_mem S
      ⟨π⁻¹, (supportedPermutationSubgroup S).inv_mem hπ⟩ hx
    simpa using h
  · exact supportedPermutation_apply_mem S ⟨π, hπ⟩

def supportedPermutationRestriction {A : Type*} [DecidableEq A] (S : Finset A) (π : Equiv.Perm A)
    (hπ : π ∈ supportedPermutationSubgroup S) : Equiv.Perm S :=
  π.subtypePerm (supportedPermutation_mem_iff S π hπ)

theorem supportedPermutationRestriction_apply {A : Type*} [DecidableEq A] (S : Finset A) (π : Equiv.Perm A)
    (hπ : π ∈ supportedPermutationSubgroup S) (x : S) :
    (supportedPermutationRestriction S π hπ x).val = π x.val := rfl

theorem supportedPermutationRestriction_extension {A : Type*} [DecidableEq A] (S : Finset A) (π : Equiv.Perm A)
    (hπ : π ∈ supportedPermutationSubgroup S) :
    Equiv.Perm.ofSubtype (supportedPermutationRestriction S π hπ) = π := by
  apply Equiv.Perm.ofSubtype_subtypePerm
  intro x hx
  by_contra hn
  exact hx (hπ x hn)

theorem supportedPermutationRestriction_sign {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) (π : Equiv.Perm A) (hπ : π ∈ supportedPermutationSubgroup S) :
    Equiv.Perm.sign (supportedPermutationRestriction S π hπ) = Equiv.Perm.sign π := by
  rw [← Equiv.Perm.sign_ofSubtype, supportedPermutationRestriction_extension]

end
end ModifiedCartan

