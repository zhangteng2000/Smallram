import ModifiedCartan.YoungPermutationSubgroups

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- Permutations supported on a finite subset, fixing its complement pointwise. -/
def supportedPermutationSubgroup {A : Type*} (S : Finset A) : Subgroup (Equiv.Perm A) where
  carrier := {g | ∀ a, a ∉ S → g a = a}
  one_mem' := by intro a ha; rfl
  mul_mem' := by
    intro g h hg hh a ha
    change g (h a) = a
    rw [hh a ha, hg a ha]
  inv_mem' := by
    intro g hg a ha
    calc
      g⁻¹ a = g⁻¹ (g a) := congrArg (fun x => g⁻¹ x) (hg a ha).symm
      _ = a := g.symm_apply_apply a

theorem supportedPermutation_apply_mem {A : Type*} (S : Finset A)
    (g : supportedPermutationSubgroup S) {a : A} (ha : a ∈ S) : g.val a ∈ S := by
  by_contra h
  have he := g.val.injective (g.property (g.val a) h)
  apply h
  rw [he]
  exact ha

theorem swap_mem_supportedPermutationSubgroup {A : Type*} [DecidableEq A] (S : Finset A)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) : Equiv.swap a b ∈ supportedPermutationSubgroup S := by
  intro x hx
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h.symm ▸ ha)) (fun h => hx (h.symm ▸ hb))

/-- Extension by the identity identifies the subgroup with the symmetric group of the subset. -/
def supportedPermutationEquiv {A : Type*} (S : Finset A) :
    Equiv.Perm S ≃* supportedPermutationSubgroup S where
  toEquiv := Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∈ S)
  map_mul' g h := by
    apply Subtype.ext
    exact (Equiv.Perm.ofSubtype (p := fun a => a ∈ S)).map_mul g h

theorem supportedPermutation_card {A : Type*} [Fintype A] (S : Finset A) :
    Fintype.card (supportedPermutationSubgroup S) = S.card.factorial := by
  rw [← Fintype.card_congr (supportedPermutationEquiv S).toEquiv,
    Fintype.card_perm, Fintype.card_coe]

end
end ModifiedCartan


