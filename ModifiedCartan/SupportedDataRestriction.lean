import ModifiedCartan.FiniteSubtypeSupports
import ModifiedCartan.ZFactorizationParameters

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem supportedPermutationData_ext {A : Type*} {p q : SupportedPermutationData A}
    (hX : p.1 = q.1) (hπ : p.2.val = q.2.val) : p = q := by
  rcases p with ⟨X, π, hπX⟩
  rcases q with ⟨Y, σ, hσY⟩
  dsimp at hX hπ
  subst Y
  subst σ
  rfl

theorem supportedPermutationSubgroup_mono {A : Type*} {X U : Finset A} (h : X ⊆ U) :
    supportedPermutationSubgroup X ≤ supportedPermutationSubgroup U := by
  intro π hπ a ha
  exact hπ a (fun hx => ha (h hx))

def extendSupportedPermutationData {A : Type*} (U : Finset A)
    (p : SupportedPermutationData U) : SupportedPermutationData A :=
  ⟨finiteSubtypeSupportImage U p.1, Equiv.Perm.ofSubtype p.2.val, by
    intro a ha
    by_cases hu : a ∈ U
    · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hu]
      have hn : (⟨a, hu⟩ : U) ∉ p.1 := fun h =>
        ha ((finiteSubtypeSupportImage_mem U p.1 ⟨a, hu⟩).mpr h)
      exact congrArg Subtype.val (p.2.property ⟨a, hu⟩ hn)
    · exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hu⟩

def restrictSupportedPermutationData {A : Type*} (U : Finset A)
    (p : SupportedPermutationData A) (hp : p.1 ⊆ U) : SupportedPermutationData U :=
  ⟨p.1.subtype (fun a => a ∈ U),
    supportedPermutationRestriction U p.2.val (supportedPermutationSubgroup_mono hp p.2.property), by
      intro a ha
      apply Subtype.ext
      exact p.2.property a.val (fun h => ha (Finset.mem_subtype.mpr h))⟩

theorem restrict_extendSupportedPermutationData {A : Type*} (U : Finset A)
    (p : SupportedPermutationData U) :
    restrictSupportedPermutationData U (extendSupportedPermutationData U p)
      (finiteSubtypeSupportImage_subset U p.1) = p := by
  apply supportedPermutationData_ext
  · exact finiteSubtypeSupportImage_preimage U p.1
  · apply Equiv.ext
    intro a
    apply Subtype.ext
    exact Equiv.Perm.ofSubtype_apply_coe p.2.val a

theorem extend_restrictSupportedPermutationData {A : Type*} (U : Finset A)
    (p : SupportedPermutationData A) (hp : p.1 ⊆ U) :
    extendSupportedPermutationData U (restrictSupportedPermutationData U p hp) = p := by
  apply supportedPermutationData_ext
  · exact finiteSubtypeSupportImage_subtype U p.1 hp
  · exact supportedPermutationRestriction_extension U p.2.val
      (supportedPermutationSubgroup_mono hp p.2.property)

/-- Supported permutation data on a finite subalphabet are exactly ambient
supported data whose designated support lies in that subalphabet. -/
def supportedPermutationDataSubtypeEquiv {A : Type*} (U : Finset A) :
    SupportedPermutationData U ≃ {p : SupportedPermutationData A // p.1 ⊆ U} where
  toFun p := ⟨extendSupportedPermutationData U p, finiteSubtypeSupportImage_subset U p.1⟩
  invFun p := restrictSupportedPermutationData U p.val p.property
  left_inv := restrict_extendSupportedPermutationData U
  right_inv p := Subtype.ext (extend_restrictSupportedPermutationData U p.val p.property)

end
end ModifiedCartan

