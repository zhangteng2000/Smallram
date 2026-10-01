import ModifiedCartan.SupportedDataRestriction

open scoped Classical

namespace ModifiedCartan
noncomputable section

abbrev AmbientFactorizationParameters {A : Type*} (θ : Equiv.Perm A) (U Z : Finset A) :=
  {p : SupportedPermutationData A × SupportedPermutationData A //
    p.1.1 ∪ p.2.1 = U ∧ p.1.1 ∩ p.2.1 = Z ∧ p.1.2.val * p.2.2.val = θ}

theorem ambientFactorization_left_subset {A : Type*} {θ : Equiv.Perm A} {U Z : Finset A}
    (p : AmbientFactorizationParameters θ U Z) : p.val.1.1 ⊆ U := by
  intro a ha
  rw [← p.property.1]
  exact Finset.mem_union_left _ ha

theorem ambientFactorization_right_subset {A : Type*} {θ : Equiv.Perm A} {U Z : Finset A}
    (p : AmbientFactorizationParameters θ U Z) : p.val.2.1 ⊆ U := by
  intro a ha
  rw [← p.property.1]
  exact Finset.mem_union_right _ ha

theorem ambientFactorization_product_supported {A : Type*} {θ : Equiv.Perm A} {U Z : Finset A}
    (p : AmbientFactorizationParameters θ U Z) : θ ∈ supportedPermutationSubgroup U := by
  rw [← p.property.2.2]
  exact (supportedPermutationSubgroup U).mul_mem
    (supportedPermutationSubgroup_mono (ambientFactorization_left_subset p) p.val.1.2.property)
    (supportedPermutationSubgroup_mono (ambientFactorization_right_subset p) p.val.2.2.property)

theorem ambientFactorization_overlap_subset {A : Type*} {θ : Equiv.Perm A} {U Z : Finset A}
    (p : AmbientFactorizationParameters θ U Z) : Z ⊆ U := by
  rw [← p.property.2.1]
  exact Finset.inter_subset_left.trans (ambientFactorization_left_subset p)

/-- Removes exactly the letters outside both designated supports. -/
def ambientFactorizationRestrictionEquiv {A : Type*} (θ : Equiv.Perm A) (U Z : Finset A)
    (hθ : θ ∈ supportedPermutationSubgroup U) (hZ : Z ⊆ U) :
    ZFactorizationParameters (supportedPermutationRestriction U θ hθ)
      (Z.subtype (fun a => a ∈ U)) ≃ AmbientFactorizationParameters θ U Z where
  toFun p := ⟨(extendSupportedPermutationData U p.val.1,
    extendSupportedPermutationData U p.val.2), by
      constructor
      · change finiteSubtypeSupportImage U p.val.1.1 ∪
          finiteSubtypeSupportImage U p.val.2.1 = U
        have h := congrArg (finiteSubtypeSupportImage U) p.property.1
        rw [finiteSubtypeSupportImage_univ] at h
        simpa only [finiteSubtypeSupportImage, Finset.map_union] using h
      · constructor
        · change finiteSubtypeSupportImage U p.val.1.1 ∩
            finiteSubtypeSupportImage U p.val.2.1 = Z
          have h := congrArg (finiteSubtypeSupportImage U) p.property.2.1
          rw [finiteSubtypeSupportImage_subtype U Z hZ] at h
          simpa only [finiteSubtypeSupportImage, Finset.map_inter] using h
        · change Equiv.Perm.ofSubtype p.val.1.2.val * Equiv.Perm.ofSubtype p.val.2.2.val = θ
          rw [← map_mul, p.property.2.2, supportedPermutationRestriction_extension]⟩
  invFun p := ⟨(restrictSupportedPermutationData U p.val.1 (ambientFactorization_left_subset p),
    restrictSupportedPermutationData U p.val.2 (ambientFactorization_right_subset p)), by
      constructor
      · ext a
        simp only [restrictSupportedPermutationData, Finset.mem_union, Finset.mem_subtype,
          Finset.mem_univ, iff_true]
        rw [← Finset.mem_union, p.property.1]
        exact a.property
      · constructor
        · ext a
          simp only [restrictSupportedPermutationData, Finset.mem_inter, Finset.mem_subtype]
          rw [← Finset.mem_inter, p.property.2.1]
        · apply Equiv.ext
          intro a
          apply Subtype.ext
          exact congrArg (fun σ : Equiv.Perm A => σ a.val) p.property.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact restrict_extendSupportedPermutationData U p.val.1
    · exact restrict_extendSupportedPermutationData U p.val.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact extend_restrictSupportedPermutationData U p.val.1 (ambientFactorization_left_subset p)
    · exact extend_restrictSupportedPermutationData U p.val.2 (ambientFactorization_right_subset p)

end
end ModifiedCartan

