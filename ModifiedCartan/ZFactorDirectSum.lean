import ModifiedCartan.ZSupportCoordinates
import ModifiedCartan.SupportedPermutationRestrictions

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem zConstructedRightFactor_split_apply {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D)
    (σ : Equiv.Perm Z) (p : (Σ a : Z, Fin ((κ a).val + 1)) ⊕ D) :
    zConstructedRightFactor θ Z κ D hD σ (zSupportSplitEquiv θ Z κ D hsub p).val =
      (zSupportSplitEquiv θ Z κ D hsub
        (Equiv.sumCongr (blockInflation (fun a => (κ a).val) σ) (θ.subtypePerm hD) p)).val := by
  cases p with
  | inl p =>
    change zConstructedRightFactor θ Z κ D hD σ (zPrefixEmbedding θ Z κ p) =
      zPrefixEmbedding θ Z κ (blockInflation (fun a => (κ a).val) σ p)
    rw [zConstructedRightFactor_apply_prefix θ Z κ D hsub hD σ _
      (Finset.mem_map.mpr ⟨p, Finset.mem_univ p, rfl⟩)]
    exact zPrefixPermutation_apply_embedding θ Z κ σ p
  | inr d =>
    change zConstructedRightFactor θ Z κ D hD σ d.val = θ d.val
    exact zConstructedRightFactor_apply_complement θ Z κ D hsub hD σ d.val d.property

theorem zConstructedRightFactor_restriction_eq {A : Type*} [Fintype A]
    (θ : Equiv.Perm A) (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D) (σ : Equiv.Perm Z) :
    supportedPermutationRestriction (zPrefixSet θ Z κ ∪ D) (zConstructedRightFactor θ Z κ D hD σ)
      (zConstructedRightFactor_support θ Z κ D hD σ) =
    (zSupportSplitEquiv θ Z κ D hsub).permCongr
      (Equiv.sumCongr (blockInflation (fun a => (κ a).val) σ) (θ.subtypePerm hD)) := by
  apply Equiv.ext
  intro x
  obtain ⟨p, rfl⟩ := (zSupportSplitEquiv θ Z κ D hsub).surjective x
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  exact zConstructedRightFactor_split_apply θ Z κ D hsub hD σ p

end
end ModifiedCartan

