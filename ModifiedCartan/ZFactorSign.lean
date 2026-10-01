import ModifiedCartan.ZFactorDirectSum
import ModifiedCartan.SigmaPermutationSign

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem zConstructedRightFactor_sign {A : Type*} [Fintype A]
    (θ : Equiv.Perm A) (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D) (σ : Equiv.Perm Z) :
    Equiv.Perm.sign (zConstructedRightFactor θ Z κ D hD σ) =
      (Equiv.Perm.sign σ * (-1) ^ (∑ a : Z, (κ a).val)) * Equiv.Perm.sign (θ.subtypePerm hD) := by
  rw [← supportedPermutationRestriction_sign (zPrefixSet θ Z κ ∪ D) _
    (zConstructedRightFactor_support θ Z κ D hD σ),
    zConstructedRightFactor_restriction_eq θ Z κ D hsub hD σ,
    Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
    blockInflation_sign]

end
end ModifiedCartan

