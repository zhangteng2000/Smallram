import ModifiedCartan.ZFactorPowerSums
import ModifiedCartan.ZFactorSign
import ModifiedCartan.RightZFactorBijection

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem zConstructedRightFactor_signed_coloring {A B R : Type*} [Fintype A] [Fintype B]
    [CommRing R] [Algebra ℂ R] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D)
    (σ : Equiv.Perm Z) (x : B → R) :
    ((Equiv.Perm.sign (zConstructedRightFactor θ Z κ D hD σ) : ℤ) : ℂ) •
      permutationFixedColoringSum
        (supportedPermutationRestriction (zPrefixSet θ Z κ ∪ D)
          (zConstructedRightFactor θ Z κ D hD σ) (zConstructedRightFactor_support θ Z κ D hD σ)) x =
    (((Equiv.Perm.sign (θ.subtypePerm hD) : ℤ) : ℂ) •
      (((Equiv.Perm.sign (blockInflation (fun a => (κ a).val) σ) : ℤ) : ℂ) •
        permutationFixedColoringSum (blockInflation (fun a => (κ a).val) σ) x)) *
      permutationFixedColoringSum (θ.subtypePerm hD) x := by
  rw [zConstructedRightFactor_fixedColoringSum θ Z κ D hsub hD σ x,
    zConstructedRightFactor_sign θ Z κ D hsub hD σ, blockInflation_sign]
  simp only [Units.val_mul, Int.cast_mul, Algebra.smul_def, map_mul]
  ring

/-- Actual signed sum over all right Z-factors with a fixed support. The free
strip part is exactly the scaled monomial expression, with its derived sign.
KP source Section 4.1.3; auxiliary to LaTeX `lem:KP-correspondence`. -/
theorem rightZFactor_signed_coloring_sum {A B R : Type*} [Fintype A] [Fintype B]
    [CommRing R] [Algebra ℂ R] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D) (x : B → R) :
    (∑ π : {π : Equiv.Perm A // IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) π},
      ((Equiv.Perm.sign π.val : ℤ) : ℂ) • permutationFixedColoringSum
        (supportedPermutationRestriction (zPrefixSet θ Z κ ∪ D) π.val
          ((isRightZFactor_iff θ Z _ π.val).mp π.property).2.1) x) =
    (((Equiv.Perm.sign (θ.subtypePerm hD) : ℤ) : ℂ) •
      ((-1 : ℂ) ^ (∑ a : Z, (κ a).val) •
        ∑ f : Z → B, if Function.Injective f then ∏ a : Z, x (f a) ^ ((κ a).val + 1) else 0)) *
      permutationFixedColoringSum (θ.subtypePerm hD) x := by
  rw [← Equiv.sum_comp (rightZFactorEquiv θ Z κ D hsub hD)
    (fun π => ((Equiv.Perm.sign π.val : ℤ) : ℂ) • permutationFixedColoringSum
      (supportedPermutationRestriction (zPrefixSet θ Z κ ∪ D) π.val
        ((isRightZFactor_iff θ Z _ π.val).mp π.property).2.1) x)]
  calc
    _ = ∑ σ : Equiv.Perm Z,
        (((Equiv.Perm.sign (θ.subtypePerm hD) : ℤ) : ℂ) •
          (((Equiv.Perm.sign (blockInflation (fun a => (κ a).val) σ) : ℤ) : ℂ) •
            permutationFixedColoringSum (blockInflation (fun a => (κ a).val) σ) x)) *
          permutationFixedColoringSum (θ.subtypePerm hD) x := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact zConstructedRightFactor_signed_coloring θ Z κ D hsub hD σ x
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.smul_sum,
        signed_blockInflation_fixedColoring_sum (fun a => (κ a).val) x]

end
end ModifiedCartan

