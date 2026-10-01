import ModifiedCartan.ZFactorDirectSum
import ModifiedCartan.FixedColoringDirectSum
import ModifiedCartan.SignedBlockInflation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem zConstructedRightFactor_fixedColoringSum {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hsub : D ⊆ zStripComplement θ Z) (hD : ∀ x, θ x ∈ D ↔ x ∈ D)
    (σ : Equiv.Perm Z) (x : B → R) :
    permutationFixedColoringSum
      (supportedPermutationRestriction (zPrefixSet θ Z κ ∪ D)
        (zConstructedRightFactor θ Z κ D hD σ) (zConstructedRightFactor_support θ Z κ D hD σ)) x =
    permutationFixedColoringSum (blockInflation (fun a => (κ a).val) σ) x *
      permutationFixedColoringSum (θ.subtypePerm hD) x := by
  rw [zConstructedRightFactor_restriction_eq θ Z κ D hsub hD σ,
    permutationFixedColoringSum_conjugate, permutationFixedColoringSum_sumCongr]

theorem signed_blockInflation_fixedColoring_sum {A B R : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [CommRing R] [Algebra ℂ R]
    (κ : A → ℕ) (x : B → R) :
    (∑ σ : Equiv.Perm A, ((Equiv.Perm.sign (blockInflation κ σ) : ℤ) : ℂ) •
      permutationFixedColoringSum (blockInflation κ σ) x) =
    (-1 : ℂ) ^ (∑ a, κ a) •
      ∑ f : A → B, if Function.Injective f then ∏ a, x (f a) ^ (κ a + 1) else 0 := by
  simp_rw [permutationFixedColoringSum_cycles]
  exact signed_blockInflation_cycle_power_sum κ x

end
end ModifiedCartan

