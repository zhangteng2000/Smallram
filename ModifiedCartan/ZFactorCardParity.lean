import ModifiedCartan.ZCycleSupportCard
import ModifiedCartan.CycleUnionSignTwist
import ModifiedCartan.ZFactorSets

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem zCycleSupport_card_balance {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (C : ZComplementCycleParameters θ Z) :
    (zFactorLeftSet Z (zCycleSupport θ Z κ C)).card + (∑ a : Z, (κ a).val) +
      (permutationCycleUnion θ C.val).card = Fintype.card A := by
  have hx := zFactorLeftSet_card Z (zCycleSupport θ Z κ C) (zCycleSupport_isZAdmissible θ Z κ C).1
  have hy : (zCycleSupport θ Z κ C).card =
      (∑ a : Z, ((κ a).val + 1)) + (permutationCycleUnion θ C.val).card :=
    zPrefixSet_union_card θ Z κ _ (zCycleSupport_complement_subset θ Z C)
  have hp : (∑ a : Z, ((κ a).val + 1)) = (∑ a : Z, (κ a).val) + Z.card := by
    rw [Finset.sum_add_distrib]
    simp
  rw [hy, hp] at hx
  omega

theorem parity_completion_complex (n a b d c : ℕ) (s : ℂ) (h : a + b + d = n)
    (hs : (-1 : ℂ) ^ d * s = (-1 : ℂ) ^ c) :
    (-1 : ℂ) ^ a * (-1 : ℂ) ^ b * s = (-1 : ℂ) ^ n * (-1 : ℂ) ^ c := by
  have hd : (-1 : ℂ) ^ d * (-1 : ℂ) ^ d = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul]
    simp
  rw [← h, pow_add, pow_add, ← hs]
  calc
    _ = (-1 : ℂ) ^ a * (-1 : ℂ) ^ b * ((-1 : ℂ) ^ d * (-1 : ℂ) ^ d) * s := by
      rw [hd, mul_one]
    _ = _ := by ring

theorem zCycleSupport_sign_balance {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (C : ZComplementCycleParameters θ Z) :
    (-1 : ℂ) ^ (zFactorLeftSet Z (zCycleSupport θ Z κ C)).card *
      (-1 : ℂ) ^ (∑ a : Z, (κ a).val) *
        ((Equiv.Perm.sign (θ.subtypePerm (permutationCycleUnion_invariant θ C.val)) : ℤ) : ℂ) =
    (-1 : ℂ) ^ Fintype.card A * (-1 : ℂ) ^ C.val.card :=
  parity_completion_complex _ _ _ _ _ _ (zCycleSupport_card_balance θ Z κ C)
    (cycleUnion_restriction_sign_twist_complex θ C.val)

end
end ModifiedCartan

