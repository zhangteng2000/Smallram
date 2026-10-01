import ModifiedCartan.SupportedDataRestriction
import ModifiedCartan.FixedColoringTransport
import Mathlib.GroupTheory.Perm.Sign

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem extendSupportedPermutationData_sign {A : Type*} [Fintype A]
    (U : Finset A) (p : SupportedPermutationData U) :
    Equiv.Perm.sign (extendSupportedPermutationData U p).2.val = Equiv.Perm.sign p.2.val :=
  Equiv.Perm.sign_ofSubtype p.2.val

theorem extendSupportedPermutationData_card {A : Type*}
    (U : Finset A) (p : SupportedPermutationData U) :
    (extendSupportedPermutationData U p).1.card = p.1.card :=
  finiteSubtypeSupportImage_card U p.1

theorem extendSupportedPermutationData_restriction {A : Type*}
    (U : Finset A) (p : SupportedPermutationData U) :
    supportedPermutationRestriction (extendSupportedPermutationData U p).1
      (extendSupportedPermutationData U p).2.val (extendSupportedPermutationData U p).2.property =
    (finiteSubtypeSupportElementEquiv U p.1).permCongr
      (supportedPermutationRestriction p.1 p.2.val p.2.property) := by
  dsimp only [extendSupportedPermutationData]
  apply Equiv.ext
  intro x
  obtain ⟨a, rfl⟩ := (finiteSubtypeSupportElementEquiv U p.1).surjective x
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  exact Equiv.Perm.ofSubtype_apply_coe p.2.val a.val

/-- Extending a supported permutation preserves its cycle power-sum
polynomial on its designated support, including all singleton cycles. -/
theorem extendSupportedPermutationData_fixedColoringSum {A B R : Type*}
    [Fintype B] [CommSemiring R] (U : Finset A) (p : SupportedPermutationData U) (x : B → R) :
    permutationFixedColoringSum
      (supportedPermutationRestriction (extendSupportedPermutationData U p).1
        (extendSupportedPermutationData U p).2.val (extendSupportedPermutationData U p).2.property) x =
      permutationFixedColoringSum (supportedPermutationRestriction p.1 p.2.val p.2.property) x := by
  have h := extendSupportedPermutationData_restriction U p
  dsimp only [extendSupportedPermutationData] at h ⊢
  rw [h]
  exact permutationFixedColoringSum_conjugate (finiteSubtypeSupportElementEquiv U p.1) _ x

end
end ModifiedCartan

