import ModifiedCartan.CycleUnionPowerSums
import ModifiedCartan.CycleUnionSignTwist
import ModifiedCartan.FiniteAlphabetShift

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem cycleUnion_signed_fixedColoringSum {A B R : Type*} [Fintype A] [Fintype B]
    [CommRing R] [Algebra ℂ R] (σ : Equiv.Perm A) (C : Finset (PermutationCycles σ)) (x : B → R) :
    (-1 : ℂ) ^ (permutationCycleUnion σ C).card •
      (((Equiv.Perm.sign (σ.subtypePerm (permutationCycleUnion_invariant σ C)) : ℤ) : ℂ) •
        permutationFixedColoringSum (σ.subtypePerm (permutationCycleUnion_invariant σ C)) x) =
    (-1 : ℂ) ^ C.card • ∏ c ∈ C, ∑ b : B, x b ^ permutationCycleWeight σ (fun _ => 1) c := by
  rw [← mul_smul, cycleUnion_restriction_sign_twist_complex,
    cycleUnion_restriction_fixedColoringSum]

theorem cycleUnion_signed_powerSumPolynomial {A B : Type*} [Fintype A] [Fintype B]
    (σ : Equiv.Perm A) (C : Finset (PermutationCycles σ)) :
    MvPolynomial.C ((-1 : ℂ) ^ (permutationCycleUnion σ C).card *
      ((Equiv.Perm.sign (σ.subtypePerm (permutationCycleUnion_invariant σ C)) : ℤ) : ℂ)) *
      permutationFixedColoringSum (σ.subtypePerm (permutationCycleUnion_invariant σ C))
        (fun b : B => (MvPolynomial.X b : MvPolynomial B ℂ)) =
    MvPolynomial.C ((-1 : ℂ) ^ C.card) *
      ∏ c ∈ C, finitePowerSumPolynomial B (permutationCycleWeight σ (fun _ => 1) c) := by
  rw [cycleUnion_restriction_sign_twist_complex, cycleUnion_restriction_fixedColoringSum]
  rfl

end
end ModifiedCartan

