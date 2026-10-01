import ModifiedCartan.RightZFactorSignedSum
import ModifiedCartan.ZFactorCardParity
import ModifiedCartan.CycleUnionPowerSums
import ModifiedCartan.FiniteAlphabetShift

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The actual finite-alphabet inner sum in KP source equation (4.4),
with cycles counted on Y, including singleton cycles. -/
def rightZFactorPolynomial {A : Type*} [Fintype A] (B : Type*) [Fintype B]
    (θ : Equiv.Perm A) (Z Y : Finset A) : MvPolynomial B ℂ :=
  ∑ π : {π : Equiv.Perm A // IsRightZFactor θ Z Y π},
    MvPolynomial.C (((Equiv.Perm.sign π.val : ℤ) : ℂ)) *
      permutationFixedColoringSum
        (supportedPermutationRestriction Y π.val ((isRightZFactor_iff θ Z Y π.val).mp π.property).2.1)
        (fun b : B => (MvPolynomial.X b : MvPolynomial B ℂ))

theorem rightZFactorPolynomial_cycleSupport {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a))
    (C : ZComplementCycleParameters θ Z) :
    rightZFactorPolynomial B θ Z (zCycleSupport θ Z κ C) =
      (MvPolynomial.C (((Equiv.Perm.sign (θ.subtypePerm (permutationCycleUnion_invariant θ C.val)) : ℤ) : ℂ)) *
        (MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Z, (κ a).val)) *
          scaledMonomialPolynomial B (fun a : Z => (κ a).val + 1))) *
        ∏ c ∈ C.val, finitePowerSumPolynomial B (permutationCycleWeight θ (fun _ => 1) c) := by
  have h := rightZFactor_signed_coloring_sum θ Z κ (permutationCycleUnion θ C.val)
    (zCycleSupport_complement_subset θ Z C) (permutationCycleUnion_invariant θ C.val)
    (fun b : B => (MvPolynomial.X b : MvPolynomial B ℂ))
  rw [cycleUnion_restriction_fixedColoringSum] at h
  simp only [rightZFactorPolynomial, zCycleSupport, MvPolynomial.smul_eq_C_mul,
    scaledMonomialPolynomial, finitePowerSumPolynomial] at h ⊢
  convert h using 1 <;> congr 2

/-- Exact sign normalization for the actual inner factor sum; auxiliary to
LaTeX `lem:KP-correspondence`, KP source Section 4.1.4. -/
theorem rightZFactorPolynomial_normalized {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a))
    (C : ZComplementCycleParameters θ Z) :
    MvPolynomial.C ((-1 : ℂ) ^ (zFactorLeftSet Z (zCycleSupport θ Z κ C)).card) *
      rightZFactorPolynomial B θ Z (zCycleSupport θ Z κ C) =
    MvPolynomial.C ((-1 : ℂ) ^ Fintype.card A * (-1 : ℂ) ^ C.val.card) *
      scaledMonomialPolynomial B (fun a : Z => (κ a).val + 1) *
        ∏ c ∈ C.val, finitePowerSumPolynomial B (permutationCycleWeight θ (fun _ => 1) c) := by
  rw [rightZFactorPolynomial_cycleSupport]
  have he (a b c : ℂ) (M P : MvPolynomial B ℂ) :
      MvPolynomial.C a * ((MvPolynomial.C c * (MvPolynomial.C b * M)) * P) =
        MvPolynomial.C (a * b * c) * M * P := by
    simp only [map_mul]
    ring
  rw [he, zCycleSupport_sign_balance]

end
end ModifiedCartan

