import ModifiedCartan.RightZFactorLaurentSeries

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem zCycleSupport_leftLaurentExponent {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (C : ZComplementCycleParameters θ Z) :
    -((zFactorLeftSet Z (zCycleSupport θ Z κ C)).card : ℤ) =
      -(∑ c ∈ permutationCycleImage θ (zStripComplement θ Z),
        (permutationCycleWeight θ (fun _ => 1) c : ℤ)) + compositionLaurentExponent (zStripLength θ Z) κ +
        ∑ c ∈ C.val, (permutationCycleWeight θ (fun _ => 1) c : ℤ) := by
  have hx : ((zFactorLeftSet Z (zCycleSupport θ Z κ C)).card : ℤ) +
      ((zCycleSupport θ Z κ C).card : ℤ) = (Fintype.card A : ℤ) + Z.card := by
    exact_mod_cast zFactorLeftSet_card Z (zCycleSupport θ Z κ C)
      (zCycleSupport_isZAdmissible θ Z κ C).1
  have he := zCycleSupport_laurentExponent θ Z κ C
  omega

theorem zSupportLaurentTerm_normalized {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a))
    (C : ZComplementCycleParameters θ Z) :
    zSupportLaurentTerm B θ Z (zCycleSupport θ Z κ C) =
      LaurentPolynomial.C (MvPolynomial.C ((-1 : ℂ) ^ Fintype.card A)) *
      ((LaurentPolynomial.T (-(∑ c ∈ permutationCycleImage θ (zStripComplement θ Z),
          (permutationCycleWeight θ (fun _ => 1) c : ℤ))) *
        (LaurentPolynomial.T (compositionLaurentExponent (zStripLength θ Z) κ) *
          LaurentPolynomial.C (scaledMonomialPolynomial B (fun a : Z => (κ a).val + 1)))) *
       (LaurentPolynomial.C ((-1 : MvPolynomial B ℂ) ^ C.val.card *
          ∏ c ∈ C.val, finitePowerSumPolynomial B (permutationCycleWeight θ (fun _ => 1) c)) *
        LaurentPolynomial.T (∑ c ∈ C.val, (permutationCycleWeight θ (fun _ => 1) c : ℤ)))) := by
  unfold zSupportLaurentTerm
  rw [rightZFactorPolynomial_normalized]
  have ht : (LaurentPolynomial.T (-((zFactorLeftSet Z (zCycleSupport θ Z κ C)).card : ℤ)) :
      LaurentPolynomial (MvPolynomial B ℂ)) =
      LaurentPolynomial.T (-(∑ c ∈ permutationCycleImage θ (zStripComplement θ Z),
        (permutationCycleWeight θ (fun _ => 1) c : ℤ))) *
      LaurentPolynomial.T (compositionLaurentExponent (zStripLength θ Z) κ) *
      LaurentPolynomial.T (∑ c ∈ C.val, (permutationCycleWeight θ (fun _ => 1) c : ℤ)) := by
    rw [← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add,
      zCycleSupport_leftLaurentExponent]
  rw [ht]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

end
end ModifiedCartan

