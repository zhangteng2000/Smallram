import ModifiedCartan.FiniteSubsetSwaps
import ModifiedCartan.KPAlphaConjugation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [DecidableEq A]

def permutationElement (u : Equiv.Perm A) : ℂ[Equiv.Perm A] :=
  MonoidAlgebra.single u 1

theorem permutationElement_mul (u v : Equiv.Perm A) :
    permutationElement u * permutationElement v = permutationElement (u * v) := by
  simp [permutationElement, MonoidAlgebra.single_mul_single]

theorem permutationElement_one : permutationElement (1 : Equiv.Perm A) = 1 := rfl

theorem permutationElement_inv_mul (u : Equiv.Perm A) :
    permutationElement u⁻¹ * permutationElement u = 1 := by
  rw [permutationElement_mul, inv_mul_cancel, permutationElement_one]

theorem permutationElement_conjugation_cancel (u : Equiv.Perm A)
    (x y : ℂ[Equiv.Perm A]) (h : permutationElement u * x * permutationElement u⁻¹ = y) :
    permutationElement u * x = y * permutationElement u := by
  have he := congrArg (fun q => q * permutationElement u) h
  simpa only [mul_assoc, permutationElement_inv_mul, mul_one] using he

def transpositionElement (i j : A) : ℂ[Equiv.Perm A] := permutationElement (Equiv.swap i j)

theorem transpositionElement_conjugate (u : Equiv.Perm A) (i j : A) :
    permutationElement u * transpositionElement i j * permutationElement u⁻¹ =
      transpositionElement (u i) (u j) := by
  simp only [transpositionElement, permutationElement_mul, ← Equiv.swap_apply_apply]

/-- The star of transpositions joining a fixed letter to an actual subset. -/
def permutationStar (I : Finset A) (i : A) : ℂ[Equiv.Perm A] :=
  ∑ j : I, transpositionElement i j.val

theorem permutationStar_conjugate (I : Finset A) (i : A) (u : Equiv.Perm A) :
    permutationElement u * permutationStar I i * permutationElement u⁻¹ =
      permutationStar (I.image u) (u i) := by
  simp only [permutationStar, Finset.mul_sum, Finset.sum_mul, transpositionElement_conjugate]
  exact (permutationImageEquiv I u).sum_comp (fun j => transpositionElement (u i) j.val)

theorem permutationStar_commutes_supported (I : Finset A) (i : A) (hi : i ∉ I)
    (u : supportedPermutationSubgroup I) :
    permutationElement u.val * permutationStar I i =
      permutationStar I i * permutationElement u.val := by
  apply permutationElement_conjugation_cancel
  rw [permutationStar_conjugate, supportedPermutation_image_self, u.property i hi]

theorem kpAlpha_commutes_permutationStar (μ : YoungDiagram) (I : Finset A)
    (i : A) (hi : i ∉ I) :
    kpAlpha μ I * permutationStar I i = permutationStar I i * kpAlpha μ I := by
  by_cases hI : I.card = partitionSize μ
  · rw [kpAlpha_of_card_eq μ I hI]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    have he (c : ℂ) : MonoidAlgebra.single (supportedPermutationEquiv I p).val c =
        c • permutationElement (supportedPermutationEquiv I p).val := by
      simp [permutationElement, MonoidAlgebra.smul_single]
    rw [he, smul_mul_assoc, mul_smul_comm, permutationStar_commutes_supported I i hi]
  · rw [kpAlpha_of_card_ne μ I hI, zero_mul, mul_zero]

end
end ModifiedCartan


