import ModifiedCartan.KPOperators
import ModifiedCartan.SupportedPermutationImages

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Conjugation transports the actual character sum to the image subset. -/
theorem kpAlpha_conjugate (μ : YoungDiagram) (I : Finset A) (u : Equiv.Perm A) :
    MonoidAlgebra.single u (1 : ℂ) * kpAlpha μ I * MonoidAlgebra.single u⁻¹ 1 =
      kpAlpha μ (I.image u) := by
  have hc := Finset.card_image_of_injective I u.injective
  by_cases hI : I.card = partitionSize μ
  · have hJ : (I.image u).card = partitionSize μ := hc.trans hI
    rw [kpAlpha_of_card_eq μ I hI, kpAlpha_of_card_eq μ _ hJ]
    simp only [Finset.mul_sum, Finset.sum_mul, MonoidAlgebra.single_mul_single,
      one_mul, mul_one]
    calc
      _ = ∑ p : Equiv.Perm I,
          MonoidAlgebra.single
            (supportedPermutationEquiv (I.image u) ((permutationImageEquiv I u).permCongr p)).val
            (spechtCharacterOn μ ((Fintype.card_coe _).trans hJ)
              ((permutationImageEquiv I u).permCongr p)) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [supportedPermutation_image_conjugate,
          spechtCharacterOn_relabel μ _ _ (permutationImageEquiv I u) p]
      _ = _ := (permutationImageEquiv I u).permCongr.sum_comp (fun p =>
        MonoidAlgebra.single (supportedPermutationEquiv (I.image u) p).val
          (spechtCharacterOn μ ((Fintype.card_coe _).trans hJ) p))
  · have hJ : (I.image u).card ≠ partitionSize μ := by rwa [hc]
    rw [kpAlpha_of_card_ne μ I hI, kpAlpha_of_card_ne μ _ hJ, mul_zero, zero_mul]

theorem kpAlpha_commutes_of_stabilizes_set (μ : YoungDiagram) (I : Finset A)
    (u : Equiv.Perm A) (h : I.image u = I) :
    MonoidAlgebra.single u (1 : ℂ) * kpAlpha μ I =
      kpAlpha μ I * MonoidAlgebra.single u 1 := by
  have he := congrArg (fun x : ℂ[Equiv.Perm A] => x * MonoidAlgebra.single u 1)
    (kpAlpha_conjugate μ I u)
  have hi : MonoidAlgebra.single u⁻¹ (1 : ℂ) * MonoidAlgebra.single u 1 =
      (1 : ℂ[Equiv.Perm A]) := by
    rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul]
    rfl
  simpa only [h, mul_assoc, hi, mul_one] using he

end
end ModifiedCartan


