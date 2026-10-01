import ModifiedCartan.ColumnPartitions
import ModifiedCartan.KPSubsetWeights
import ModifiedCartan.ZFactorizationParameters
import ModifiedCartan.RemovalSigns

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem kpAlpha_column_supported {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (X : Finset A) (hX : X.card = k) :
    kpAlpha (columnPartition k) X =
      ∑ σ : supportedPermutationSubgroup X,
        MonoidAlgebra.single σ.val (((Equiv.Perm.sign σ.val : ℤ) : ℂ)) := by
  rw [kpAlpha_of_card_eq _ _ (hX.trans (partitionSize_columnPartition k).symm)]
  simp_rw [spechtCharacterOn_columnPartition]
  rw [← Equiv.sum_comp (supportedPermutationEquiv X).toEquiv
    (fun σ => MonoidAlgebra.single σ.val (((Equiv.Perm.sign σ.val : ℤ) : ℂ)))]
  apply Finset.sum_congr rfl
  intro σ hσ
  change MonoidAlgebra.single (supportedPermutationEquiv X σ).val
      (((Equiv.Perm.sign σ : ℤ) : ℂ)) =
    MonoidAlgebra.single (supportedPermutationEquiv X σ).val
      (((Equiv.Perm.sign (supportedPermutationEquiv X σ).val : ℤ) : ℂ))
  rw [sign_supportedPermutationEquiv]

/-- The previously constructed KP single-column operator, expanded over
literal supported permutations. LaTeX `eq:KP-operators`. -/
theorem kpBeta_column_supported {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (z : A → ℂ) (a : ℂ) :
    kpBeta (columnPartition k) z a =
      ∑ p : SupportedPermutationData A,
        if p.1.card = k then (∏ l ∈ Finset.univ \ p.1, (a + z l)) •
          MonoidAlgebra.single p.2.val (((Equiv.Perm.sign p.2.val : ℤ) : ℂ)) else 0 := by
  rw [kpBeta_eq_sum_all_subsets, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro X hX
  by_cases hk : X.card = k
  · rw [kpAlpha_column_supported k X hk]
    simp only [hk, if_true, Finset.smul_sum, kpWeight]
  · rw [kpAlpha_of_card_ne _ _ (by simpa only [partitionSize_columnPartition] using hk)]
    simp only [hk, if_false, Finset.sum_const_zero, smul_zero]

end
end ModifiedCartan

