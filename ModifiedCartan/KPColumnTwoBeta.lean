import ModifiedCartan.KPColumnTwoAlpha
import ModifiedCartan.PairSubsetSum
import ModifiedCartan.KPRootWeights
import ModifiedCartan.KPGaudinReduction

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem kpBeta_column_two_at_root_sum (z : A → ℂ) (i : A) :
    kpBeta (columnPartition 2) z (-z i) =
      ∑ j ∈ (Finset.univ : Finset A).erase i,
        kpWeight z (-z i) {i, j} • (1 - transpositionElement i j) := by
  rw [kpBeta, partitionSize_columnPartition]
  change (∑ I ∈ (Finset.univ : Finset A).powersetCard 2,
    kpWeight z (-z i) I • kpAlpha (columnPartition 2) I) = _
  calc
    _ = ∑ I ∈ (Finset.univ : Finset A).powersetCard 2,
        if i ∈ I then kpWeight z (-z i) I • kpAlpha (columnPartition 2) I else 0 := by
      apply Finset.sum_congr rfl
      intro I hI
      by_cases hi : i ∈ I
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi, kpWeight_at_root_zero z i I hi, zero_smul]
    _ = ∑ j ∈ (Finset.univ : Finset A).erase i,
        kpWeight z (-z i) {i, j} • kpAlpha (columnPartition 2) {i, j} :=
      sum_two_subsets_containing i _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [kpAlpha_column_two_pair i j (Ne.symm (Finset.mem_erase.mp hj).1)]

theorem kpBeta_column_two_at_root (z : A → ℂ) (hz : Function.Injective z) (i : A) :
    kpBeta (columnPartition 2) z (-z i) =
      kpRootProduct z i • (kpGaudin z i -
        (∑ j : A, (z i - z j)⁻¹) • (1 : ℂ[Equiv.Perm A])) := by
  rw [kpBeta_column_two_at_root_sum, kpGaudin, Finset.sum_smul,
    ← Finset.sum_sub_distrib, Finset.smul_sum]
  have he : (∑ j ∈ (Finset.univ : Finset A).erase i,
      kpRootProduct z i • ((z i - z j)⁻¹ • transpositionElement i j -
        (z i - z j)⁻¹ • (1 : ℂ[Equiv.Perm A]))) =
      ∑ j : A, kpRootProduct z i • ((z i - z j)⁻¹ • transpositionElement i j -
        (z i - z j)⁻¹ • (1 : ℂ[Equiv.Perm A])) := by
    have hh := Finset.add_sum_erase (Finset.univ : Finset A)
      (fun j => kpRootProduct z i • ((z i - z j)⁻¹ • transpositionElement i j -
        (z i - z j)⁻¹ • (1 : ℂ[Equiv.Perm A]))) (Finset.mem_univ i)
    simpa only [sub_self, inv_zero, zero_smul, smul_zero, zero_add] using hh
  rw [← he]
  apply Finset.sum_congr rfl
  intro j hj
  rw [kpWeight_pair_at_root z hz i j (Ne.symm (Finset.mem_erase.mp hj).1)]
  rw [show z j - z i = -(z i - z j) by ring, inv_neg]
  module

end
end ModifiedCartan


