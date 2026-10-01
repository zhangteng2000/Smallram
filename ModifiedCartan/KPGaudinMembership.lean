import ModifiedCartan.KPColumnTwoBeta
import ModifiedCartan.KPTranslation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem kpGaudin_mem_generated {A : Type*} [Fintype A] [DecidableEq A]
    (z : A → ℂ) (hz : Function.Injective z) (i : A) :
    kpGaudin z i ∈ kpGeneratedAlgebra z := by
  have he : (kpRootProduct z i)⁻¹ • kpBeta (columnPartition 2) z (-z i) +
      (∑ j : A, (z i - z j)⁻¹) • (1 : ℂ[Equiv.Perm A]) = kpGaudin z i := by
    rw [kpBeta_column_two_at_root z hz i, smul_smul,
      inv_mul_cancel₀ (kpRootProduct_ne_zero z hz i), one_smul, sub_add_cancel]
  rw [← he]
  apply (kpGeneratedAlgebra z).add_mem
  · exact (kpGeneratedAlgebra z).smul_mem (kpBeta_mem_generated _ z _) _
  · exact (kpGeneratedAlgebra z).smul_mem (kpGeneratedAlgebra z).one_mem _

end
end ModifiedCartan


