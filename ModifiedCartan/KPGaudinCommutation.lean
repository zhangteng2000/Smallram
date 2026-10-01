import ModifiedCartan.KPGaudinReduction
import ModifiedCartan.AllSubsetInsertion

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Every actual beta operator commutes with each rational Gaudin element at
distinct parameters. This is a prerequisite, not yet beta-beta commutativity. -/
theorem kpGaudin_commutes_kpBeta (μ : YoungDiagram) (z : A → ℂ)
    (hz : Function.Injective z) (a : ℂ) (i : A) :
    kpGaudin z i * kpBeta μ z a = kpBeta μ z a * kpGaudin z i := by
  apply sub_eq_zero.mp
  rw [kpGaudin_beta_commutator_subsets μ z hz a i,
    sum_subset_insert_with_letter i]
  apply Finset.sum_eq_zero
  intro J _
  by_cases hi : i ∈ J
  · rw [ite_eq_left hi]
    calc
      _ = ∑ j : ↥(J.erase i), (-kpWeight z a J) •
          kpAlphaSwapCommutator μ i j.val (J.erase j.val) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.insert_erase (Finset.mem_erase.mp j.property).2]
      _ = (-kpWeight z a J) • ∑ j : ↥(J.erase i),
          kpAlphaSwapCommutator μ i j.val (J.erase j.val) := (Finset.smul_sum).symm
      _ = 0 := by
        have hs : (∑ j : ↥(J.erase i),
            kpAlphaSwapCommutator μ i j.val (J.erase j.val)) = 0 :=
          kpAlpha_erase_commutator_sum μ J i hi
        rw [hs, smul_zero]
  · rw [ite_eq_right hi]

end
end ModifiedCartan


