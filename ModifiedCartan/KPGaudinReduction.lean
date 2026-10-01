import ModifiedCartan.KPTranspositionCommutator

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The rational Gaudin element. The diagonal term is zero because `0⁻¹ = 0`. -/
def kpGaudin (z : A → ℂ) (i : A) : ℂ[Equiv.Perm A] :=
  ∑ j : A, (z i - z j)⁻¹ • transpositionElement i j

theorem kpGaudin_commutator_expand (z : A → ℂ) (i : A) (x : ℂ[Equiv.Perm A]) :
    kpGaudin z i * x - x * kpGaudin z i =
      ∑ j : A, (z i - z j)⁻¹ • (transpositionElement i j * x - x * transpositionElement i j) := by
  simp only [kpGaudin, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib,
    smul_mul_assoc, mul_smul_comm, smul_sub]

theorem kpGaudin_weight_cancel (z : A → ℂ) (hz : Function.Injective z)
    (i j : A) (hij : i ≠ j) (w : ℂ) :
    (z i - z j)⁻¹ * ((z j - z i) * w) = -w := by
  have hn : z i - z j ≠ 0 := sub_ne_zero.mpr (fun he => hij (hz he))
  rw [← mul_assoc, show z j - z i = -(z i - z j) by ring,
    mul_neg, inv_mul_cancel₀ hn, neg_one_mul]

theorem kpGaudin_beta_commutator_subsets (μ : YoungDiagram) (z : A → ℂ)
    (hz : Function.Injective z) (a : ℂ) (i : A) :
    kpGaudin z i * kpBeta μ z a - kpBeta μ z a * kpGaudin z i =
      ∑ j : A, ∑ I : Finset A, if i ∈ I ∧ j ∉ I then
        (-kpWeight z a (insert j I)) • kpAlphaSwapCommutator μ i j I else 0 := by
  rw [kpGaudin_commutator_expand]
  apply Finset.sum_congr rfl
  intro j _
  rw [kpBeta_transposition_commutator, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro I _
  by_cases h : i ∈ I ∧ j ∉ I
  · rw [ite_eq_left h, ite_eq_left h, smul_smul,
      kpGaudin_weight_cancel z hz i j (fun he => h.2 (he ▸ h.1))]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

end
end ModifiedCartan


