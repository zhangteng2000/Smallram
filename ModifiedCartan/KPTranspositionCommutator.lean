import ModifiedCartan.KPAlphaEraseCommutator
import ModifiedCartan.KPSubsetWeights
import ModifiedCartan.FiniteInvolutionSum
import ModifiedCartan.FinsetSwapEquiv

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def kpAlphaSwapCommutator (μ : YoungDiagram) (i j : A) (I : Finset A) : ℂ[Equiv.Perm A] :=
  transpositionElement i j * kpAlpha μ I - kpAlpha μ I * transpositionElement i j

theorem kpAlphaSwapCommutator_image (μ : YoungDiagram) (i j : A) (I : Finset A) :
    kpAlphaSwapCommutator μ i j (finsetSwapEquiv i j I) = -kpAlphaSwapCommutator μ i j I := by
  have h₁ := transposition_kpAlpha_image μ I i j
  have h₂ := transposition_kpAlpha_image μ (I.image (Equiv.swap i j)) i j
  rw [finset_image_swap_twice] at h₂
  change transpositionElement i j * kpAlpha μ (I.image (Equiv.swap i j)) -
      kpAlpha μ (I.image (Equiv.swap i j)) * transpositionElement i j = _
  rw [h₂, ← h₁, kpAlphaSwapCommutator, neg_sub]

theorem kpAlphaSwapCommutator_zero (μ : YoungDiagram) (i j : A) (I : Finset A)
    (h : i ∈ I ↔ j ∈ I) : kpAlphaSwapCommutator μ i j I = 0 := by
  exact sub_eq_zero.mpr (kpAlpha_commutes_of_stabilizes_set μ I (Equiv.swap i j)
    (finset_image_swap_stable I i j h))

/-- Exact subset pairing for the commutator of a transposition with beta. -/
theorem kpBeta_transposition_commutator (μ : YoungDiagram) (z : A → ℂ) (a : ℂ) (i j : A) :
    transpositionElement i j * kpBeta μ z a - kpBeta μ z a * transpositionElement i j =
      ∑ I : Finset A, if i ∈ I ∧ j ∉ I then
        ((z j - z i) * kpWeight z a (insert j I)) • kpAlphaSwapCommutator μ i j I else 0 := by
  have hp (I : Finset A) (h : i ∈ I ∧ j ∉ I) :
      ¬(i ∈ finsetSwapEquiv i j I ∧ j ∉ finsetSwapEquiv i j I) := by
    rw [finsetSwapEquiv_cut]
    exact fun he => h.2 he.1
  have hz (I : Finset A) (h₁ : ¬(i ∈ I ∧ j ∉ I))
      (h₂ : ¬(i ∈ finsetSwapEquiv i j I ∧ j ∉ finsetSwapEquiv i j I)) :
      kpAlphaSwapCommutator μ i j I = 0 := by
    rw [finsetSwapEquiv_cut] at h₂
    apply kpAlphaSwapCommutator_zero
    tauto
  rw [kpBeta_eq_sum_all_subsets, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [mul_smul_comm, smul_mul_assoc, ← smul_sub]
  change (∑ I : Finset A, kpWeight z a I • kpAlphaSwapCommutator μ i j I) = _
  rw [sum_involution_cut (finsetSwapEquiv i j) (finsetSwapEquiv_involutive i j)
    (fun I => i ∈ I ∧ j ∉ I) hp (kpAlphaSwapCommutator μ i j)
    (kpAlphaSwapCommutator_image μ i j) hz (kpWeight z a)]
  apply Finset.sum_congr rfl
  intro I _
  by_cases h : i ∈ I ∧ j ∉ I
  · simp only [ite_eq_left h]
    rw [show finsetSwapEquiv i j I = I.image (Equiv.swap i j) from rfl,
      kpWeight_swap_difference z a I i j h.1 h.2]
  · simp only [ite_eq_right h]

end
end ModifiedCartan


