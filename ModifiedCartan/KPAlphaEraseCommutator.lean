import ModifiedCartan.PermutationStar

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem transpositionElement_comm (i j : A) :
    transpositionElement i j = transpositionElement j i := by
  simp only [transpositionElement, Equiv.swap_comm]

theorem transposition_kpAlpha_image (μ : YoungDiagram) (I : Finset A) (i j : A) :
    transpositionElement i j * kpAlpha μ I =
      kpAlpha μ (I.image (Equiv.swap i j)) * transpositionElement i j :=
  permutationElement_conjugation_cancel (Equiv.swap i j) _ _ (kpAlpha_conjugate μ I _)

theorem transposition_kpAlpha_erase (μ : YoungDiagram) (J : Finset A) (i j : A)
    (hi : i ∈ J) (hj : j ∈ J) :
    transpositionElement i j * kpAlpha μ (J.erase j) =
      kpAlpha μ (J.erase i) * transpositionElement i j := by
  rw [transposition_kpAlpha_image, finset_image_swap_erase J i j hi hj]

theorem kpAlpha_erase_commutator_pair (μ : YoungDiagram) (J : Finset A) (i j : A)
    (hi : i ∈ J) (hj : j ∈ J) :
    transpositionElement i j * kpAlpha μ (J.erase j) -
        kpAlpha μ (J.erase j) * transpositionElement i j =
      kpAlpha μ (J.erase i) * transpositionElement i j -
        transpositionElement i j * kpAlpha μ (J.erase i) := by
  have he := transposition_kpAlpha_erase μ J j i hj hi
  rw [transpositionElement_comm j i] at he
  rw [transposition_kpAlpha_erase μ J i j hi hj, ← he]

/-- Cancellation of all deletion commutators in one enlarged subset. -/
theorem kpAlpha_erase_commutator_sum (μ : YoungDiagram) (J : Finset A) (i : A)
    (hi : i ∈ J) :
    (∑ j : ↥(J.erase i),
      (transpositionElement i j.val * kpAlpha μ (J.erase j.val) -
        kpAlpha μ (J.erase j.val) * transpositionElement i j.val)) = 0 := by
  calc
    _ = ∑ j : ↥(J.erase i),
        (kpAlpha μ (J.erase i) * transpositionElement i j.val -
          transpositionElement i j.val * kpAlpha μ (J.erase i)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact kpAlpha_erase_commutator_pair μ J i j.val hi (Finset.mem_erase.mp j.property).2
    _ = kpAlpha μ (J.erase i) * permutationStar (J.erase i) i -
        permutationStar (J.erase i) i * kpAlpha μ (J.erase i) := by
      simp only [permutationStar, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    _ = 0 := sub_eq_zero.mpr (kpAlpha_commutes_permutationStar μ _ i (Finset.notMem_erase i J))

end
end ModifiedCartan


