import ModifiedCartan.FiniteSubsetSwaps
import ModifiedCartan.SizedSubsetInsertion
import ModifiedCartan.FixedPointPermutationSums

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def kpWeight (z : A → ℂ) (a : ℂ) (I : Finset A) : ℂ :=
  ∏ l ∈ Finset.univ \ I, (a + z l)

theorem complement_erase_of_mem (J : Finset A) (i : A) (hi : i ∈ J) :
    Finset.univ \ J.erase i = insert i (Finset.univ \ J) := by
  ext x
  by_cases hx : x = i <;> simp [hx, hi]

theorem kpWeight_erase (z : A → ℂ) (a : ℂ) (J : Finset A) (i : A) (hi : i ∈ J) :
    kpWeight z a (J.erase i) = (a + z i) * kpWeight z a J := by
  rw [kpWeight, complement_erase_of_mem J i hi, Finset.prod_insert (by simp [hi])]
  rfl

theorem kpWeight_swap_difference (z : A → ℂ) (a : ℂ) (I : Finset A) (i j : A)
    (hi : i ∈ I) (hj : j ∉ I) :
    kpWeight z a I - kpWeight z a (I.image (Equiv.swap i j)) =
      (z j - z i) * kpWeight z a (insert j I) := by
  have hij : i ≠ j := fun he => hj (he ▸ hi)
  have he : I.image (Equiv.swap i j) = (insert j I).erase i := by
    rw [finset_image_swap_replace I i j hi hj]
    ext x
    by_cases hx : x = i <;> simp [hx, hij, eq_comm]
  have hw := kpWeight_erase z a (insert j I) j (Finset.mem_insert_self j I)
  rw [Finset.erase_insert hj] at hw
  rw [he, hw, kpWeight_erase z a _ i (Finset.mem_insert_of_mem hi)]
  ring

theorem kpBeta_eq_sum_all_subsets (μ : YoungDiagram) (z : A → ℂ) (a : ℂ) :
    kpBeta μ z a = ∑ I : Finset A, kpWeight z a I • kpAlpha μ I := by
  rw [kpBeta, sum_sizedLetterSubset]
  calc
    _ = ∑ I : Finset A, if h : I.card = partitionSize μ then
        kpWeight z a I • kpAlpha μ I else 0 :=
      (sum_dite_eq_sum_subtype (fun I : Finset A => I.card = partitionSize μ)
        (fun I _ => kpWeight z a I • kpAlpha μ I)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      by_cases h : I.card = partitionSize μ
      · rw [dif_pos h]
      · rw [dif_neg h, kpAlpha_of_card_ne μ I h, smul_zero]

end
end ModifiedCartan


