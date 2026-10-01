import ModifiedCartan.TotalTranspositionElement
import ModifiedCartan.KPAlphaFullInduction
import ModifiedCartan.SymmetricPairErasureModule
import Mathlib.GroupTheory.Perm.Support

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem supportedPermutation_extension_swap (I : Finset A) (a b : I) :
    (supportedPermutationEquiv I (Equiv.swap a b)).val = Equiv.swap a.val b.val := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ I
  · rw [supportedPermutationEquiv_apply_coe I (Equiv.swap a b) ⟨x, hx⟩]
    exact (Subtype.val_injective.swap_apply a b (⟨x, hx⟩ : I)).symm
  · rw [(supportedPermutationEquiv I (Equiv.swap a b)).property x hx]
    have ha : x ≠ a.val := fun h => hx (h.symm ▸ a.property)
    have hb : x ≠ b.val := fun h => hx (h.symm ▸ b.property)
    exact (Equiv.swap_apply_of_ne_of_ne ha hb).symm

theorem kpSubsetExtension_transposition (I : Finset A) (a b : I) :
    kpSubsetExtension I (transpositionElement a b) = transpositionElement a.val b.val := by
  simp only [kpSubsetExtension, transpositionElement, permutationElement,
    MonoidAlgebra.mapDomainLinearMap_single, supportedPermutation_extension_swap]

theorem kpSubsetExtension_totalTransposition (I : Finset A) :
    kpSubsetExtension I (totalTranspositionElement I) =
      (2 : ℂ)⁻¹ • ∑ a ∈ I, ∑ b ∈ I, if a = b then 0 else transpositionElement a b := by
  have he : kpSubsetExtension I (totalTranspositionElement I) =
      (2 : ℂ)⁻¹ • ∑ a : I, ∑ b : I,
        if a.val = b.val then 0 else transpositionElement a.val b.val := by
    simp only [totalTranspositionElement, map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b
    · subst b
      simp
    · have hv : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      rw [ite_eq_right hab, ite_eq_right hv, kpSubsetExtension_transposition]
  rw [he]
  congr 1
  calc
    _ = ∑ a : I, ∑ b ∈ I, if a.val = b then 0 else transpositionElement a.val b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_coe_sort I (fun b => if a.val = b then 0 else transpositionElement a.val b)
    _ = _ := Finset.sum_coe_sort I (fun a => ∑ b ∈ I, if a = b then 0 else transpositionElement a b)

/-- Deleting a letter decomposes the full central sum into the smaller central
sum and the star of transpositions at the deleted letter. -/
theorem totalTranspositionElement_delete (i : A) :
    totalTranspositionElement A =
      kpSubsetExtension (Finset.univ.erase i) (totalTranspositionElement (↥(Finset.univ.erase i))) +
        permutationStar (Finset.univ.erase i) i := by
  let f : A → A → ℂ[Equiv.Perm A] := fun a b => if a = b then 0 else transpositionElement a b
  have hs (a b : A) : f a b = f b a := by
    dsimp [f]
    rw [transpositionElement]
    simp only [transpositionElement, eq_comm, Equiv.swap_comm]
  have he := half_sum_symmetric_erase_module Finset.univ f hs i (Finset.mem_univ i) (by simp [f])
  have ht : (∑ j : A, f i j) = permutationStar (Finset.univ.erase i) i := by
    rw [permutationStar, Finset.sum_coe_sort, ← Finset.filter_ne Finset.univ i, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i = j <;> simp [f, h]
  change totalTranspositionElement A =
    (2 : ℂ)⁻¹ • (∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i,
      if a = b then 0 else transpositionElement a b) + ∑ j : A, f i j at he
  rw [← kpSubsetExtension_totalTransposition, ht] at he
  exact he

end
end ModifiedCartan


