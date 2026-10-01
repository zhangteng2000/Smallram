import ModifiedCartan.GarnirAlternation
import ModifiedCartan.FillingPolytabloids

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def garnirColumnPermutations (μ : YoungDiagram) (r j : ℕ) :
    Finset (supportedPermutationSubgroup (garnirBelt μ r j)) :=
  Finset.univ.filter (fun g => g.val ∈ youngColumnSubgroup μ)

def garnirMixingPermutations (μ : YoungDiagram) (r j : ℕ) :
    Finset (supportedPermutationSubgroup (garnirBelt μ r j)) :=
  Finset.univ.filter (fun g => g.val ∉ youngColumnSubgroup μ)

theorem garnirColumnPermutations_card_pos (μ : YoungDiagram) (r j : ℕ) :
    0 < (garnirColumnPermutations μ r j).card := by
  apply Finset.card_pos.mpr
  refine ⟨1, ?_⟩
  simp [garnirColumnPermutations]

theorem garnir_column_sum (μ : YoungDiagram) (r j : ℕ) :
    (∑ g ∈ garnirColumnPermutations μ r j,
      youngPermutationSign μ g.val •
        youngTabloidRepresentation μ g.val (youngPolytabloid μ)) =
      ((garnirColumnPermutations μ r j).card : ℂ) • youngPolytabloid μ := by
  calc
    _ = ∑ _g ∈ garnirColumnPermutations μ r j, (1 : ℂ) • youngPolytabloid μ := by
      apply Finset.sum_congr rfl
      intro g hg
      have hc : g.val ∈ youngColumnSubgroup μ := (Finset.mem_filter.mp hg).2
      rw [youngPolytabloid_column_action μ ⟨g.val, hc⟩,
        smul_smul, youngPermutationSign_mul_self]
    _ = _ := by rw [← Finset.sum_smul]; simp

/-- Full signed averaging yields Garnir's relation with a positive multiplicity.
This avoids choosing representatives for the column-preserving subgroup. -/
theorem garnir_relation_sum (μ : YoungDiagram) (r j : ℕ)
    (hcell : (r, j + 1) ∈ μ) :
    ((garnirColumnPermutations μ r j).card : ℂ) • youngPolytabloid μ +
      ∑ g ∈ garnirMixingPermutations μ r j,
        youngPermutationSign μ g.val •
          youngTabloidRepresentation μ g.val (youngPolytabloid μ) = 0 := by
  rw [← garnir_column_sum]
  unfold garnirColumnPermutations garnirMixingPermutations
  rw [Finset.sum_filter_add_sum_filter_not]
  simpa only [youngSubgroupAlternatingOperator, LinearMap.sum_apply,
    LinearMap.smul_apply] using garnirBelt_alternation_polytabloid_zero μ r j hcell

theorem youngFillingPermutation_precompose (μ : YoungDiagram) (T : YoungFilling μ)
    (g : Equiv.Perm (YoungBoxes μ)) :
    youngFillingPermutation μ (g.trans T) = youngFillingPermutation μ T * g := by
  apply Equiv.ext
  intro b
  rfl

theorem garnir_filling_relation_sum (μ : YoungDiagram) (r j : ℕ)
    (hcell : (r, j + 1) ∈ μ) (T : YoungFilling μ) :
    ((garnirColumnPermutations μ r j).card : ℂ) • youngFillingPolytabloid μ T +
      ∑ g ∈ garnirMixingPermutations μ r j,
        youngPermutationSign μ g.val • youngFillingPolytabloid μ (g.val.trans T) = 0 := by
  have h := congrArg (youngTabloidRepresentation μ (youngFillingPermutation μ T))
    (garnir_relation_sum μ r j hcell)
  simpa only [map_add, map_smul, map_sum, map_zero, youngFillingPolytabloid,
    youngFillingPermutation_precompose, map_mul, Module.End.mul_apply] using h

/-- The actual filling polytabloid is a linear combination of mixed Garnir fillings. -/
theorem garnir_filling_relation (μ : YoungDiagram) (r j : ℕ)
    (hcell : (r, j + 1) ∈ μ) (T : YoungFilling μ) :
    youngFillingPolytabloid μ T =
      ((garnirColumnPermutations μ r j).card : ℂ)⁻¹ •
        (-(∑ g ∈ garnirMixingPermutations μ r j,
          youngPermutationSign μ g.val • youngFillingPolytabloid μ (g.val.trans T))) := by
  have hk : ((garnirColumnPermutations μ r j).card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (garnirColumnPermutations_card_pos μ r j))
  have h := eq_neg_of_add_eq_zero_left (garnir_filling_relation_sum μ r j hcell T)
  rw [← h, inv_smul_smul₀ hk]

theorem garnir_filling_mem_of_mixed (μ : YoungDiagram) (r j : ℕ)
    (hcell : (r, j + 1) ∈ μ) (T : YoungFilling μ)
    (U : Submodule ℂ (YoungPermutationModule μ))
    (hU : ∀ g ∈ garnirMixingPermutations μ r j,
      youngFillingPolytabloid μ (g.val.trans T) ∈ U) :
    youngFillingPolytabloid μ T ∈ U := by
  rw [garnir_filling_relation μ r j hcell T]
  apply U.smul_mem
  apply U.neg_mem
  apply U.sum_mem
  intro g hg
  exact U.smul_mem _ (hU g hg)

end
end ModifiedCartan


