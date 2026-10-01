import ModifiedCartan.GarnirRelation
import ModifiedCartan.GarnirSeparation
import ModifiedCartan.FiniteSetExchange

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem garnir_mixing_image_left_ne (μ : YoungDiagram) (r j : ℕ)
    (g : supportedPermutationSubgroup (garnirBelt μ r j))
    (hg : g ∈ garnirMixingPermutations μ r j) :
    (garnirLeft μ r j).image g.val ≠ garnirLeft μ r j := by
  intro he
  apply (Finset.mem_filter.mp hg).2
  intro a
  by_cases ha : a ∈ garnirBelt μ r j
  · have hga := supportedPermutation_apply_mem (garnirBelt μ r j) g ha
    rcases Finset.mem_union.mp ha with hl | hr
    · have hgl : g.val a ∈ garnirLeft μ r j := by
        rw [← he]
        exact Finset.mem_image.mpr ⟨a, hl, rfl⟩
      exact ((mem_garnirLeft μ r j _).mp hgl).1.trans
        ((mem_garnirLeft μ r j _).mp hl).1.symm
    · have hgr : g.val a ∈ garnirRight μ r j := by
        rcases Finset.mem_union.mp hga with hgl | hgr
        · rw [← he] at hgl
          obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hgl
          have hba : b = a := g.val.injective hab
          exact False.elim (Finset.disjoint_left.mp (garnirLeft_disjoint_right μ r j)
            (hba ▸ hb) hr)
        · exact hgr
      exact ((mem_garnirRight μ r j _).mp hgr).1.trans
        ((mem_garnirRight μ r j _).mp hr).1.symm
  · rw [g.property a ha]

theorem garnir_image_left_sdiff_mem_right (μ : YoungDiagram) (r j : ℕ)
    (g : supportedPermutationSubgroup (garnirBelt μ r j)) (a : YoungBoxes μ)
    (ha : a ∈ (garnirLeft μ r j).image g.val \ garnirLeft μ r j) :
    a ∈ garnirRight μ r j := by
  have ha' := Finset.mem_sdiff.mp ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha'.1
  have hgb := supportedPermutation_apply_mem (garnirBelt μ r j) g
    (Finset.mem_union_left _ hb)
  exact (Finset.mem_union.mp hgb).resolve_left ha'.2

/-- Every mixing term strictly decreases the sum of labels in the left tail. -/
theorem garnir_mixing_left_sum_lt (μ : YoungDiagram) (T : YoungFilling μ)
    (hT : YoungColumnStandard T) (r j : ℕ) (hl : (r, j) ∈ μ) (hr : (r, j + 1) ∈ μ)
    (hinv : T ⟨(r, j + 1), hr⟩ < T ⟨(r, j), hl⟩)
    (g : supportedPermutationSubgroup (garnirBelt μ r j))
    (hg : g ∈ garnirMixingPermutations μ r j) :
    (∑ a ∈ garnirLeft μ r j, (T (g.val a)).val) <
      ∑ a ∈ garnirLeft μ r j, (T a).val := by
  rw [← Finset.sum_image (f := fun a => (T a).val) g.val.injective.injOn]
  apply finset_sum_lt_of_equal_card_exchange
  · exact Finset.card_image_of_injective _ g.val.injective
  · exact garnir_mixing_image_left_ne μ r j g hg
  · intro a ha b hb
    exact garnir_labels_separated μ T hT r j hl hr hinv b a
      (Finset.mem_sdiff.mp hb).1 (garnir_image_left_sdiff_mem_right μ r j g a ha)

end
end ModifiedCartan


