import ModifiedCartan.YoungColumns

open scoped Classical

namespace ModifiedCartan
noncomputable section

def youngColumnPermutation (μ : YoungDiagram) (c : youngColumnSubgroup μ)
    (j : Fin (μ.rowLen 0)) : Equiv.Perm (Fin (μ.colLen j.val)) :=
  ((youngColumnEquiv μ j).trans (Equiv.subtypeEquiv c.val (fun a => by
    have hc : youngColumnIndex μ (c.val a) = youngColumnIndex μ a := Fin.ext (c.property a)
    rw [hc]))).trans (youngColumnEquiv μ j).symm

theorem youngColumnPermutation_apply_val (μ : YoungDiagram) (c : youngColumnSubgroup μ)
    (j : Fin (μ.rowLen 0)) (r : Fin (μ.colLen j.val)) :
    (youngColumnPermutation μ c j r).val = (c.val ((youngColumnEquiv μ j r).val)).val.1 := rfl

theorem youngColumn_eq_one_of_restrictions (μ : YoungDiagram) (c : youngColumnSubgroup μ)
    (h : ∀ j : Fin (μ.rowLen 0), youngColumnPermutation μ c j = 1) : c = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro b
  apply Subtype.ext
  apply Prod.ext
  · let j := youngColumnIndex μ b
    let r := (youngColumnEquiv μ j).symm ⟨b, rfl⟩
    have hr := congrArg (fun σ : Equiv.Perm (Fin (μ.colLen j.val)) => (σ r).val) (h j)
    change (c.val ((youngColumnEquiv μ j r).val)).val.1 = r.val at hr
    have hv : r.val = b.val.1 := rfl
    have hb : (youngColumnEquiv μ j r).val = b :=
      congrArg (fun x : YoungColumnBoxes μ j => x.val)
        ((youngColumnEquiv μ j).apply_symm_apply ⟨b, rfl⟩)
    rw [hv, hb] at hr
    exact hr
  · exact c.property b

theorem youngColumn_exists_nontrivial_restriction (μ : YoungDiagram)
    (c : youngColumnSubgroup μ) (hc : c ≠ 1) :
    ∃ j : Fin (μ.rowLen 0), youngColumnPermutation μ c j ≠ 1 := by
  by_contra h
  push Not at h
  exact hc (youngColumn_eq_one_of_restrictions μ c h)

end
end ModifiedCartan


