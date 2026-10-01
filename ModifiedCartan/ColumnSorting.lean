import ModifiedCartan.SortedColumnLabels

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Sort all columns independently, as an actual permutation of the box set. -/
def youngColumnSortPermutation (μ : YoungDiagram) (T : YoungFilling μ) :
    Equiv.Perm (YoungBoxes μ) :=
  Equiv.ofFiberEquiv (f := youngColumnIndex μ) (g := youngColumnIndex μ)
    (fun j => (youngColumnEquiv μ j).symm.trans (youngSortedColumnEquiv μ T j))

theorem youngColumnSortPermutation_mem (μ : YoungDiagram) (T : YoungFilling μ) :
    youngColumnSortPermutation μ T ∈ youngColumnSubgroup μ := by
  intro b
  exact congrArg Fin.val (Equiv.ofFiberEquiv_map
    (fun j => (youngColumnEquiv μ j).symm.trans (youngSortedColumnEquiv μ T j)) b)

theorem youngColumnSortPermutation_apply (μ : YoungDiagram) (T : YoungFilling μ)
    (j : Fin (μ.rowLen 0)) (b : YoungColumnBoxes μ j) :
    youngColumnSortPermutation μ T b.val =
      (youngSortedColumnEquiv μ T j ((youngColumnEquiv μ j).symm b)).val := by
  rcases b with ⟨b, rfl⟩
  rfl

/-- Every bijective filling can be made column standard by permuting positions within columns. -/
theorem youngColumnSort_standard (μ : YoungDiagram) (T : YoungFilling μ) :
    YoungColumnStandard ((youngColumnSortPermutation μ T).trans T) := by
  intro a b hr hc
  let j := youngColumnIndex μ a
  let aa : YoungColumnBoxes μ j := ⟨a, rfl⟩
  let bb : YoungColumnBoxes μ j := ⟨b, by apply Fin.ext; exact hc.symm⟩
  have ha := youngColumnSortPermutation_apply μ T j aa
  have hb := youngColumnSortPermutation_apply μ T j bb
  change T (youngColumnSortPermutation μ T a) < T (youngColumnSortPermutation μ T b)
  rw [ha, hb]
  apply youngSortedColumnEquiv_strict μ T j
  exact hr

end
end ModifiedCartan


