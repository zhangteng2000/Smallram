import ModifiedCartan.YoungAlternatingOperator
import ModifiedCartan.YoungTabloidRows

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem permutationFiberSubgroup_swap_mem {A B : Type*} [DecidableEq A]
    (f : A → B) {a b : A} (hab : f a = f b) :
    Equiv.swap a b ∈ permutationFiberSubgroup f := by
  intro x
  by_cases hxa : x = a
  · subst x
    simpa only [Equiv.swap_apply_left] using hab.symm
  · by_cases hxb : x = b
    · subst x
      simpa only [Equiv.swap_apply_right] using hab
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem young_swap_fixes_tabloid (μ : YoungDiagram) (t : YoungTabloid μ)
    (a b : YoungBoxes μ) (hab : youngTabloidRows μ t a = youngTabloidRows μ t b) :
    Equiv.swap a b • t = t := by
  apply youngTabloidRows_injective μ
  funext x
  rw [youngTabloidRows_smul, Equiv.swap_inv]
  exact permutationFiberSubgroup_swap_mem (youngTabloidRows μ t) hab x

theorem youngPermutationSign_swap (μ : YoungDiagram) (a b : YoungBoxes μ) (hab : a ≠ b) :
    youngPermutationSign μ (Equiv.swap a b) = -1 := by
  change ((Equiv.Perm.sign (Equiv.swap a b) : ℤ) : ℂ) = -1
  rw [Equiv.Perm.sign_swap hab]
  norm_num

/-- Two same-column letters in one row force cancellation of the alternating sum. -/
theorem youngColumnAlternatingOperator_kills_collision (μ : YoungDiagram) (t : YoungTabloid μ)
    (a b : YoungBoxes μ) (hne : a ≠ b) (hc : a.val.2 = b.val.2)
    (hr : youngTabloidRows μ t a = youngTabloidRows μ t b) :
    youngColumnAlternatingOperator μ (MonoidAlgebra.single t 1) = 0 := by
  let d : youngColumnSubgroup μ := ⟨Equiv.swap a b,
    permutationFiberSubgroup_swap_mem (fun c : YoungBoxes μ => c.val.2) hc⟩
  have hd : youngTabloidRepresentation μ d.val (MonoidAlgebra.single t 1) =
      MonoidAlgebra.single t 1 := by
    change Representation.ofMulAction ℂ (Equiv.Perm (YoungBoxes μ)) (YoungTabloid μ)
      (Equiv.swap a b) (MonoidAlgebra.single t 1) = _
    rw [Representation.ofMulAction_single, young_swap_fixes_tabloid μ t a b hr]
  have hs : youngPermutationSign μ d.val = -1 := youngPermutationSign_swap μ a b hne
  have h := youngColumnAlternatingOperator_column_apply μ d (MonoidAlgebra.single t 1)
  rw [hd, hs, neg_one_smul] at h
  let v := youngColumnAlternatingOperator μ (MonoidAlgebra.single t 1)
  have hv : (2 : ℂ) • v = 0 := by
    calc
      _ = v + v := by rw [two_smul]
      _ = v + -v := congrArg (fun w => v + w) h
      _ = 0 := add_neg_cancel v
  exact (smul_eq_zero.mp hv).resolve_left (by norm_num)

end
end ModifiedCartan


