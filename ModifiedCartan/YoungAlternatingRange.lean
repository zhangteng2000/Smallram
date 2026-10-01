import ModifiedCartan.YoungTabloidCancellation
import ModifiedCartan.YoungColumnOrbit
import ModifiedCartan.YoungSpechtModule

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- Each tabloid is sent to a scalar multiple of the identity polytabloid. -/
theorem youngColumnAlternatingOperator_single_scalar (μ : YoungDiagram) (t : YoungTabloid μ) :
    ∃ a : ℂ, youngColumnAlternatingOperator μ (MonoidAlgebra.single t 1) = a • youngPolytabloid μ := by
  by_cases ht : ∀ a b : YoungBoxes μ, a.val.2 = b.val.2 →
      youngTabloidRows μ t a = youngTabloidRows μ t b → a = b
  · obtain ⟨c, rfl⟩ := youngTabloid_eq_column_of_injective μ t ht
    refine ⟨youngPermutationSign μ c.val, ?_⟩
    calc
      _ = youngColumnAlternatingOperator μ (youngTabloidRepresentation μ c.val
          (MonoidAlgebra.single (youngTabloid μ 1) 1)) := by
        rw [youngTabloidRepresentation_single, mul_one]
      _ = _ := by rw [youngColumnAlternatingOperator_column_apply,
        youngColumnAlternatingOperator_identity]
  · push_neg at ht
    obtain ⟨a, b, hc, hr, hne⟩ := ht
    refine ⟨0, ?_⟩
    rw [youngColumnAlternatingOperator_kills_collision μ t a b hne hc hr, zero_smul]

theorem youngColumnAlternatingOperator_apply_mem_line (μ : YoungDiagram)
    (v : YoungPermutationModule μ) :
    youngColumnAlternatingOperator μ v ∈ Submodule.span ℂ {youngPolytabloid μ} := by
  induction v using MonoidAlgebra.induction_linear with
  | zero => simp
  | add v w hv hw =>
    rw [map_add]
    exact Submodule.add_mem _ hv hw
  | single t a =>
    obtain ⟨b, hb⟩ := youngColumnAlternatingOperator_single_scalar μ t
    have hs : MonoidAlgebra.single t a = a • MonoidAlgebra.single t 1 := by simp
    rw [hs, map_smul, hb]
    apply Submodule.smul_mem
    apply Submodule.smul_mem
    exact Submodule.mem_span_singleton_self _

/-- The column alternating operator has exactly the polytabloid line as its range. -/
theorem youngColumnAlternatingOperator_range (μ : YoungDiagram) :
    LinearMap.range (youngColumnAlternatingOperator μ) =
      Submodule.span ℂ {youngPolytabloid μ} := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact youngColumnAlternatingOperator_apply_mem_line μ v
  · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact ⟨MonoidAlgebra.single (youngTabloid μ 1) 1, youngColumnAlternatingOperator_identity μ⟩

end
end ModifiedCartan


