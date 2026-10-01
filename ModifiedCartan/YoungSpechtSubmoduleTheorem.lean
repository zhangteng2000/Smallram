import ModifiedCartan.YoungAlternatingHermitian
import ModifiedCartan.YoungAlternatingRange

open scoped BigOperators Classical MonoidAlgebra ComplexConjugate

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

/-- The scalar in column antisymmetrization is the inner product with the polytabloid. -/
theorem youngColumnAlternatingOperator_eq_inner_smul (μ : YoungDiagram)
    (v : YoungPermutationModule μ) :
    youngColumnAlternatingOperator μ v = inner ℂ (youngPolytabloid μ) v • youngPolytabloid μ := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (youngColumnAlternatingOperator_apply_mem_line μ v)
  have hc : inner ℂ (youngPolytabloid μ) v = a := by
    calc
      _ = inner ℂ (youngColumnAlternatingOperator μ
          (MonoidAlgebra.single (youngTabloid μ 1) 1)) v := by
        rw [youngColumnAlternatingOperator_identity]
      _ = inner ℂ (MonoidAlgebra.single (youngTabloid μ 1) 1)
          (youngColumnAlternatingOperator μ v) := youngColumnAlternatingOperator_inner μ _ _
      _ = a := by
        rw [← ha, inner_smul_right, youngTabloid_inner_single_left,
          youngPolytabloid_identity_coefficient, mul_one]
  rw [hc]
  exact ha.symm

/-- The classical Specht submodule theorem for the actual tabloid module. -/
theorem young_specht_submodule_theorem (μ : YoungDiagram)
    (U : Subrepresentation (youngTabloidRepresentation μ)) :
    youngSpechtSubrepresentation μ ≤ U ∨
      U.toSubmodule ≤ (youngSpechtSubrepresentation μ).toSubmoduleᗮ := by
  by_cases h : ∀ u : YoungPermutationModule μ, u ∈ U → inner ℂ (youngPolytabloid μ) u = 0
  · right
    intro u hu
    apply ((youngSpechtSubrepresentation μ).toSubmodule.mem_orthogonal u).mpr
    intro v hv
    change v ∈ Submodule.span ℂ
      (Set.range fun g => youngTabloidRepresentation μ g (youngPolytabloid μ)) at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [unitary_inner_action_left _ (youngTabloidRepresentation_unitary μ)]
      exact h _ (U.apply_mem_toSubmodule g⁻¹ hu)
    | zero => simp
    | add x y hx hy h1 h2 => simp [inner_add_left, h1, h2]
    | smul a x hx ih => simp [inner_smul_left, ih]
  · push Not at h
    obtain ⟨u, hu, hne⟩ := h
    left
    apply (representationOrbitSpan_le_iff (youngTabloidRepresentation μ) (youngPolytabloid μ) U).mpr
    have hv := youngColumnAlternatingOperator_mem_subrepresentation μ U hu
    rw [youngColumnAlternatingOperator_eq_inner_smul] at hv
    have hs := U.toSubmodule.smul_mem (inner ℂ (youngPolytabloid μ) u)⁻¹ hv
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hs

end
end ModifiedCartan


