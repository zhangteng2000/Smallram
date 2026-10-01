import ModifiedCartan.KPGaudinMembership
import ModifiedCartan.GaudinCyclicity

open scoped BigOperators Classical MonoidAlgebra Topology

namespace ModifiedCartan
noncomputable section

variable {N : ℕ}

theorem gaudinDegenerationCombination_mem_generated (z w : Fin N → ℂ) (t : ℂ)
    (ht : t ≠ 0) (hz : Function.Injective (gaudinDeformedParameters z t)) :
    gaudinDegenerationCombination z w t ∈ kpGeneratedAlgebra (gaudinDeformedParameters z t) := by
  apply Subalgebra.sum_mem
  intro i hi
  apply Subalgebra.smul_mem
  rw [gaudinDegenerationElement_eq z i t ht]
  exact (kpGeneratedAlgebra _).smul_mem (kpGaudin_mem_generated _ hz i) _

/-- The actual generated algebra contains an actual cyclic operator on each
Specht module throughout a punctured neighborhood of the JM degeneration. -/
theorem specht_eventually_generated_cyclic (τ : YoungDiagram)
    (h : Fintype.card (Fin N) = partitionSize τ) (z : Fin N → ℂ) :
    ∃ (w : Fin N → ℂ) (v : YoungSpechtModule τ), ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 →
      gaudinDegenerationCombination z w t ∈ kpGeneratedAlgebra (gaudinDeformedParameters z t) ∧
      HasPolynomialCyclicVector ((spechtRepresentationOn τ h).asAlgebraHom
        (gaudinDegenerationCombination z w t)) v := by
  obtain ⟨w, v, hv⟩ := specht_eventually_cyclic_gaudin_combination τ h z
  refine ⟨w, v, ?_⟩
  filter_upwards [hv, gaudinDegenerationDenominator_eventually_ne_zero z] with t hcyc hD
  intro ht
  exact ⟨gaudinDegenerationCombination_mem_generated z w t ht
    (gaudinDeformedParameters_injective z t ht hD), hcyc⟩

end
end ModifiedCartan


