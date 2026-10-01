import ModifiedCartan.CyclicSubalgebra
import ModifiedCartan.KPSpechtAlgebra
import ModifiedCartan.KPGeneratedCyclicity

open scoped BigOperators Classical MonoidAlgebra Topology

namespace ModifiedCartan
noncomputable section

/-- An actual nonempty parameter region where each Specht image is the entire
centralizer of an actual cyclic element, and has its exact tableau dimension. -/
theorem specht_eventually_generated_centralizer {N : ℕ} (τ : YoungDiagram)
    (h : Fintype.card (Fin N) = partitionSize τ) (z : Fin N → ℂ) :
    ∃ w : Fin N → ℂ, ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 →
      kpSpechtAlgebra τ h (gaudinDeformedParameters z t) =
        Subalgebra.centralizer ℂ
          {(spechtRepresentationOn τ h).asAlgebraHom (gaudinDegenerationCombination z w t)} ∧
      Module.finrank ℂ (kpSpechtAlgebra τ h (gaudinDeformedParameters z t)) =
        standardSkewTableauCount τ ⊥ := by
  obtain ⟨w, v, hv⟩ := specht_eventually_generated_cyclic τ h z
  refine ⟨w, ?_⟩
  filter_upwards [hv] with t ht
  intro ht0
  obtain ⟨hmem, hcyc⟩ := ht ht0
  have hT : (spechtRepresentationOn τ h).asAlgebraHom (gaudinDegenerationCombination z w t) ∈
      kpSpechtAlgebra τ h (gaudinDeformedParameters z t) :=
    Subalgebra.mem_map.mpr ⟨_, hmem, rfl⟩
  refine ⟨commutative_subalgebra_eq_centralizer_of_cyclic _
    (kpSpechtAlgebra_elements_commute τ h _) _ hT v hcyc, ?_⟩
  rw [finrank_commutative_subalgebra_of_cyclic _
    (kpSpechtAlgebra_elements_commute τ h _) _ hT v hcyc,
    finrank_specht_eq_standardTableauCount]

end
end ModifiedCartan


