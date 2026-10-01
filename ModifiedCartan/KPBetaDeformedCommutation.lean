import ModifiedCartan.GaudinCyclicity

open scoped BigOperators Classical MonoidAlgebra Topology

namespace ModifiedCartan
noncomputable section

theorem kpBeta_commutes_gaudinDegenerationCombination {N : ℕ}
    (μ : YoungDiagram) (z w : Fin N → ℂ) (a t : ℂ) (ht : t ≠ 0)
    (hz : Function.Injective (gaudinDeformedParameters z t)) :
    Commute (kpBeta μ (gaudinDeformedParameters z t) a) (gaudinDegenerationCombination z w t) := by
  apply Commute.sum_right Finset.univ
  intro i _
  apply Commute.smul_right
  rw [gaudinDegenerationElement_eq z i t ht]
  apply Commute.smul_right
  exact (kpGaudin_commutes_kpBeta μ (gaudinDeformedParameters z t) hz a i).symm

/-- Actual beta operators commute on every Specht module along the deformed
parameter curve in a punctured neighborhood of the JM degeneration. -/
theorem specht_kpBeta_deformed_eventually_commute {N : ℕ}
    (τ : YoungDiagram) (h : Fintype.card (Fin N) = partitionSize τ) (z : Fin N → ℂ)
    (μ ν : YoungDiagram) (a b : ℂ) :
    ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 →
      Commute ((spechtRepresentationOn τ h).asAlgebraHom (kpBeta μ (gaudinDeformedParameters z t) a))
        ((spechtRepresentationOn τ h).asAlgebraHom (kpBeta ν (gaudinDeformedParameters z t) b)) := by
  obtain ⟨w, v, hv⟩ := specht_eventually_cyclic_gaudin_combination τ h z
  filter_upwards [hv, gaudinDegenerationDenominator_eventually_ne_zero z] with t hcyc hD
  intro ht
  have hz := gaudinDeformedParameters_injective z t ht hD
  apply centralizer_commutative_of_cyclic _ v hcyc
  · exact (kpBeta_commutes_gaudinDegenerationCombination μ z w a t ht hz).map
      (spechtRepresentationOn τ h).asAlgebraHom
  · exact (kpBeta_commutes_gaudinDegenerationCombination ν z w b t ht hz).map
      (spechtRepresentationOn τ h).asAlgebraHom

end
end ModifiedCartan



