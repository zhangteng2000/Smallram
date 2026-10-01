import ModifiedCartan.GaudinDegenerationElement
import ModifiedCartan.JucysMurphyCyclicity

open scoped BigOperators Classical MonoidAlgebra Topology

namespace ModifiedCartan
noncomputable section

theorem specht_eventually_cyclic_gaudin_combination {N : ℕ}
    (τ : YoungDiagram) (h : Fintype.card (Fin N) = partitionSize τ) (z : Fin N → ℂ) :
    ∃ (w : Fin N → ℂ) (v : YoungSpechtModule τ), ∀ᶠ t in 𝓝 (0 : ℂ),
      HasPolynomialCyclicVector ((spechtRepresentationOn τ h).asAlgebraHom
        (gaudinDegenerationCombination z w t)) v := by
  obtain ⟨w, v, hv⟩ := specht_exists_cyclic_jucysMurphy_combination τ h
  refine ⟨w, v, ?_⟩
  apply eventually_hasPolynomialCyclicVector_of_matrix_continuousAt
    (youngStandardPolytabloidBasis τ)
    (fun t => (spechtRepresentationOn τ h).asAlgebraHom (gaudinDegenerationCombination z w t)) 0 v
    (gaudinDegenerationCombination_matrix_continuousAt_zero _ _ z w)
  simpa only [gaudinDegenerationCombination_zero] using hv

end
end ModifiedCartan



