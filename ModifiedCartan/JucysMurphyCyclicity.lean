import ModifiedCartan.JucysMurphyEigenbasis
import ModifiedCartan.JointEigenbasisCyclic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- An actual linear combination of the Jucys--Murphy elements acts cyclically
on every constructed Specht representation. All spectral premises are proved. -/
theorem specht_exists_cyclic_jucysMurphy_combination {A : Type*} [Fintype A] [LinearOrder A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) :
    ∃ (t : A → ℂ) (v : YoungSpechtModule μ), HasPolynomialCyclicVector
      ((spechtRepresentationOn μ h).asAlgebraHom (∑ i : A, t i • jucysMurphyElement i)) v := by
  let D := simpleJucysMurphyBasis μ h
  obtain ⟨t, ht⟩ := exists_cyclic_linearCombination_of_joint_eigenbasis D.basis
    (fun i => (spechtRepresentationOn μ h).asAlgebraHom (jucysMurphyElement i))
    D.values D.values_injective D.eigen
  refine ⟨t, ∑ s : StandardYoungTableau μ, D.basis s, ?_⟩
  simpa only [map_sum, map_smul] using ht

end
end ModifiedCartan


