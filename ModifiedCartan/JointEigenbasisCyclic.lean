import ModifiedCartan.SimpleEigenbasisCyclic
import ModifiedCartan.FiniteJointSpectrumSeparation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem exists_cyclic_linearCombination_of_joint_eigenbasis {ι J V : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J] [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (T : J → Module.End ℂ V) (e : ι → (J → ℂ))
    (he : Function.Injective e) (hT : ∀ i j, T j (b i) = e i j • b i) :
    ∃ t : J → ℂ, HasPolynomialCyclicVector (∑ j, t j • T j) (∑ i, b i) := by
  obtain ⟨t, ht⟩ := exists_separating_finite_weights e he
  refine ⟨t, hasPolynomialCyclicVector_of_simple_eigenbasis b _ _ ht ?_⟩
  intro i
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, hT, smul_smul, Finset.sum_smul]

end
end ModifiedCartan


