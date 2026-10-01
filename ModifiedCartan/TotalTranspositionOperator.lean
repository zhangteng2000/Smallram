import ModifiedCartan.TotalTranspositionElement
import ModifiedCartan.ClassWeightedOperator

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A V : Type*} [Fintype A] [DecidableEq A] [AddCommGroup V] [Module ℂ V]

def totalTranspositionOperator (ρ : Representation ℂ (Equiv.Perm A) V) : Module.End ℂ V :=
  ρ.asAlgebraHom (totalTranspositionElement A)

theorem totalTranspositionOperator_eq_sum (ρ : Representation ℂ (Equiv.Perm A) V) :
    totalTranspositionOperator ρ =
      (2 : ℂ)⁻¹ • ∑ i : A, ∑ j : A, if i = j then 0 else ρ (Equiv.swap i j) := by
  simp only [totalTranspositionOperator, totalTranspositionElement, map_smul, map_sum,
    transpositionElement, permutationElement]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = j <;> simp [h, Representation.asAlgebraHom_single_one]

theorem totalTranspositionOperator_commutes (ρ : Representation ℂ (Equiv.Perm A) V)
    (u : Equiv.Perm A) : totalTranspositionOperator ρ * ρ u = ρ u * totalTranspositionOperator ρ := by
  have he := congrArg ρ.asAlgebraHom (totalTranspositionElement_commutes_permutation u)
  simpa only [map_mul, permutationElement, Representation.asAlgebraHom_single_one,
    totalTranspositionOperator] using he.symm

def totalTranspositionIntertwiner (ρ : Representation ℂ (Equiv.Perm A) V) :
    Representation.IntertwiningMap ρ ρ where
  toLinearMap := totalTranspositionOperator ρ
  isIntertwining' u := totalTranspositionOperator_commutes ρ u

theorem exists_totalTransposition_scalar (ρ : Representation ℂ (Equiv.Perm A) V)
    [FiniteDimensional ℂ V] [Representation.IsIrreducible ρ] :
    ∃ c : ℂ, totalTranspositionOperator ρ = c • (1 : Module.End ℂ V) := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (totalTranspositionIntertwiner ρ)
  exact ⟨c, (congrArg (fun L : Representation.IntertwiningMap ρ ρ => L.toLinearMap) hc).symm⟩

theorem totalTranspositionOperator_natural {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Equiv.Perm A) V) (σ : Representation ℂ (Equiv.Perm A) W)
    (L : Representation.IntertwiningMap ρ σ) (v : V) :
    totalTranspositionOperator σ (L v) = L (totalTranspositionOperator ρ v) := by
  simp only [totalTranspositionOperator_eq_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = j
  · simp [h]
  · simp only [ite_eq_right h]
    exact (Representation.IntertwiningMap.isIntertwining ρ σ L (Equiv.swap i j) v).symm

end
end ModifiedCartan


