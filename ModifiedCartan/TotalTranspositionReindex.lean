import ModifiedCartan.YoungTranspositionScalar
import ModifiedCartan.SpechtFiniteAlphabetRepresentation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem permCongr_swap {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (i j : A) : e.permCongr (Equiv.swap i j) = Equiv.swap (e i) (e j) := by
  apply Equiv.ext
  intro x
  rw [Equiv.permCongr_apply]
  rw [← e.injective.swap_apply, e.apply_symm_apply]

theorem totalTranspositionOperator_reindex {A B V : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm B) V) (e : A ≃ B) :
    totalTranspositionOperator (ρ.comp e.permCongrHom.toMonoidHom) = totalTranspositionOperator ρ := by
  rw [totalTranspositionOperator_eq_sum, totalTranspositionOperator_eq_sum]
  congr 1
  change (∑ i : A, ∑ j : A, if i = j then 0 else ρ (e.permCongr (Equiv.swap i j))) = _
  simp_rw [permCongr_swap]
  calc
    _ = ∑ i : A, ∑ j : A, if e i = e j then 0 else ρ (Equiv.swap (e i) (e j)) := by
      simp only [e.injective.eq_iff]
    _ = ∑ i : A, ∑ j : B, if e i = j then 0 else ρ (Equiv.swap (e i) j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp e (fun j => if e i = j then 0 else ρ (Equiv.swap (e i) j))
    _ = _ := Equiv.sum_comp e (fun i => ∑ j : B, if i = j then 0 else ρ (Equiv.swap i j))

theorem specht_totalTransposition_scalar (μ : YoungDiagram) :
    totalTranspositionOperator (spechtRepresentation μ) =
      youngTranspositionScalar μ • (1 : Module.End ℂ (YoungSpechtModule μ)) := by
  rw [spechtRepresentation, totalTranspositionOperator_reindex, young_totalTransposition_scalar]

theorem spechtRepresentationOn_totalTransposition_scalar {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) :
    totalTranspositionOperator (spechtRepresentationOn μ h) =
      youngTranspositionScalar μ • (1 : Module.End ℂ (YoungSpechtModule μ)) := by
  rw [spechtRepresentationOn, totalTranspositionOperator_reindex, specht_totalTransposition_scalar]

end
end ModifiedCartan


