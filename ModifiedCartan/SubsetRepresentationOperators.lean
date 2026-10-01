import ModifiedCartan.TotalTranspositionDeletion
import ModifiedCartan.SpechtRestrictionMultiplicity
import ModifiedCartan.TotalTranspositionOperator

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A V : Type*} [Fintype A] [DecidableEq A] [AddCommGroup V] [Module ℂ V]

theorem asAlgebraHom_subsetExtension (ρ : Representation ℂ (Equiv.Perm A) V)
    (I : Finset A) (x : ℂ[Equiv.Perm I]) :
    ρ.asAlgebraHom (kpSubsetExtension I x) =
      Representation.asAlgebraHom (ρ.comp (subsetPermutationInclusion I)) x := by
  induction x using MonoidAlgebra.induction_on with
  | of p =>
    change ρ.asAlgebraHom (kpSubsetExtension I (MonoidAlgebra.single p 1)) =
      Representation.asAlgebraHom (ρ.comp (subsetPermutationInclusion I)) (MonoidAlgebra.single p 1)
    simp only [kpSubsetExtension, MonoidAlgebra.mapDomainLinearMap_single,
      Representation.asAlgebraHom_single_one]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]

theorem totalTranspositionOperator_delete (ρ : Representation ℂ (Equiv.Perm A) V) (a : A) :
    totalTranspositionOperator ρ =
      totalTranspositionOperator (ρ.comp (subsetPermutationInclusion (Finset.univ.erase a))) +
        ρ.asAlgebraHom (permutationStar (Finset.univ.erase a) a) := by
  rw [totalTranspositionOperator, totalTranspositionElement_delete a, map_add,
    asAlgebraHom_subsetExtension]
  rfl

end
end ModifiedCartan


