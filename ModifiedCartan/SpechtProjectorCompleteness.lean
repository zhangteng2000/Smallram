import ModifiedCartan.SpechtRegularCompleteness
import Mathlib.RepresentationTheory.Equiv

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A W : Type*} [Fintype A] [DecidableEq A]
  [AddCommGroup W] [Module ℂ W]

/-- Exhaustiveness transported from the regular representation to an actual
representation by its cyclic-vector intertwiner. -/
theorem sum_spechtProjector (τ : Representation ℂ (Equiv.Perm A) W) :
    (∑ μ : SizedYoungDiagram (Fintype.card A),
      characterProjector (sizedSpechtRepresentation μ) τ) = 1 := by
  apply LinearMap.ext
  intro v
  let R := Representation.leftRegular ℂ (Equiv.Perm A)
  let f := (Representation.leftRegularMapEquiv τ).symm v
  have hf : f (MonoidAlgebra.single 1 1) = v := by
    simpa only [map_one, Module.End.one_apply] using
      Representation.leftRegularMapEquiv_symm_single τ (1 : Equiv.Perm A) v
  have hn (μ : SizedYoungDiagram (Fintype.card A)) :
      characterProjector (sizedSpechtRepresentation μ) τ v =
        f (characterProjector (sizedSpechtRepresentation μ) R (MonoidAlgebra.single 1 1)) := by
    have h := congrArg (fun L : ℂ[Equiv.Perm A] →ₗ[ℂ] W => L (MonoidAlgebra.single 1 1))
      (characterProjector_natural (sizedSpechtRepresentation μ) R τ f)
    simpa only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply, hf] using h
  change (∑ μ : SizedYoungDiagram (Fintype.card A),
    characterProjector (sizedSpechtRepresentation μ) τ) v = v
  rw [LinearMap.sum_apply]
  simp_rw [hn]
  rw [← map_sum]
  have hp := congrArg (fun L : Module.End ℂ ℂ[Equiv.Perm A] => L (MonoidAlgebra.single 1 1))
    (sum_spechtProjector_regular (A := A))
  rw [LinearMap.sum_apply, Module.End.one_apply] at hp
  change f (∑ μ : SizedYoungDiagram (Fintype.card A),
    characterProjector (sizedSpechtRepresentation μ) (Representation.leftRegular ℂ (Equiv.Perm A))
      (MonoidAlgebra.single 1 1)) = v
  rw [hp]
  exact hf

end
end ModifiedCartan


