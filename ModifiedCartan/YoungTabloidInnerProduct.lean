import ModifiedCartan.YoungPolytabloid
import ModifiedCartan.CharacterOrthogonalInvariant
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators Classical MonoidAlgebra ComplexConjugate

namespace ModifiedCartan
noncomputable section

/-- Coefficients in the tabloid basis, viewed in Euclidean space. -/
def youngTabloidEuclideanEquiv (μ : YoungDiagram) :
    YoungPermutationModule μ ≃ₗ[ℂ] EuclideanSpace ℂ (YoungTabloid μ) :=
  ((MonoidAlgebra.coeffLinearEquiv ℂ).trans
    (Finsupp.linearEquivFunOnFinite ℂ ℂ (YoungTabloid μ))).trans
    (WithLp.linearEquiv 2 ℂ (YoungTabloid μ → ℂ)).symm

@[simp] theorem youngTabloidEuclideanEquiv_apply (μ : YoungDiagram)
    (v : YoungPermutationModule μ) (t : YoungTabloid μ) :
    youngTabloidEuclideanEquiv μ v t = v.coeff t := rfl

/-- The norm for which the tabloid basis is orthonormal. -/
abbrev youngPermutationModuleNormed (μ : YoungDiagram) : NormedAddCommGroup (YoungPermutationModule μ) :=
  NormedAddCommGroup.induced _ _ (youngTabloidEuclideanEquiv μ)
    (youngTabloidEuclideanEquiv μ).injective

attribute [local instance] youngPermutationModuleNormed

/-- The positive definite Hermitian inner product in the tabloid basis. -/
abbrev youngPermutationModuleInner (μ : YoungDiagram) : InnerProductSpace ℂ (YoungPermutationModule μ) :=
  InnerProductSpace.induced (youngTabloidEuclideanEquiv μ).toLinearMap

attribute [local instance] youngPermutationModuleInner

theorem youngTabloid_inner_formula (μ : YoungDiagram) (v w : YoungPermutationModule μ) :
    inner ℂ v w = ∑ t : YoungTabloid μ, conj (v.coeff t) * w.coeff t := by
  change inner ℂ (youngTabloidEuclideanEquiv μ v) (youngTabloidEuclideanEquiv μ w) = _
  simp only [PiLp.inner_apply, RCLike.inner_apply', youngTabloidEuclideanEquiv_apply]

theorem youngTabloid_inner_single_left (μ : YoungDiagram) (t : YoungTabloid μ)
    (v : YoungPermutationModule μ) : inner ℂ (MonoidAlgebra.single t 1) v = v.coeff t := by
  rw [youngTabloid_inner_formula]
  simp [Finsupp.single_apply]

/-- Permuting the tabloid orthonormal basis is unitary. -/
theorem youngTabloidRepresentation_unitary (μ : YoungDiagram) :
    IsUnitaryRepresentation (youngTabloidRepresentation μ) := by
  intro g v w
  rw [youngTabloid_inner_formula, youngTabloid_inner_formula]
  simp only [youngTabloidRepresentation, Representation.coeff_ofMulAction]
  let e : Equiv.Perm (YoungTabloid μ) :=
    { toFun := fun t => g⁻¹ • t
      invFun := fun t => g • t
      left_inv := by intro t; simp
      right_inv := by intro t; simp }
  exact Equiv.sum_comp e (fun t => conj (v.coeff t) * w.coeff t)

end
end ModifiedCartan


