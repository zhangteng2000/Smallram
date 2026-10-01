import ModifiedCartan.IntertwinerAlgebraAction
import ModifiedCartan.SpechtProjectorCompleteness

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem isotypic_le_ker_of_asAlgebraHom_eq_zero {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (x : ℂ[G])
    (hx : ρ.asAlgebraHom x = 0) :
    representationIsotypicSubmodule ρ σ ≤ LinearMap.ker (σ.asAlgebraHom x) := by
  apply iSup_le
  intro F
  rintro _ ⟨v, rfl⟩
  change σ.asAlgebraHom x (F v) = 0
  rw [intertwiner_asAlgebraHom_apply ρ σ F x v, hx, LinearMap.zero_apply, map_zero]

theorem asAlgebraHom_eq_zero_of_all_specht_eq_zero {A W : Type*}
    [Fintype A] [DecidableEq A] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Equiv.Perm A) W) (x : ℂ[Equiv.Perm A])
    (hx : ∀ μ : SizedYoungDiagram (Fintype.card A),
      (sizedSpechtRepresentation μ).asAlgebraHom x = 0) : σ.asAlgebraHom x = 0 := by
  apply LinearMap.ext
  intro v
  have hv : (∑ μ : SizedYoungDiagram (Fintype.card A),
      characterProjector (sizedSpechtRepresentation μ) σ v) = v := by
    have he := congrArg (fun T : Module.End ℂ W => T v) (sum_spechtProjector σ)
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using he
  change σ.asAlgebraHom x v = 0
  rw [← hv, map_sum]
  apply Finset.sum_eq_zero
  intro μ _
  letI := spechtRepresentationOn_irreducible μ.val μ.property.symm (A := A)
  exact isotypic_le_ker_of_asAlgebraHom_eq_zero (sizedSpechtRepresentation μ) σ x (hx μ)
    (characterProjector_apply_mem_isotypic (sizedSpechtRepresentation μ) σ v)

end
end ModifiedCartan


