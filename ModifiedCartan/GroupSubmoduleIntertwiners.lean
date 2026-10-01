import ModifiedCartan.CharacterSimpleGeneration
import Mathlib.RepresentationTheory.Irreducible

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {G W : Type*} [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]

/-- The inclusion of a group-algebra submodule as an equivariant complex linear map. -/
def groupSubmoduleIntertwiner (σ : Representation ℂ G W) (S : Submodule ℂ[G] σ.asModule) :
    Representation.IntertwiningMap (Representation.ofModule (k := ℂ) (G := G) S) σ where
  toLinearMap :=
    { toFun := fun v => σ.asModuleEquiv ((RestrictScalars.addEquiv ℂ ℂ[G] S v).val)
      map_add' := by intro v w; rfl
      map_smul' := by
        intro c v
        change σ.asModuleEquiv ((algebraMap ℂ ℂ[G] c) •
          (RestrictScalars.addEquiv ℂ ℂ[G] S v).val) = _
        rw [IsScalarTower.algebraMap_smul, map_smul]
        rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change σ.asModuleEquiv ((Representation.ofModule (k := ℂ) (G := G) S g v : S).val) =
      σ g (σ.asModuleEquiv ((RestrictScalars.addEquiv ℂ ℂ[G] S v).val))
    simp only [Representation.ofModule, MonoidAlgebra.lift_symm_apply,
      RestrictScalars.lsmul_apply_apply]
    change σ.asModuleEquiv (MonoidAlgebra.single g (1 : ℂ) •
      (RestrictScalars.addEquiv ℂ ℂ[G] S v).val) = _
    rw [Representation.single_smul, one_smul]
    rfl

theorem groupSubmoduleIntertwiner_apply (σ : Representation ℂ G W)
    (S : Submodule ℂ[G] σ.asModule) (v : RestrictScalars ℂ ℂ[G] S) :
    groupSubmoduleIntertwiner σ S v =
      σ.asModuleEquiv (RestrictScalars.addEquiv ℂ ℂ[G] S v).val := rfl

theorem groupSubmoduleIntertwiner_injective (σ : Representation ℂ G W)
    (S : Submodule ℂ[G] σ.asModule) : Function.Injective (groupSubmoduleIntertwiner σ S) := by
  intro v w h
  apply (RestrictScalars.addEquiv ℂ ℂ[G] S).injective
  apply Subtype.ext
  exact σ.asModuleEquiv.injective h

set_option backward.isDefEq.respectTransparency false in
theorem groupSubmoduleRepresentationFinite [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (S : Submodule ℂ[G] σ.asModule) :
    FiniteDimensional ℂ (RestrictScalars ℂ ℂ[G] S) :=
  Module.Finite.of_injective (groupSubmoduleIntertwiner σ S).toLinearMap
    (groupSubmoduleIntertwiner_injective σ S)

set_option backward.isDefEq.respectTransparency false in
theorem groupSubmoduleRepresentationIrreducible (σ : Representation ℂ G W)
    (S : Submodule ℂ[G] σ.asModule) [IsSimpleModule ℂ[G] S] :
    Representation.IsIrreducible (Representation.ofModule (k := ℂ) (G := G) S) :=
  (Representation.isSimpleModule_iff_irreducible_ofModule S).mp inferInstance

end
end ModifiedCartan


