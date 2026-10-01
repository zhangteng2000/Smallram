import ModifiedCartan.SubsetRepresentationOperators

open scoped Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem intertwiner_asAlgebraHom_apply {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (F : Representation.IntertwiningMap ρ σ) (x : ℂ[G]) (v : V) :
    σ.asAlgebraHom x (F v) = F (ρ.asAlgebraHom x v) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    change σ.asAlgebraHom (MonoidAlgebra.single g 1) (F v) =
      F (ρ.asAlgebraHom (MonoidAlgebra.single g 1) v)
    rw [Representation.asAlgebraHom_single_one, Representation.asAlgebraHom_single_one]
    exact (Representation.IntertwiningMap.isIntertwining ρ σ F g v).symm
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul c x hx => simp only [map_smul, LinearMap.smul_apply, hx]

end
end ModifiedCartan


