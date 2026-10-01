import ModifiedCartan.IsotypicAnnihilator

open scoped Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem leftRegular_asAlgebraHom_apply_one {G : Type*} [Group G] (x : ℂ[G]) :
    (Representation.leftRegular ℂ G).asAlgebraHom x (MonoidAlgebra.single 1 1) = x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    change (Representation.leftRegular ℂ G).asAlgebraHom (MonoidAlgebra.single g 1)
      (MonoidAlgebra.single 1 1) = MonoidAlgebra.single g 1
    rw [Representation.asAlgebraHom_single_one]
    simp only [Representation.leftRegular, Representation.ofMulAction_single, smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul c x hx => simp only [map_smul, LinearMap.smul_apply, hx]

/-- The family of all constructed Specht actions detects every group-algebra element. -/
theorem eq_zero_of_all_specht_actions_zero {A : Type*} [Fintype A] [DecidableEq A]
    (x : ℂ[Equiv.Perm A])
    (hx : ∀ μ : SizedYoungDiagram (Fintype.card A),
      (sizedSpechtRepresentation μ).asAlgebraHom x = 0) : x = 0 := by
  letI := (MonoidAlgebra.basis (Equiv.Perm A) ℂ).finiteDimensional_of_finite
  have he := asAlgebraHom_eq_zero_of_all_specht_eq_zero (Representation.leftRegular ℂ (Equiv.Perm A)) x hx
  have hv := congrArg (fun T : Module.End ℂ ℂ[Equiv.Perm A] => T (MonoidAlgebra.single 1 1)) he
  simpa only [leftRegular_asAlgebraHom_apply_one, LinearMap.zero_apply] using hv

end
end ModifiedCartan


