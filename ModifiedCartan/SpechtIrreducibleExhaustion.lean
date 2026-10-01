import ModifiedCartan.SpechtProjectorCompleteness

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Every actual finite-dimensional complex irreducible representation of a
finite symmetric group is equivalent to one of the constructed Specht modules. -/
theorem exists_spechtRepresentationOn_equiv {A W : Type*} [Fintype A] [DecidableEq A]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ (Equiv.Perm A) W) [Representation.IsIrreducible τ] :
    ∃ μ : SizedYoungDiagram (Fintype.card A), Nonempty (Representation.Equiv (sizedSpechtRepresentation μ) τ) := by
  by_contra h
  have hp (μ : SizedYoungDiagram (Fintype.card A)) :
      characterProjector (sizedSpechtRepresentation μ) τ = 0 := by
    let _ := spechtRepresentationOn_irreducible μ.val μ.property.symm (A := A)
    have hn : ¬ Nonempty (Representation.Equiv (sizedSpechtRepresentation μ) τ) := fun he => h ⟨μ, he⟩
    rw [characterProjector_on_irreducible, if_neg hn]
  have he := sum_spechtProjector τ
  simp only [hp, Finset.sum_const_zero] at he
  have ht := congrArg (LinearMap.trace ℂ W) he
  rw [map_zero, LinearMap.trace_one] at ht
  have hd : Module.finrank ℂ W = 0 := by exact_mod_cast ht.symm
  exact irreducible_finrank_ne_zero τ hd

end
end ModifiedCartan


