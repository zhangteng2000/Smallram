import ModifiedCartan.ClassFunctionOperator

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def classFunctionScalar (f : G → ℂ) (ρ : Representation ℂ G V) : ℂ :=
  (∑ g : G, f g⁻¹ * ρ.character g) / (Module.finrank ℂ V : ℂ)

theorem classFunctionOperator_trace (f : G → ℂ) (ρ : Representation ℂ G V) :
    LinearMap.trace ℂ V (classFunctionOperator f ρ) = ∑ g : G, f g⁻¹ * ρ.character g := by
  simp only [classFunctionOperator, map_sum, map_smul, smul_eq_mul, Representation.character]

theorem exists_scalar_classFunctionOperator (f : G → ℂ) (hf : IsConjugacyInvariant f)
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    ∃ c : ℂ, classFunctionOperator f ρ = c • (1 : Module.End ℂ V) := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (classFunctionIntertwiner f hf ρ)
  refine ⟨c, ?_⟩
  exact (congrArg (fun F : Representation.IntertwiningMap ρ ρ => F.toLinearMap) hc).symm

theorem classFunctionOperator_on_irreducible (f : G → ℂ) (hf : IsConjugacyInvariant f)
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    classFunctionOperator f ρ = classFunctionScalar f ρ • (1 : Module.End ℂ V) := by
  obtain ⟨c, hc⟩ := exists_scalar_classFunctionOperator f hf ρ
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast irreducible_finrank_ne_zero ρ
  have ht := congrArg (LinearMap.trace ℂ V) hc
  rw [classFunctionOperator_trace, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  have he : c = classFunctionScalar f ρ := (eq_div_iff hd).mpr ht.symm
  rw [hc, he]

end
end ModifiedCartan

