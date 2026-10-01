import ModifiedCartan.YoungPolytabloid

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- The smallest invariant subspace containing an actual vector. -/
def representationOrbitSpan {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g v)
  apply_mem_toSubmodule g := by
    intro w hw
    have hle : Submodule.span ℂ (Set.range fun h => ρ h v) ≤
        (Submodule.span ℂ (Set.range fun h => ρ h v)).comap (ρ g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨h, rfl⟩
      change ρ g (ρ h v) ∈ Submodule.span ℂ (Set.range fun h => ρ h v)
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    exact hle hw

theorem mem_representationOrbitSpan {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) : v ∈ representationOrbitSpan ρ v := by
  change v ∈ Submodule.span ℂ (Set.range fun g => ρ g v)
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

theorem representationOrbitSpan_le_iff {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (S : Subrepresentation ρ) :
    representationOrbitSpan ρ v ≤ S ↔ v ∈ S := by
  constructor
  · intro h
    exact h (mem_representationOrbitSpan ρ v)
  · intro hv
    change Submodule.span ℂ (Set.range fun g => ρ g v) ≤ S.toSubmodule
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact S.apply_mem_toSubmodule g hv

/-- The actual polytabloid Specht module for the diagram, as an invariant subspace. -/
def youngSpechtSubrepresentation (μ : YoungDiagram) :
    Subrepresentation (youngTabloidRepresentation μ) :=
  representationOrbitSpan (youngTabloidRepresentation μ) (youngPolytabloid μ)

abbrev YoungSpechtModule (μ : YoungDiagram) := (youngSpechtSubrepresentation μ).toSubmodule

def youngSpechtRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (YoungBoxes μ)) (YoungSpechtModule μ) :=
  (youngSpechtSubrepresentation μ).toRepresentation

theorem youngPolytabloid_mem_specht (μ : YoungDiagram) :
    youngPolytabloid μ ∈ youngSpechtSubrepresentation μ :=
  mem_representationOrbitSpan _ _

theorem youngSpechtSubrepresentation_ne_bot (μ : YoungDiagram) :
    youngSpechtSubrepresentation μ ≠ ⊥ := by
  intro h
  have hm := youngPolytabloid_mem_specht μ
  rw [h] at hm
  exact youngPolytabloid_ne_zero μ hm

instance (μ : YoungDiagram) : FiniteDimensional ℂ (YoungSpechtModule μ) := by
  unfold YoungSpechtModule
  infer_instance

end
end ModifiedCartan


