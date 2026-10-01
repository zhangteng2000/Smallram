import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Span
import Mathlib.Tactic

open scoped Topology
open Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- The finite-dimensional complex isometry needed for the manuscript's
unitary normalization of the homogeneous vector at zero. -/
theorem exists_linearIsometry_map_of_norm_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {u v : E} (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) :
    ∃ L : E →ₗᵢ[ℂ] E, L u = v := by
  have hv : v ≠ 0 := by
    intro hv
    have hun : ‖u‖ = 0 := by simpa only [hv, norm_zero] using huv
    exact hu (norm_eq_zero.mp hun)
  let eu := LinearEquiv.toSpanNonzeroSingleton ℂ E u hu
  let ev := LinearEquiv.toSpanNonzeroSingleton ℂ E v hv
  let M : (ℂ ∙ u) →ₗ[ℂ] E :=
    (Submodule.subtype (ℂ ∙ v)).comp (ev.toLinearMap.comp eu.symm.toLinearMap)
  have hnorm : ∀ s, ‖M s‖ = ‖s‖ := by
    intro s
    calc
      ‖M s‖ = ‖ev (eu.symm s)‖ := rfl
      _ = ‖v‖ * ‖eu.symm s‖ := LinearEquiv.toSpanNonzeroSingleton_homothety ℂ v hv _
      _ = ‖u‖ * ‖eu.symm s‖ := by rw [huv]
      _ = ‖eu (eu.symm s)‖ := (LinearEquiv.toSpanNonzeroSingleton_homothety ℂ u hu _).symm
      _ = ‖s‖ := by rw [eu.apply_symm_apply]
  let L : (ℂ ∙ u) →ₗᵢ[ℂ] E := { toLinearMap := M, norm_map' := hnorm }
  refine ⟨L.extend, ?_⟩
  have hval : ((eu 1 : ℂ ∙ u) : E) = u := by
    simp only [eu, LinearEquiv.toSpanNonzeroSingleton_apply, one_smul]
  calc
    L.extend u = L.extend (eu 1) := congrArg L.extend hval.symm
    _ = L (eu 1) := L.extend_apply _
    _ = v := by
      change (ev (eu.symm (eu 1)) : E) = v
      rw [eu.symm_apply_apply]
      simp only [ev, LinearEquiv.toSpanNonzeroSingleton_apply, one_smul]

end
end ModifiedCartan
#print axioms ModifiedCartan.exists_linearIsometry_map_of_norm_eq
