import ModifiedCartan.SpechtRowFiltration

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngSpechtRowFiltration_action_mem (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : Equiv.Perm (YoungBoxes μ)) (r : ℕ) (v : YoungPermutationModule μ)
    (hv : v ∈ youngSpechtRowFiltration μ a r) :
    youngTabloidRepresentation μ g v ∈ youngSpechtRowFiltration μ (g a) r := by
  refine ⟨(youngSpechtSubrepresentation μ).apply_mem_toSubmodule g hv.1, ?_⟩
  intro t ht
  rw [youngTabloidRepresentation, Representation.coeff_ofMulAction]
  apply hv.2
  rw [youngTabloidRows_smul, inv_inv]
  exact ht

/-- Relabeling the fixed letter gives an actual linear equivalence of the
corresponding Specht row cutoffs. -/
def youngSpechtRowFiltrationRelabel (μ : YoungDiagram) (a b : YoungBoxes μ)
    (g : Equiv.Perm (YoungBoxes μ)) (hg : g a = b) (r : ℕ) :
    (youngSpechtRowFiltration μ a r).toSubmodule ≃ₗ[ℂ]
      (youngSpechtRowFiltration μ b r).toSubmodule where
  toFun v := ⟨youngTabloidRepresentation μ g v.val, by
    rw [← hg]
    exact youngSpechtRowFiltration_action_mem μ a g r v.val v.property⟩
  invFun v := ⟨youngTabloidRepresentation μ g⁻¹ v.val, by
    have hgi : g⁻¹ b = a := by rw [← hg]; exact g.symm_apply_apply a
    rw [← hgi]
    exact youngSpechtRowFiltration_action_mem μ b g⁻¹ r v.val v.property⟩
  left_inv v := by
    apply Subtype.ext
    change youngTabloidRepresentation μ g⁻¹ (youngTabloidRepresentation μ g v.val) = v.val
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    apply Subtype.ext
    change youngTabloidRepresentation μ g (youngTabloidRepresentation μ g⁻¹ v.val) = v.val
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_add' v w := Subtype.ext (map_add (youngTabloidRepresentation μ g) v.val w.val)
  map_smul' z v := Subtype.ext (map_smul (youngTabloidRepresentation μ g) z v.val)

theorem youngSpechtRowFiltration_finrank_letter_independent (μ : YoungDiagram)
    (a b : YoungBoxes μ) (r : ℕ) :
    Module.finrank ℂ (youngSpechtRowFiltration μ a r).toSubmodule =
      Module.finrank ℂ (youngSpechtRowFiltration μ b r).toSubmodule :=
  (youngSpechtRowFiltrationRelabel μ a b (Equiv.swap a b) (Equiv.swap_apply_left a b) r).finrank_eq

end
end ModifiedCartan


