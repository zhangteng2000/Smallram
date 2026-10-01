import ModifiedCartan.RowFiltrationRelabel
import ModifiedCartan.RemovalSigns

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- Transport of a point stabilizer by an actual relabeling permutation. -/
def youngLetterStabilizerConjugate (μ : YoungDiagram) (a b : YoungBoxes μ)
    (u : Equiv.Perm (YoungBoxes μ)) (hu : u a = b) :
    youngLetterStabilizer μ a →* youngLetterStabilizer μ b where
  toFun g := ⟨u * g.val * u⁻¹, by
    apply (mem_youngLetterStabilizer_iff μ b _).mpr
    have hi : u⁻¹ b = a := by rw [← hu]; exact u.symm_apply_apply a
    change u (g.val (u⁻¹ b)) = b
    rw [hi, youngLetterStabilizer_fixes]
    exact hu⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [mul_assoc])

/-- The row-cutoff relabeling equivalence intertwines the two stabilizer actions. -/
def youngSpechtRowFiltrationRelabelEquiv (μ : YoungDiagram) (a b : YoungBoxes μ)
    (u : Equiv.Perm (YoungBoxes μ)) (hu : u a = b) (r : ℕ) :
    (youngSpechtRowFiltration μ a r).toRepresentation.Equiv
      ((youngSpechtRowFiltration μ b r).toRepresentation.comp
        (youngLetterStabilizerConjugate μ a b u hu)) :=
  Representation.Equiv.mk (youngSpechtRowFiltrationRelabel μ a b u hu r) (by
    intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change youngTabloidRepresentation μ u (youngTabloidRepresentation μ g.val v.val) =
      youngTabloidRepresentation μ (u * g.val * u⁻¹) (youngTabloidRepresentation μ u v.val)
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one])

theorem youngSpechtRowFiltration_character_relabel (μ : YoungDiagram) (a b : YoungBoxes μ)
    (u : Equiv.Perm (YoungBoxes μ)) (hu : u a = b) (r : ℕ)
    (g : youngLetterStabilizer μ a) :
    (youngSpechtRowFiltration μ a r).toRepresentation.character g =
      (youngSpechtRowFiltration μ b r).toRepresentation.character
        (youngLetterStabilizerConjugate μ a b u hu g) :=
  congrFun (Representation.char_iso (youngSpechtRowFiltrationRelabelEquiv μ a b u hu r)) g

end
end ModifiedCartan


