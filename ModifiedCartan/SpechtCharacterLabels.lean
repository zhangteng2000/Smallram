import ModifiedCartan.SpechtRepresentation

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- Transporting a symmetric-group character between two labelings gives the same value. -/
theorem permutation_character_label_independent {A B V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm A) V) (e f : B ≃ A) (g : Equiv.Perm B) :
    ρ.character (e.permCongr g) = ρ.character (f.permCongr g) := by
  let u : Equiv.Perm A := f.symm.trans e
  have he : e.permCongr g = u * f.permCongr g * u⁻¹ := by
    ext a
    change e (g (e.symm a)) = e (f.symm (f (g (f.symm (f (e.symm a))))))
    simp
  rw [he, Representation.char_conj]

/-- The actual Specht character on a finite alphabet of the required size.
Its value is independent of the bijection used to number that alphabet. -/
def spechtCharacterOn {A : Type*} [Fintype A] (μ : YoungDiagram)
    (h : Fintype.card A = partitionSize μ) (g : Equiv.Perm A) : ℂ :=
  spechtCharacter μ ((Fintype.equivFinOfCardEq h).permCongr g)

theorem spechtCharacterOn_eq_young {A : Type*} [Fintype A] (μ : YoungDiagram)
    (h : Fintype.card A = partitionSize μ) (e : A ≃ YoungBoxes μ) (g : Equiv.Perm A) :
    spechtCharacterOn μ h g = (youngSpechtRepresentation μ).character (e.permCongr g) := by
  change (youngSpechtRepresentation μ).character
      (((Fintype.equivFinOfCardEq h).trans (youngBoxNumbering μ).symm).permCongr g) = _
  exact permutation_character_label_independent (youngSpechtRepresentation μ) _ e g

theorem spechtCharacterOn_relabel {A B : Type*} [Fintype A] [Fintype B] (μ : YoungDiagram)
    (hA : Fintype.card A = partitionSize μ) (hB : Fintype.card B = partitionSize μ)
    (e : A ≃ B) (g : Equiv.Perm A) :
    spechtCharacterOn μ hB (e.permCongr g) = spechtCharacterOn μ hA g := by
  change (spechtRepresentation μ).character
      ((e.trans (Fintype.equivFinOfCardEq hB)).permCongr g) =
    (spechtRepresentation μ).character ((Fintype.equivFinOfCardEq hA).permCongr g)
  exact permutation_character_label_independent (spechtRepresentation μ) _ _ g

theorem spechtCharacterOn_one {A : Type*} [Fintype A] (μ : YoungDiagram)
    (h : Fintype.card A = partitionSize μ) :
    spechtCharacterOn μ h 1 = Module.finrank ℂ (YoungSpechtModule μ) := by
  unfold spechtCharacterOn
  have he : (Fintype.equivFinOfCardEq h).permCongr (1 : Equiv.Perm A) = 1 := by
    apply Equiv.ext
    intro x
    exact (Fintype.equivFinOfCardEq h).apply_symm_apply x
  rw [he, spechtCharacter_one]

end
end ModifiedCartan


