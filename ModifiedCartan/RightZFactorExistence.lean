import ModifiedCartan.ZConstructedRightFactor
import ModifiedCartan.ZSupportParameters

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- Exact existence criterion for right factors, auxiliary to LaTeX
`lem:KP-correspondence`, KP source Section 4.1.3. -/
theorem exists_rightZFactor_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A) :
    (∃ π : Equiv.Perm A, IsRightZFactor θ Z Y π) ↔ IsZAdmissible θ Z Y := by
  constructor
  · rintro ⟨π, hπ⟩
    exact rightZFactor_isZAdmissible θ Z Y π hπ
  · intro h
    let κ := zAdmissibleComposition θ Z Y h
    let D := zStripComplement θ Z ∩ Y
    have hD : ∀ x, θ x ∈ D ↔ x ∈ D := zAdmissible_complement_apply_iff θ Z Y h
    let π := zConstructedRightFactor θ Z κ D hD 1
    have hp : IsRightZFactor θ Z (zPrefixSet θ Z κ ∪ D) π :=
      zConstructedRightFactor_isRight θ Z κ D Finset.inter_subset_left hD 1
    have he : Y = zPrefixSet θ Z κ ∪ D := zAdmissible_reconstruction θ Z Y h
    exact ⟨π, he.symm ▸ hp⟩

theorem rightZFactor_support_classification {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) : (∃ π : Equiv.Perm A, IsRightZFactor θ Z Y π) ↔
    ∃ κ : ∀ a : Z, Fin (zStripLength θ Z a),
      ∃ D : Finset A, D ⊆ zStripComplement θ Z ∧
        (∀ x, θ x ∈ D ↔ x ∈ D) ∧ Y = zPrefixSet θ Z κ ∪ D := by
  rw [exists_rightZFactor_iff]
  constructor
  · intro h
    exact ⟨zAdmissibleComposition θ Z Y h, zStripComplement θ Z ∩ Y,
      Finset.inter_subset_left, zAdmissible_complement_apply_iff θ Z Y h,
      zAdmissible_reconstruction θ Z Y h⟩
  · rintro ⟨κ, D, hsub, hD, he⟩
    exact he.symm ▸ zPrefixSet_union_isZAdmissible θ Z κ D hD

end
end ModifiedCartan

