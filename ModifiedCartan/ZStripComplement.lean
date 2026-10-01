import ModifiedCartan.ZStripUnion

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The letters on cycles disjoint from Z, for KP Section 4.1.3. -/
def zStripComplement {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) : Finset A :=
  Finset.univ \ zStripUnion θ Z

theorem mem_zStripComplement_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (x : A) : x ∈ zStripComplement θ Z ↔ x ∉ zStripUnion θ Z := by
  simp [zStripComplement]

theorem zStripComplement_not_mem_Z {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (x : A) (hx : x ∈ zStripComplement θ Z) : x ∉ Z := by
  intro hZ
  exact (mem_zStripComplement_iff θ Z x).mp hx (subset_zStripUnion θ Z hZ)

theorem zStripComplement_apply_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (x : A) : θ x ∈ zStripComplement θ Z ↔ x ∈ zStripComplement θ Z := by
  simp only [mem_zStripComplement_iff, zStripUnion_apply_iff]

theorem zStripComplement_inv_apply_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (x : A) : θ⁻¹ x ∈ zStripComplement θ Z ↔ x ∈ zStripComplement θ Z := by
  have h := zStripComplement_apply_iff θ Z (θ⁻¹ x)
  simpa using h.symm

def zStripComplementPerm {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :
    Equiv.Perm (zStripComplement θ Z) := θ.subtypePerm (zStripComplement_apply_iff θ Z)

theorem zStripComplementPerm_apply {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (x : zStripComplement θ Z) :
    (zStripComplementPerm θ Z x).val = θ x.val := rfl

theorem zStripUnion_complement_partition {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) : zStripUnion θ Z ∪ zStripComplement θ Z = Finset.univ := by
  ext x
  simp [zStripComplement]

theorem zStripUnion_complement_disjoint {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) : Disjoint (zStripUnion θ Z) (zStripComplement θ Z) := by
  apply Finset.disjoint_left.mpr
  intro x hx hc
  exact (mem_zStripComplement_iff θ Z x).mp hc hx

theorem zStripLengths_add_complement_card {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) : (∑ a : Z, zStripLength θ Z a) + (zStripComplement θ Z).card =
      Fintype.card A := by
  have h := Finset.card_sdiff_add_card_eq_card
    (show zStripUnion θ Z ⊆ Finset.univ from Finset.subset_univ _)
  rw [zStripUnion_card] at h
  simpa [zStripComplement, Nat.add_comm] using h

end
end ModifiedCartan

