import ModifiedCartan.ZStripEmbedding
import Mathlib.Data.Fintype.BigOperators

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The union of all actual Z-strips, for KP Section 4.1.3 and
LaTeX `lem:KP-correspondence`. -/
def zStripUnion {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) : Finset A :=
  Finset.univ.map (zStripEmbedding θ Z)

theorem mem_zStripUnion_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (x : A) : x ∈ zStripUnion θ Z ↔
      ∃ a : Z, ∃ i : Fin (zStripLength θ Z a), (θ ^ i.val) a.val = x := by
  simp only [zStripUnion, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, i⟩, h⟩
    exact ⟨a, i, h⟩
  · rintro ⟨a, i, h⟩
    exact ⟨⟨a, i⟩, h⟩

theorem subset_zStripUnion {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :
    Z ⊆ zStripUnion θ Z := by
  intro a ha
  refine (mem_zStripUnion_iff θ Z a).mpr ⟨⟨a, ha⟩, ⟨0, zStripLength_pos θ Z ⟨a, ha⟩⟩, ?_⟩
  simp

theorem zStripUnion_apply_mem {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (x : A) (hx : x ∈ zStripUnion θ Z) : θ x ∈ zStripUnion θ Z := by
  obtain ⟨a, i, hi⟩ := (mem_zStripUnion_iff θ Z x).mp hx
  rw [← hi]
  have he : θ ((θ ^ i.val) a.val) = (θ ^ (i.val + 1)) a.val := by
    rw [pow_succ', Equiv.Perm.mul_apply]
  rw [he]
  by_cases hlt : i.val + 1 < zStripLength θ Z a
  · exact (mem_zStripUnion_iff θ Z _).mpr ⟨a, ⟨i.val + 1, hlt⟩, rfl⟩
  · have heq : i.val + 1 = zStripLength θ Z a := by have := i.isLt; omega
    rw [heq]
    exact subset_zStripUnion θ Z (zStripLength_return θ Z a)

theorem zStripUnion_image {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :
    (zStripUnion θ Z).image θ = zStripUnion θ Z := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact zStripUnion_apply_mem θ Z a ha
  · rw [Finset.card_image_of_injective _ θ.injective]

theorem zStripUnion_apply_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (x : A) : θ x ∈ zStripUnion θ Z ↔ x ∈ zStripUnion θ Z := by
  constructor
  · intro h
    rw [← zStripUnion_image θ Z] at h
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
    exact θ.injective he ▸ ha
  · exact zStripUnion_apply_mem θ Z x

theorem zStripUnion_card {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :
    (zStripUnion θ Z).card = ∑ a : Z, zStripLength θ Z a := by
  simp [zStripUnion, Fintype.card_sigma]

end
end ModifiedCartan

