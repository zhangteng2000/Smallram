import ModifiedCartan.ZPrefixSets

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem zPrefixSet_predecessor {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (x : A)
    (hx : x ∈ zPrefixSet θ Z κ \ Z) : θ⁻¹ x ∈ zPrefixSet θ Z κ := by
  obtain ⟨hm, hn⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨a, i, hi⟩ := (mem_zPrefixSet_iff θ Z κ x).mp hm
  have hpos : 0 < i.val := by
    by_contra h
    have he : i.val = 0 := by omega
    have hax : a.val = x := by simpa [he] using hi
    exact hn (hax ▸ a.property)
  have he : i.val = (i.val - 1) + 1 := by omega
  have hp : θ⁻¹ ((θ ^ i.val) a.val) = (θ ^ (i.val - 1)) a.val := by
    conv_lhs => rw [he, pow_succ', Equiv.Perm.mul_apply]
    simp
  rw [← hi, hp]
  exact (mem_zPrefixSet_iff θ Z κ _).mpr ⟨a, ⟨i.val - 1, by have := i.isLt; omega⟩, rfl⟩

theorem zPrefixSet_union_isZAdmissible {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hD : ∀ x, θ x ∈ D ↔ x ∈ D) : IsZAdmissible θ Z (zPrefixSet θ Z κ ∪ D) := by
  refine ⟨fun x hx => Finset.mem_union_left D (subset_zPrefixSet θ Z κ hx), ?_⟩
  intro x hx
  obtain ⟨hm, hn⟩ := Finset.mem_sdiff.mp hx
  rcases Finset.mem_union.mp hm with hp | hd
  · exact Finset.mem_union_left D (zPrefixSet_predecessor θ Z κ x (Finset.mem_sdiff.mpr ⟨hp, hn⟩))
  · apply Finset.mem_union_right
    exact (hD (θ⁻¹ x)).mp (by simpa using hd)

theorem zAdmissible_prefix_eq_inter {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (h : IsZAdmissible θ Z Y) :
    zPrefixSet θ Z (zAdmissibleComposition θ Z Y h) = zStripUnion θ Z ∩ Y := by
  ext x
  constructor
  · intro hx
    refine Finset.mem_inter.mpr ⟨zPrefixSet_subset_union θ Z _ hx, ?_⟩
    obtain ⟨a, i, hi⟩ := (mem_zPrefixSet_iff θ Z _ x).mp hx
    rw [← hi]
    apply zStripPrefix_mem θ Z Y a i.val
    simpa only [zAdmissibleComposition_part] using i.isLt
  · intro hx
    obtain ⟨hs, hy⟩ := Finset.mem_inter.mp hx
    obtain ⟨a, i, hi⟩ := (mem_zStripUnion_iff θ Z x).mp hs
    rw [← hi]
    apply (zPrefixSet_strip_mem_iff θ Z _ a i.val i.isLt).mpr
    rw [zAdmissibleComposition_part]
    exact (zAdmissible_strip_mem_iff θ Z Y h a i.val i.isLt).mp (by rwa [hi])

theorem zAdmissible_reconstruction {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (h : IsZAdmissible θ Z Y) :
    Y = zPrefixSet θ Z (zAdmissibleComposition θ Z Y h) ∪ (zStripComplement θ Z ∩ Y) := by
  rw [zAdmissible_prefix_eq_inter θ Z Y h]
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, mem_zStripComplement_iff]
  tauto

theorem zPrefixSet_union_strip_mem_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hD : D ⊆ zStripComplement θ Z) (a : Z) (i : ℕ) (hi : i < zStripLength θ Z a) :
    (θ ^ i) a.val ∈ zPrefixSet θ Z κ ∪ D ↔ i < (κ a).val + 1 := by
  have hn : (θ ^ i) a.val ∉ D := by
    intro hm
    exact (mem_zStripComplement_iff θ Z _).mp (hD hm)
      ((mem_zStripUnion_iff θ Z _).mpr ⟨a, ⟨i, hi⟩, rfl⟩)
  simp only [Finset.mem_union, hn, or_false, zPrefixSet_strip_mem_iff θ Z κ a i hi]

end
end ModifiedCartan

