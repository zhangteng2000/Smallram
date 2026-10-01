import ModifiedCartan.ZStripPrefixLength

open scoped Classical

namespace ModifiedCartan
noncomputable section

def zPrefixEmbedding {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) : (Σ a : Z, Fin ((κ a).val + 1)) ↪ A where
  toFun p := (θ ^ p.2.val) p.1.val
  inj' := by
    rintro ⟨a, i⟩ ⟨b, j⟩ he
    have hi : i.val < zStripLength θ Z a := by have := i.isLt; have := (κ a).isLt; omega
    have hj : j.val < zStripLength θ Z b := by have := j.isLt; have := (κ b).isLt; omega
    obtain ⟨hab, hij⟩ := (zStrip_pow_eq_iff θ Z a b i.val j.val hi hj).mp he
    subst b
    have heij : i = j := Fin.ext hij
    subst j
    rfl

/-- A nonempty initial segment in each actual strip. -/
def zPrefixSet {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) : Finset A :=
  Finset.univ.map (zPrefixEmbedding θ Z κ)

theorem mem_zPrefixSet_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (x : A) :
    x ∈ zPrefixSet θ Z κ ↔ ∃ a : Z, ∃ i : Fin ((κ a).val + 1), (θ ^ i.val) a.val = x := by
  simp only [zPrefixSet, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, i⟩, h⟩
    exact ⟨a, i, h⟩
  · rintro ⟨a, i, h⟩
    exact ⟨⟨a, i⟩, h⟩

theorem zPrefixSet_subset_union {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) : zPrefixSet θ Z κ ⊆ zStripUnion θ Z := by
  intro x hx
  obtain ⟨a, i, hi⟩ := (mem_zPrefixSet_iff θ Z κ x).mp hx
  refine (mem_zStripUnion_iff θ Z x).mpr ⟨a, ⟨i.val, ?_⟩, hi⟩
  have := i.isLt
  have := (κ a).isLt
  omega

theorem subset_zPrefixSet {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) : Z ⊆ zPrefixSet θ Z κ := by
  intro a ha
  refine (mem_zPrefixSet_iff θ Z κ a).mpr ⟨⟨a, ha⟩, ⟨0, by omega⟩, ?_⟩
  simp

theorem zPrefixSet_strip_mem_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (a : Z) (i : ℕ)
    (hi : i < zStripLength θ Z a) :
    (θ ^ i) a.val ∈ zPrefixSet θ Z κ ↔ i < (κ a).val + 1 := by
  constructor
  · intro hm
    obtain ⟨b, j, he⟩ := (mem_zPrefixSet_iff θ Z κ _).mp hm
    have hj : j.val < zStripLength θ Z b := by have := j.isLt; have := (κ b).isLt; omega
    obtain ⟨hba, hji⟩ := (zStrip_pow_eq_iff θ Z b a j.val i hj hi).mp he
    subst b
    simpa only [hji] using j.isLt
  · intro h
    exact (mem_zPrefixSet_iff θ Z κ _).mpr ⟨a, ⟨i, h⟩, rfl⟩

theorem zPrefixSet_card {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (κ : ∀ a : Z, Fin (zStripLength θ Z a)) :
    (zPrefixSet θ Z κ).card = ∑ a : Z, ((κ a).val + 1) := by
  simp [zPrefixSet, Fintype.card_sigma]

end
end ModifiedCartan

