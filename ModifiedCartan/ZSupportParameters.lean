import ModifiedCartan.ZSupportReconstruction

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem zStripPrefixLength_eq_of_mem_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (a : Z) (k : ℕ) (hk : k ≤ zStripLength θ Z a)
    (hm : ∀ i < zStripLength θ Z a, (θ ^ i) a.val ∈ Y ↔ i < k) :
    zStripPrefixLength θ Z Y a = k := by
  apply (Nat.find_eq_iff (zStripExit_exists θ Z Y a)).mpr
  refine ⟨⟨hk, ?_⟩, ?_⟩
  · by_cases he : k = zStripLength θ Z a
    · exact Or.inl he
    · exact Or.inr (fun h => (Nat.lt_irrefl k) ((hm k (by omega)).mp h))
  · intro i hi hs
    rcases hs.2 with he | hn
    · omega
    · exact hn ((hm i (by omega)).mpr hi)

theorem zPrefixSet_union_prefixLength {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hD : D ⊆ zStripComplement θ Z) (a : Z) :
    zStripPrefixLength θ Z (zPrefixSet θ Z κ ∪ D) a = (κ a).val + 1 := by
  apply zStripPrefixLength_eq_of_mem_iff
  · have := (κ a).isLt; omega
  · exact zPrefixSet_union_strip_mem_iff θ Z κ D hD a

theorem zPrefixSet_union_composition {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hD : D ⊆ zStripComplement θ Z)
    (h : IsZAdmissible θ Z (zPrefixSet θ Z κ ∪ D)) :
    zAdmissibleComposition θ Z (zPrefixSet θ Z κ ∪ D) h = κ := by
  funext a
  apply Fin.ext
  have hp := zAdmissibleComposition_part θ Z _ h a
  rw [zPrefixSet_union_prefixLength θ Z κ D hD a] at hp
  omega

theorem zPrefixSet_union_complement {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z : Finset A) (κ : ∀ a : Z, Fin (zStripLength θ Z a)) (D : Finset A)
    (hD : D ⊆ zStripComplement θ Z) :
    zStripComplement θ Z ∩ (zPrefixSet θ Z κ ∪ D) = D := by
  ext x
  constructor
  · intro hx
    obtain ⟨hc, hm⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_union.mp hm with hp | hd
    · exact False.elim ((mem_zStripComplement_iff θ Z x).mp hc
        (zPrefixSet_subset_union θ Z κ hp))
    · exact hd
  · intro hx
    exact Finset.mem_inter.mpr ⟨hD hx, Finset.mem_union_right _ hx⟩

/-- All parameters are literal finite strip lengths and an invariant subset of
the complement; no existence of a factorization is assumed in this type. -/
def ZSupportParameters {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :=
  (∀ a : Z, Fin (zStripLength θ Z a)) ×
    {D : Finset A // D ⊆ zStripComplement θ Z ∧ ∀ x, θ x ∈ D ↔ x ∈ D}

def zAdmissibleSupportEquiv {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :
    ZSupportParameters θ Z ≃ {Y : Finset A // IsZAdmissible θ Z Y} where
  toFun p := ⟨zPrefixSet θ Z p.1 ∪ p.2.val,
    zPrefixSet_union_isZAdmissible θ Z p.1 p.2.val p.2.property.2⟩
  invFun Y := ⟨zAdmissibleComposition θ Z Y.val Y.property,
    ⟨zStripComplement θ Z ∩ Y.val, Finset.inter_subset_left,
      zAdmissible_complement_apply_iff θ Z Y.val Y.property⟩⟩
  left_inv p := by
    apply Prod.ext
    · exact zPrefixSet_union_composition θ Z p.1 p.2.val p.2.property.1
        (zPrefixSet_union_isZAdmissible θ Z p.1 p.2.val p.2.property.2)
    · exact Subtype.ext (zPrefixSet_union_complement θ Z p.1 p.2.val p.2.property.1)
  right_inv Y := Subtype.ext (zAdmissible_reconstruction θ Z Y.val Y.property).symm

end
end ModifiedCartan

