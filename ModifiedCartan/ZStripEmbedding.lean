import ModifiedCartan.ZStripLength

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem permutation_pow_cancel_le {A : Type*} (θ : Equiv.Perm A) (a b : A)
    (i j : ℕ) (hij : i ≤ j) (he : (θ ^ i) a = (θ ^ j) b) :
    a = (θ ^ (j - i)) b := by
  have hj : j = i + (j - i) := by omega
  rw [hj, pow_add, Equiv.Perm.mul_apply] at he
  exact (θ ^ i).injective he

theorem zStrip_pow_eq_of_le {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (a b : Z) (i j : ℕ) (hj : j < zStripLength θ Z b) (hij : i ≤ j)
    (he : (θ ^ i) a.val = (θ ^ j) b.val) : a = b ∧ i = j := by
  have hab := permutation_pow_cancel_le θ a.val b.val i j hij he
  have hzero : j - i = 0 := by
    by_contra hn
    exact zStripLength_minimal θ Z b (j - i) (Nat.pos_of_ne_zero hn)
      (by omega) (hab ▸ a.property)
  have hij' : i = j := by omega
  subst j
  exact ⟨Subtype.ext ((θ ^ i).injective he), rfl⟩

theorem zStrip_pow_eq_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (a b : Z) (i j : ℕ) (hi : i < zStripLength θ Z a) (hj : j < zStripLength θ Z b) :
    (θ ^ i) a.val = (θ ^ j) b.val ↔ a = b ∧ i = j := by
  constructor
  · intro he
    rcases le_total i j with hij | hji
    · exact zStrip_pow_eq_of_le θ Z a b i j hj hij he
    · obtain ⟨hba, hji'⟩ := zStrip_pow_eq_of_le θ Z b a j i hi hji he.symm
      exact ⟨hba.symm, hji'.symm⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Every position of every actual Z-strip, embedded into the original alphabet.
Injectivity proves both distinctness within a strip and disjointness of strips. -/
def zStripEmbedding {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :
    (Σ a : Z, Fin (zStripLength θ Z a)) ↪ A where
  toFun p := (θ ^ p.2.val) p.1.val
  inj' := by
    rintro ⟨a, i⟩ ⟨b, j⟩ he
    obtain ⟨hab, hij⟩ := (zStrip_pow_eq_iff θ Z a b i.val j.val i.isLt j.isLt).mp he
    subst b
    have heij : i = j := Fin.ext hij
    subst j
    rfl

theorem zStripEmbedding_apply {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A)
    (a : Z) (i : Fin (zStripLength θ Z a)) : zStripEmbedding θ Z ⟨a, i⟩ = (θ ^ i.val) a.val := rfl

end
end ModifiedCartan

