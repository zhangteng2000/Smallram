import ModifiedCartan.ZAdmissibleSets

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem zStripExit_exists {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A)
    (a : Z) : ∃ n : ℕ, n ≤ zStripLength θ Z a ∧
      (n = zStripLength θ Z a ∨ (θ ^ n) a.val ∉ Y) :=
  ⟨zStripLength θ Z a, le_rfl, Or.inl rfl⟩

/-- Length of the initial part of the actual strip which lies in Y.
For admissible supports this is the exact kappa in KP Section 4.1.3. -/
def zStripPrefixLength {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A)
    (a : Z) : ℕ := Nat.find (zStripExit_exists θ Z Y a)

theorem zStripPrefixLength_le {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A)
    (a : Z) : zStripPrefixLength θ Z Y a ≤ zStripLength θ Z a :=
  (Nat.find_spec (zStripExit_exists θ Z Y a)).1

theorem zStripPrefixLength_exit {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A)
    (a : Z) (h : zStripPrefixLength θ Z Y a < zStripLength θ Z a) :
    (θ ^ zStripPrefixLength θ Z Y a) a.val ∉ Y := by
  have hs : zStripPrefixLength θ Z Y a = zStripLength θ Z a ∨
      (θ ^ zStripPrefixLength θ Z Y a) a.val ∉ Y :=
    (Nat.find_spec (zStripExit_exists θ Z Y a)).2
  obtain he | hn := hs
  · omega
  · exact hn

theorem zStripPrefixLength_pos {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A)
    (hZY : Z ⊆ Y) (a : Z) : 0 < zStripPrefixLength θ Z Y a := by
  by_contra h
  have he : zStripPrefixLength θ Z Y a = 0 := by omega
  have hn := zStripPrefixLength_exit θ Z Y a (by rw [he]; exact zStripLength_pos θ Z a)
  rw [he] at hn
  exact hn (by simpa using hZY a.property)

theorem zStripPrefix_mem {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A)
    (a : Z) (i : ℕ) (hi : i < zStripPrefixLength θ Z Y a) : (θ ^ i) a.val ∈ Y := by
  by_contra hn
  have hle : zStripPrefixLength θ Z Y a ≤ i :=
    Nat.find_min' (zStripExit_exists θ Z Y a)
      ⟨by have := zStripPrefixLength_le θ Z Y a; omega, Or.inr hn⟩
  omega

theorem zAdmissible_strip_mem_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (h : IsZAdmissible θ Z Y) (a : Z) (i : ℕ)
    (hi : i < zStripLength θ Z a) :
    (θ ^ i) a.val ∈ Y ↔ i < zStripPrefixLength θ Z Y a := by
  constructor
  · intro hm
    by_contra hn
    have hki : zStripPrefixLength θ Z Y a ≤ i := by omega
    have hm' := zAdmissible_strip_downward θ Z Y h a _ i hki hi hm
    exact zStripPrefixLength_exit θ Z Y a (by omega) hm'
  · exact zStripPrefix_mem θ Z Y a i

def zAdmissibleComposition {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A)
    (h : IsZAdmissible θ Z Y) (a : Z) : Fin (zStripLength θ Z a) :=
  ⟨zStripPrefixLength θ Z Y a - 1, by
    have := zStripPrefixLength_pos θ Z Y h.1 a
    have := zStripPrefixLength_le θ Z Y a
    omega⟩

theorem zAdmissibleComposition_part {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (h : IsZAdmissible θ Z Y) (a : Z) :
    (zAdmissibleComposition θ Z Y h a).val + 1 = zStripPrefixLength θ Z Y a := by
  change zStripPrefixLength θ Z Y a - 1 + 1 = _
  have := zStripPrefixLength_pos θ Z Y h.1 a
  omega

end
end ModifiedCartan

