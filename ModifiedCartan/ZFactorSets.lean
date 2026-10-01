import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto

open scoped Classical

namespace ModifiedCartan
noncomputable section

def zFactorLeftSet {A : Type*} [Fintype A] (Z Y : Finset A) : Finset A :=
  Finset.univ \ (Y \ Z)

theorem not_mem_zFactorLeftSet {A : Type*} [Fintype A] (Z Y : Finset A) (a : A) :
    a ∉ zFactorLeftSet Z Y ↔ a ∈ Y ∧ a ∉ Z := by
  simp [zFactorLeftSet]

theorem zFactorLeftSet_union {A : Type*} [Fintype A] (Z Y : Finset A) :
    zFactorLeftSet Z Y ∪ Y = Finset.univ := by
  ext a
  simp only [zFactorLeftSet, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
    true_and, iff_true]
  tauto

theorem zFactorLeftSet_inter {A : Type*} [Fintype A] (Z Y : Finset A) (hZY : Z ⊆ Y) :
    zFactorLeftSet Z Y ∩ Y = Z := by
  ext a
  simp only [zFactorLeftSet, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  have h := fun ha : a ∈ Z => hZY ha
  tauto

theorem zFactorLeftSet_unique {A : Type*} [Fintype A] (X Z Y : Finset A)
    (hu : X ∪ Y = Finset.univ) (hi : X ∩ Y = Z) : X = zFactorLeftSet Z Y := by
  ext a
  have hu' := congrArg (fun s => a ∈ s) hu
  have hi' := congrArg (fun s => a ∈ s) hi
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_univ] at hu' hi'
  simp only [zFactorLeftSet, Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

theorem zFactorLeftSet_card {A : Type*} [Fintype A] (Z Y : Finset A) (hZY : Z ⊆ Y) :
    (zFactorLeftSet Z Y).card + Y.card = Fintype.card A + Z.card := by
  have h := Finset.card_union_add_card_inter (zFactorLeftSet Z Y) Y
  rw [zFactorLeftSet_union, zFactorLeftSet_inter Z Y hZY, Finset.card_univ] at h
  exact h.symm

end
end ModifiedCartan

