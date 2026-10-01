import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finsupp.Indicator

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def markerAssignmentDegree {A B : Type*} [Fintype B] (c : B → Option A) : A →₀ ℕ :=
  ∑ b : B, (c b).elim 0 (fun a => Finsupp.single a 1)

def markerSquarefreeDegree {A : Type*} (s : Finset A) : A →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

theorem markerSquarefreeDegree_apply {A : Type*} [DecidableEq A] (s : Finset A) (a : A) :
    markerSquarefreeDegree s a = if a ∈ s then 1 else 0 := by
  simp [markerSquarefreeDegree, Finsupp.indicator_apply]

theorem markerAssignmentDegree_apply {A B : Type*} [Fintype B]
    (c : B → Option A) (a : A) :
    markerAssignmentDegree c a = (Finset.univ.filter (fun b => c b = some a)).card := by
  simp only [markerAssignmentDegree, Finset.sum_apply']
  calc
    _ = ∑ b : B, if c b = some a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      cases h : c b with
      | none => simp
      | some i => simp [Finsupp.single_apply]
    _ = _ := by simp

theorem markerAssignmentDegree_eq_iff {A B : Type*} [Fintype B]
    (s : Finset A) (c : B → Option A) :
    markerAssignmentDegree c = markerSquarefreeDegree s ↔
      (∀ a ∈ s, ∃! b, c b = some a) ∧ (∀ a ∉ s, ∀ b, c b ≠ some a) := by
  constructor
  · intro he
    constructor
    · intro a ha
      have hc : (Finset.univ.filter (fun b => c b = some a)).card = 1 := by
        rw [← markerAssignmentDegree_apply, he, markerSquarefreeDegree_apply, if_pos ha]
      simpa using Finset.card_eq_one_iff_existsUnique.mp hc
    · intro a ha b hb
      have hc : (Finset.univ.filter (fun b => c b = some a)).card = 0 := by
        rw [← markerAssignmentDegree_apply, he, markerSquarefreeDegree_apply, if_neg ha]
      have hempty := Finset.card_eq_zero.mp hc
      have hm : b ∈ Finset.univ.filter (fun b => c b = some a) := by simp [hb]
      rw [hempty] at hm
      exact Finset.notMem_empty b hm
  · rintro ⟨hmem, hnot⟩
    ext a
    rw [markerAssignmentDegree_apply, markerSquarefreeDegree_apply]
    by_cases ha : a ∈ s
    · rw [if_pos ha]
      apply Finset.card_eq_one_iff_existsUnique.mpr
      simpa using hmem a ha
    · rw [if_neg ha, Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact hnot a ha b (Finset.mem_filter.mp hb).2

end
end ModifiedCartan

