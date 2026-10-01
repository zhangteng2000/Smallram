import ModifiedCartan.MarkerAssignmentDegree
import Mathlib.Tactic.Tauto

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- Marker exponent in a product of two supported permutation terms. -/
def complementMarkerDegree {A : Type*} [Fintype A] (X Y : Finset A) : A →₀ ℕ :=
  markerSquarefreeDegree (Finset.univ \ X) + markerSquarefreeDegree (Finset.univ \ Y)

theorem complementMarkerDegree_apply {A : Type*} [Fintype A]
    (X Y : Finset A) (a : A) :
    complementMarkerDegree X Y a = (if a ∈ X then 0 else 1) + (if a ∈ Y then 0 else 1) := by
  simp [complementMarkerDegree, markerSquarefreeDegree_apply]

/-- Exactly the support condition for a squarefree marker coefficient in KP
equation (4.3). Auxiliary to LaTeX `lem:KP-correspondence`. -/
theorem complementMarkerDegree_squarefree_iff {A : Type*} [Fintype A]
    (X Y Z : Finset A) :
    complementMarkerDegree X Y = markerSquarefreeDegree (Finset.univ \ Z) ↔
      X ∪ Y = Finset.univ ∧ X ∩ Y = Z := by
  constructor
  · intro h
    have hp (a : A) := congrArg (fun d : A →₀ ℕ => d a) h
    simp only [complementMarkerDegree_apply, markerSquarefreeDegree_apply,
      Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
    constructor
    · ext a
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_cases hx : a ∈ X
      · exact Or.inl hx
      · right
        by_contra hy
        have ha := hp a
        split_ifs at ha <;> omega
    · ext a
      simp only [Finset.mem_inter]
      have ha := hp a
      by_cases hx : a ∈ X <;> by_cases hy : a ∈ Y <;> by_cases hz : a ∈ Z <;>
        simp_all
  · rintro ⟨hu, hi⟩
    ext a
    have hu' := congrArg (fun s => a ∈ s) hu
    have hi' := congrArg (fun s => a ∈ s) hi
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_univ] at hu' hi'
    simp only [complementMarkerDegree_apply, markerSquarefreeDegree_apply,
      Finset.mem_sdiff, Finset.mem_univ, true_and]
    by_cases hx : a ∈ X <;> by_cases hy : a ∈ Y <;> by_cases hz : a ∈ Z <;>
      simp_all

end
end ModifiedCartan

