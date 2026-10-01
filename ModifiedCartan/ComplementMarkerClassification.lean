import ModifiedCartan.ComplementMarkerDegrees

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem complementMarkerDegree_union_inter {A : Type*} [Fintype A] (X Y : Finset A) :
    complementMarkerDegree X Y = complementMarkerDegree (X ∪ Y) (X ∩ Y) := by
  ext a
  simp only [complementMarkerDegree_apply, Finset.mem_union, Finset.mem_inter]
  by_cases hx : a ∈ X <;> by_cases hy : a ∈ Y <;> simp [hx, hy]

theorem complementMarkerDegree_eq_iff {A : Type*} [Fintype A]
    (X Y U Z : Finset A) (hZU : Z ⊆ U) :
    complementMarkerDegree X Y = complementMarkerDegree U Z ↔
      X ∪ Y = U ∧ X ∩ Y = Z := by
  constructor
  · intro h
    have hp (a : A) : ((a ∈ X ∨ a ∈ Y) ↔ a ∈ U) ∧
        ((a ∈ X ∧ a ∈ Y) ↔ a ∈ Z) := by
      have hd := congrArg (fun d : A →₀ ℕ => d a) h
      have hz : a ∈ Z → a ∈ U := fun ha => hZU ha
      simp only [complementMarkerDegree_apply] at hd
      by_cases hx : a ∈ X <;> by_cases hy : a ∈ Y <;>
        by_cases hu : a ∈ U <;> by_cases hz' : a ∈ Z <;> simp_all
    constructor
    · ext a
      simpa only [Finset.mem_union] using (hp a).1
    · ext a
      simpa only [Finset.mem_inter] using (hp a).2
  · rintro ⟨hu, hi⟩
    rw [complementMarkerDegree_union_inter, hu, hi]

def markerActiveSet {A : Type*} [Fintype A] (d : A →₀ ℕ) : Finset A :=
  Finset.univ.filter (fun a => d a < 2)

def markerOverlapSet {A : Type*} [Fintype A] (d : A →₀ ℕ) : Finset A :=
  Finset.univ.filter (fun a => d a = 0)

theorem markerOverlapSet_subset_active {A : Type*} [Fintype A] (d : A →₀ ℕ) :
    markerOverlapSet d ⊆ markerActiveSet d := by
  intro a ha
  have hd : d a = 0 := (Finset.mem_filter.mp ha).2
  simp [markerActiveSet, hd]

theorem complementMarkerDegree_le_two {A : Type*} [Fintype A] (X Y : Finset A) (a : A) :
    complementMarkerDegree X Y a ≤ 2 := by
  rw [complementMarkerDegree_apply]
  split_ifs <;> omega

/-- Every marker exponent that can occur is uniquely encoded by the active
alphabet (degrees below two) and overlap (degree zero). -/
theorem complementMarkerDegree_active_overlap {A : Type*} [Fintype A]
    (d : A →₀ ℕ) (hd : ∀ a, d a ≤ 2) :
    complementMarkerDegree (markerActiveSet d) (markerOverlapSet d) = d := by
  ext a
  rw [complementMarkerDegree_apply]
  have hle := hd a
  by_cases h0 : d a = 0
  · simp [markerActiveSet, markerOverlapSet, h0]
  · by_cases h1 : d a = 1
    · simp [markerActiveSet, markerOverlapSet, h1]
    · have h2 : d a = 2 := by omega
      simp [markerActiveSet, markerOverlapSet, h2]

end
end ModifiedCartan

