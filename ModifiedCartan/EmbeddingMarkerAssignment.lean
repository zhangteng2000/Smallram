import ModifiedCartan.MarkerAssignmentDegree

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def markerAssignmentOfEmbedding {A B : Type*} (s : Finset A) (f : s ↪ B) (b : B) : Option A :=
  if h : ∃ a : s, f a = b then some (Classical.choose h).val else none

theorem markerAssignmentOfEmbedding_self {A B : Type*} (s : Finset A) (f : s ↪ B) (a : s) :
    markerAssignmentOfEmbedding s f (f a) = some a.val := by
  have h : ∃ i : s, f i = f a := ⟨a, rfl⟩
  rw [markerAssignmentOfEmbedding, dif_pos h]
  exact congrArg (fun i : s => some i.val) (f.injective (Classical.choose_spec h))

theorem markerAssignmentOfEmbedding_eq_some {A B : Type*} (s : Finset A) (f : s ↪ B)
    (b : B) (a : A) :
    markerAssignmentOfEmbedding s f b = some a ↔ ∃ i : s, i.val = a ∧ f i = b := by
  constructor
  · intro he
    by_cases h : ∃ i : s, f i = b
    · rw [markerAssignmentOfEmbedding, dif_pos h] at he
      exact ⟨Classical.choose h, Option.some.inj he, Classical.choose_spec h⟩
    · simp [markerAssignmentOfEmbedding, h] at he
  · rintro ⟨i, hi, hfi⟩
    rw [← hfi, markerAssignmentOfEmbedding_self, hi]

theorem markerAssignmentOfEmbedding_eq_none {A B : Type*} (s : Finset A) (f : s ↪ B)
    (b : B) :
    markerAssignmentOfEmbedding s f b = none ↔ ¬ ∃ i : s, f i = b := by
  simp [markerAssignmentOfEmbedding]

theorem markerAssignmentOfEmbedding_degree {A B : Type*} [Fintype B]
    (s : Finset A) (f : s ↪ B) :
    markerAssignmentDegree (markerAssignmentOfEmbedding s f) = markerSquarefreeDegree s := by
  apply (markerAssignmentDegree_eq_iff s _).mpr
  constructor
  · intro a ha
    refine ⟨f ⟨a, ha⟩, markerAssignmentOfEmbedding_self s f ⟨a, ha⟩, ?_⟩
    intro b hb
    obtain ⟨i, hi, hfi⟩ := (markerAssignmentOfEmbedding_eq_some s f b a).mp hb
    have hei : i = (⟨a, ha⟩ : s) := Subtype.ext hi
    exact hfi.symm.trans (congrArg f hei)
  · intro a ha b hb
    obtain ⟨i, hi, hfi⟩ := (markerAssignmentOfEmbedding_eq_some s f b a).mp hb
    exact ha (hi ▸ i.property)

end
end ModifiedCartan

