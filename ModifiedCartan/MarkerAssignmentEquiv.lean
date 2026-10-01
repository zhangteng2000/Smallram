import ModifiedCartan.EmbeddingMarkerAssignment

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def markerAssignmentPreimage {A B : Type*} [Fintype B] (s : Finset A)
    (c : B → Option A) (hc : markerAssignmentDegree c = markerSquarefreeDegree s) (a : s) : B :=
  Classical.choose (((markerAssignmentDegree_eq_iff s c).mp hc).1 a.val a.property).exists

theorem markerAssignmentPreimage_spec {A B : Type*} [Fintype B] (s : Finset A)
    (c : B → Option A) (hc : markerAssignmentDegree c = markerSquarefreeDegree s) (a : s) :
    c (markerAssignmentPreimage s c hc a) = some a.val :=
  Classical.choose_spec (((markerAssignmentDegree_eq_iff s c).mp hc).1 a.val a.property).exists

def markerEmbeddingOfAssignment {A B : Type*} [Fintype B] (s : Finset A)
    (c : B → Option A) (hc : markerAssignmentDegree c = markerSquarefreeDegree s) : s ↪ B where
  toFun := markerAssignmentPreimage s c hc
  inj' := by
    intro a i he
    apply Subtype.ext
    apply Option.some.inj
    exact (markerAssignmentPreimage_spec s c hc a).symm.trans
      ((congrArg c he).trans (markerAssignmentPreimage_spec s c hc i))

theorem markerEmbeddingOfAssignment_spec {A B : Type*} [Fintype B] (s : Finset A)
    (c : B → Option A) (hc : markerAssignmentDegree c = markerSquarefreeDegree s) (a : s) :
    c (markerEmbeddingOfAssignment s c hc a) = some a.val :=
  markerAssignmentPreimage_spec s c hc a

theorem markerAssignment_recover_embedding {A B : Type*} [Fintype B]
    (s : Finset A) (f : s ↪ B) :
    markerEmbeddingOfAssignment s (markerAssignmentOfEmbedding s f)
      (markerAssignmentOfEmbedding_degree s f) = f := by
  apply DFunLike.ext
  intro a
  have he := markerEmbeddingOfAssignment_spec s (markerAssignmentOfEmbedding s f)
    (markerAssignmentOfEmbedding_degree s f) a
  obtain ⟨i, hi, hfi⟩ := (markerAssignmentOfEmbedding_eq_some s f _ a.val).mp he
  exact hfi.symm.trans (congrArg f (Subtype.ext hi))

theorem markerAssignment_recover_assignment {A B : Type*} [Fintype B]
    (s : Finset A) (c : B → Option A)
    (hc : markerAssignmentDegree c = markerSquarefreeDegree s) :
    markerAssignmentOfEmbedding s (markerEmbeddingOfAssignment s c hc) = c := by
  let f := markerEmbeddingOfAssignment s c hc
  have hgood := (markerAssignmentDegree_eq_iff s c).mp hc
  funext b
  cases hb : c b with
  | none =>
    apply (markerAssignmentOfEmbedding_eq_none s f b).mpr
    rintro ⟨a, ha⟩
    have he := markerEmbeddingOfAssignment_spec s c hc a
    change c (f a) = some a.val at he
    rw [ha, hb] at he
    cases he
  | some a =>
    have ha : a ∈ s := by
      by_contra hn
      exact hgood.2 a hn b hb
    have he : f ⟨a, ha⟩ = b :=
      (hgood.1 a ha).unique (markerEmbeddingOfAssignment_spec s c hc ⟨a, ha⟩) hb
    rw [← he, markerAssignmentOfEmbedding_self]

def markerAssignmentEquiv {A B : Type*} [Fintype B] (s : Finset A) :
    (s ↪ B) ≃ {c : B → Option A // markerAssignmentDegree c = markerSquarefreeDegree s} where
  toFun f := ⟨markerAssignmentOfEmbedding s f, markerAssignmentOfEmbedding_degree s f⟩
  invFun c := markerEmbeddingOfAssignment s c.val c.property
  left_inv := markerAssignment_recover_embedding s
  right_inv c := Subtype.ext (markerAssignment_recover_assignment s c.val c.property)

end
end ModifiedCartan

