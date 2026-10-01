import ModifiedCartan.MarkerAssignmentEquiv
import ModifiedCartan.MarkerAffineExpansion
import ModifiedCartan.InjectiveGeometricProducts
import ModifiedCartan.FixedPointPermutationSums

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def markerEmbeddingWeight {A B R : Type*} [Fintype B] [CommMonoid R]
    (s : Finset A) (h : B → R) (w : A → B → R) (f : s ↪ B) : R :=
  (∏ a : s, w a.val (f a)) * ∏ b ∈ Finset.univ \ Finset.univ.image f, h b

theorem markerAssignmentWeight_of_embedding {A B R : Type*} [Fintype B] [CommMonoid R]
    (s : Finset A) (h : B → R) (w : A → B → R) (f : s ↪ B) :
    markerAssignmentWeight h w (markerAssignmentOfEmbedding s f) = markerEmbeddingWeight s h w f := by
  rw [markerAssignmentWeight, product_split_embedding f]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro a ha
    rw [markerAssignmentOfEmbedding_self]
    rfl
  · apply Finset.prod_congr rfl
    intro b hb
    have he : ¬ ∃ a : s, f a = b := by
      rintro ⟨a, ha⟩
      exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
    rw [(markerAssignmentOfEmbedding_eq_none s f b).mpr he]
    rfl

/-- The exact squarefree marker coefficient enumerates injective choices,
including the factors for unused colors. -/
theorem markerAffineProduct_squarefree_coeff {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (s : Finset A) (h : B → R) (w : A → B → R) :
    MvPolynomial.coeff (markerSquarefreeDegree s) (markerAffineProduct h w) =
      ∑ f : s ↪ B, markerEmbeddingWeight s h w f := by
  rw [markerAffineProduct_coeff]
  calc
    _ = ∑ c : {c : B → Option A // markerAssignmentDegree c = markerSquarefreeDegree s},
        markerAssignmentWeight h w c.val :=
      sum_dite_eq_sum_subtype (fun c : B → Option A => markerAssignmentDegree c = markerSquarefreeDegree s)
        (fun c _ => markerAssignmentWeight h w c)
    _ = ∑ f : s ↪ B, markerAssignmentWeight h w (markerAssignmentOfEmbedding s f) :=
      (Equiv.sum_comp (markerAssignmentEquiv (B := B) s)
        (fun c => markerAssignmentWeight h w c.val)).symm
    _ = _ := Finset.sum_congr rfl (fun f hf => markerAssignmentWeight_of_embedding s h w f)

end
end ModifiedCartan

