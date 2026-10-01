import ModifiedCartan.KPAlphaFullInduction
import ModifiedCartan.NestedPermutationErasure

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem sum_sizedYoungDiagram_congr {M : Type*} [AddCommMonoid M] {n m : ℕ}
    (h : n = m) (f : YoungDiagram → M) :
    (∑ ν : SizedYoungDiagram n, f ν.val) = ∑ ν : SizedYoungDiagram m, f ν.val := by
  subst m
  rfl

theorem kpSubsetExtension_erase (J : Finset A) (a : J) (μ : YoungDiagram)
    (hJ : J.card = partitionSize μ + 1) :
    kpSubsetExtension J (kpAlpha μ ((Finset.univ : Finset J).erase a)) =
      kpAlpha μ (J.erase a.val) := by
  have hK : ((Finset.univ : Finset J).erase a).card = partitionSize μ := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_coe, hJ]
    omega
  have hI : (J.erase a.val).card = partitionSize μ := by
    rw [Finset.card_erase_of_mem a.property, hJ]
    omega
  rw [kpAlpha_of_card_eq μ _ hK, kpAlpha_of_card_eq μ _ hI]
  simp only [kpSubsetExtension, map_sum, MonoidAlgebra.mapDomainLinearMap_single]
  calc
    _ = ∑ p : Equiv.Perm (↥((Finset.univ : Finset J).erase a)),
        MonoidAlgebra.single (supportedPermutationEquiv (J.erase a.val) ((eraseInsideEquiv J a).permCongr p)).val
          (spechtCharacterOn μ ((Fintype.card_coe _).trans hI) ((eraseInsideEquiv J a).permCongr p)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [supportedPermutation_nested_erase J a p,
        spechtCharacterOn_relabel μ _ _ (eraseInsideEquiv J a) p]
    _ = _ := (eraseInsideEquiv J a).permCongr.sum_comp (fun p =>
      MonoidAlgebra.single (supportedPermutationEquiv (J.erase a.val) p).val
        (spechtCharacterOn μ ((Fintype.card_coe _).trans hI) p))

/-- The one-box alpha identity inside any actual subset of the ambient alphabet. -/
theorem kpAlpha_sum_erase_subset (J : Finset A) (μ : YoungDiagram)
    (hJ : J.card = partitionSize μ + 1) :
    (∑ a : J, kpAlpha μ (J.erase a.val)) =
      ∑ ν : SizedYoungDiagram J.card,
        if PartitionCovers ν.val μ then kpAlpha ν.val J else 0 := by
  have he : (∑ a : J, kpAlpha μ (J.erase a.val)) =
      ∑ ν : SizedYoungDiagram (Fintype.card J),
        if PartitionCovers ν.val μ then kpAlpha ν.val J else 0 := by
    calc
      _ = kpSubsetExtension J (∑ a : J, kpAlpha μ ((Finset.univ : Finset J).erase a)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        exact (kpSubsetExtension_erase J a μ hJ).symm
      _ = kpSubsetExtension J (∑ ν : SizedYoungDiagram (Fintype.card J),
          if PartitionCovers ν.val μ then kpFullCharacterSum ν.val ν.property.symm else 0) :=
        congrArg (kpSubsetExtension J) (kpAlpha_sum_erase μ ((Fintype.card_coe J).trans hJ))
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro ν _
        by_cases hc : PartitionCovers ν.val μ
        · rw [if_pos hc, if_pos hc, kpSubsetExtension_full J ν.val
            ((Fintype.card_coe J).symm.trans ν.property.symm)]
        · rw [if_neg hc, if_neg hc, map_zero]
  exact he.trans (sum_sizedYoungDiagram_congr (Fintype.card_coe J)
    (fun ν => if PartitionCovers ν μ then kpAlpha ν J else 0))

end
end ModifiedCartan


