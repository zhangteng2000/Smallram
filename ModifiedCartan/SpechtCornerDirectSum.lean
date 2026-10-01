import ModifiedCartan.SpechtCornerStarEigenvalue
import ModifiedCartan.EigenblockBasis
import ModifiedCartan.CornerTableauCount

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def spechtCornerEmbedding (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (a : A) (b : YoungCorner μ) : Representation.IntertwiningMap
      (spechtRepresentationOn (removePartitionBox μ b) (card_erase_eq_partition_remove μ h a b))
      (eraseRestrictedSpecht μ h a) :=
  Classical.choose (exists_specht_restriction_embedding μ h a b)

theorem spechtCornerEmbedding_injective (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (a : A) (b : YoungCorner μ) : Function.Injective (spechtCornerEmbedding μ h a b) :=
  (Classical.choose_spec (exists_specht_restriction_embedding μ h a b)).1

theorem spechtCorner_finrank_sum (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) (a : A) :
    (∑ b : YoungCorner μ, Module.finrank ℂ (YoungSpechtModule (removePartitionBox μ b))) =
      Module.finrank ℂ (YoungSpechtModule μ) := by
  apply (finrank_specht_remove_recurrence μ _).symm
  rw [← h]
  exact Fintype.card_pos_iff.mpr ⟨a⟩

def spechtCornerSumEquiv (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) (a : A) :
    (∀ b : YoungCorner μ, YoungSpechtModule (removePartitionBox μ b)) ≃ₗ[ℂ] YoungSpechtModule μ :=
  eigenblockSumEquiv (fun b => (spechtCornerEmbedding μ h a b).toLinearMap)
    (spechtCornerEmbedding_injective μ h a)
    ((spechtRepresentationOn μ h).asAlgebraHom (permutationStar (Finset.univ.erase a) a))
    (fun b => (b.val.val.2 : ℂ) - (b.val.val.1 : ℂ)) (youngCorner_content_injective μ)
    (fun b v => specht_corner_star_eigenvalue μ h a b (spechtCornerEmbedding μ h a b) v)
    (spechtCorner_finrank_sum μ h a)

theorem spechtCornerSumEquiv_apply (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (a : A) (v : ∀ b : YoungCorner μ, YoungSpechtModule (removePartitionBox μ b)) :
    spechtCornerSumEquiv μ h a v = ∑ b : YoungCorner μ, spechtCornerEmbedding μ h a b (v b) := rfl

def spechtCornerBasis (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) (a : A)
    {κ : YoungCorner μ → Type*}
    (b : ∀ c : YoungCorner μ, Module.Basis (κ c) ℂ (YoungSpechtModule (removePartitionBox μ c))) :
    Module.Basis (Σ c : YoungCorner μ, κ c) ℂ (YoungSpechtModule μ) :=
  (Pi.basis b).map (spechtCornerSumEquiv μ h a)

theorem spechtCornerBasis_apply (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) (a : A)
    {κ : YoungCorner μ → Type*}
    (b : ∀ c : YoungCorner μ, Module.Basis (κ c) ℂ (YoungSpechtModule (removePartitionBox μ c)))
    (p : Σ c : YoungCorner μ, κ c) :
    spechtCornerBasis μ h a b p = spechtCornerEmbedding μ h a p.1 (b p.1 p.2) := by
  exact eigenblockBasis_apply b _ _ _ _ _ _ _ p

end
end ModifiedCartan


