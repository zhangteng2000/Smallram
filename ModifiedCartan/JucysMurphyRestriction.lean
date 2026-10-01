import ModifiedCartan.JucysMurphyElements
import ModifiedCartan.IntertwinerAlgebraAction
import ModifiedCartan.SpechtCornerDirectSum

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [LinearOrder A]

theorem jucysMurphy_corner_restriction (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (a : A) (ha : ∀ i : A, i ≤ a) (b : YoungCorner μ)
    (i : ↥(Finset.univ.erase a)) (v : YoungSpechtModule (removePartitionBox μ b)) :
    (spechtRepresentationOn μ h).asAlgebraHom (jucysMurphyElement i.val)
        (spechtCornerEmbedding μ h a b v) =
      spechtCornerEmbedding μ h a b
        ((spechtRepresentationOn (removePartitionBox μ b) (card_erase_eq_partition_remove μ h a b)).asAlgebraHom
          (jucysMurphyElement i) v) := by
  rw [← kpSubsetExtension_jucysMurphy_erase a ha i, asAlgebraHom_subsetExtension]
  exact intertwiner_asAlgebraHom_apply _ _ (spechtCornerEmbedding μ h a b) (jucysMurphyElement i) v

theorem jucysMurphy_corner_max (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (a : A) (ha : ∀ i : A, i ≤ a) (b : YoungCorner μ)
    (v : YoungSpechtModule (removePartitionBox μ b)) :
    (spechtRepresentationOn μ h).asAlgebraHom (jucysMurphyElement a)
        (spechtCornerEmbedding μ h a b v) =
      ((b.val.val.2 : ℂ) - (b.val.val.1 : ℂ)) • spechtCornerEmbedding μ h a b v := by
  rw [jucysMurphyElement_max a ha]
  exact specht_corner_star_eigenvalue μ h a b (spechtCornerEmbedding μ h a b) v

end
end ModifiedCartan


