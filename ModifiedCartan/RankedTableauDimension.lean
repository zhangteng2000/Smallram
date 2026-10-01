import ModifiedCartan.RankedYoungCoverEquivs
import ModifiedCartan.CornerTableauCount

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def youngTableauDimension (μ : YoungDiagram) : ℕ := standardSkewTableauCount μ ⊥

theorem youngTableauDimension_eq_finrank (μ : YoungDiagram) :
    youngTableauDimension μ = Module.finrank ℂ (YoungSpechtModule μ) :=
  (finrank_specht_eq_standardTableauCount μ).symm

@[simp] theorem youngTableauDimension_bot : youngTableauDimension ⊥ = 1 := standardSkewTableauCount_self ⊥

theorem youngTableauDimension_predecessors (μ : YoungDiagram) (hpos : 0 < partitionSize μ) :
    youngTableauDimension μ = ∑ δ : YoungPredecessor μ, youngTableauDimension δ.val := by
  unfold youngTableauDimension
  rw [standardTableauCount_remove_recurrence μ hpos]
  exact Equiv.sum_comp (youngCornerEquivPredecessor μ) (fun δ => standardSkewTableauCount δ.val ⊥)

theorem finite_sum_subtype_indicator {A : Type*} [Fintype A] (p : A → Prop) (f : A → ℕ) :
    (∑ a : {a : A // p a}, f a.val) = ∑ a : A, if p a then f a else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by intro a; simp) f, Finset.sum_filter]

theorem youngTableauDimension_rank_rec (n : ℕ) (μ : YoungDiagram)
    (hμ : partitionSize μ = n + 1) :
    youngTableauDimension μ = ∑ δ : SizedYoungDiagram n,
      if PartitionCovers μ δ.val then youngTableauDimension δ.val else 0 := by
  rw [youngTableauDimension_predecessors μ (by omega)]
  calc
    _ = ∑ δ : {δ : SizedYoungDiagram n // PartitionCovers μ δ.val}, youngTableauDimension δ.val.val :=
      Equiv.sum_comp (youngPredecessorSizedEquiv μ (n + 1) hμ) (fun δ => youngTableauDimension δ.val.val)
    _ = _ := finite_sum_subtype_indicator
      (fun δ : SizedYoungDiagram n => PartitionCovers μ δ.val) (fun δ => youngTableauDimension δ.val)

theorem youngTableauDimension_successors_rank (μ : YoungDiagram) (n : ℕ) (hμ : partitionSize μ = n) :
    (∑ ξ : YoungSuccessor μ, youngTableauDimension ξ.val) =
      ∑ ξ : SizedYoungDiagram (n + 1), if PartitionCovers ξ.val μ then youngTableauDimension ξ.val else 0 := by
  calc
    _ = ∑ ξ : {ξ : SizedYoungDiagram (n + 1) // PartitionCovers ξ.val μ}, youngTableauDimension ξ.val.val :=
      Equiv.sum_comp (youngSuccessorSizedEquiv μ n hμ) (fun ξ => youngTableauDimension ξ.val.val)
    _ = _ := finite_sum_subtype_indicator
      (fun ξ : SizedYoungDiagram (n + 1) => PartitionCovers ξ.val μ) (fun ξ => youngTableauDimension ξ.val)

theorem youngTableauDimension_successors_rank_of_size (μ : YoungDiagram) (m : ℕ)
    (hm : partitionSize μ + 1 = m) :
    (∑ ξ : YoungSuccessor μ, youngTableauDimension ξ.val) =
      ∑ ξ : SizedYoungDiagram m, if PartitionCovers ξ.val μ then youngTableauDimension ξ.val else 0 := by
  subst m
  exact youngTableauDimension_successors_rank μ (partitionSize μ) rfl

end
end ModifiedCartan


