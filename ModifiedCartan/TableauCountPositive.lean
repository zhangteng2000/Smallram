import ModifiedCartan.TableauCountRecurrence
import ModifiedCartan.TableauPrefixSteps
import ModifiedCartan.FinitePartitions
import Mathlib.Order.Preorder.Finite

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem nonempty_skewAddition_of_size_lt {n : ℕ} {μ ν : YoungDiagram}
    (hμν : μ ≤ ν) (hν : PartitionFits n ν) (hsize : partitionSize μ < partitionSize ν) :
    Nonempty (SkewAddition n ν μ) := by
  have hp : 0 < (ν.cells \ μ.cells).card := by
    rw [skewPartitionBoxes_card hμν]
    omega
  obtain ⟨c, hc, hmin⟩ := Finset.exists_minimal (Finset.card_pos.mp hp)
  have hcν : c ∈ ν := (Finset.mem_sdiff.mp hc).1
  have hcμ : c ∉ μ := (Finset.mem_sdiff.mp hc).2
  have hpred : ∀ d, d ≤ c → d ≠ c → d ∈ μ := by
    intro d hd hne
    by_contra hdμ
    have hdν : d ∈ ν := ν.isLowerSet hd hcν
    have hcd : c ≤ d := hmin (Finset.mem_sdiff.mpr ⟨hdν, hdμ⟩) hd
    exact hne (le_antisymm hd hcd)
  have hrow := rowLen_eq_of_minimal_missing_box hcμ hpred
  have hadd := addableRow_of_minimal_missing_box hcμ hpred
  refine ⟨⟨⟨c.1, hν.row_lt_of_mem hcν⟩, hadd, ?_⟩⟩
  intro d hd
  rcases (mem_addPartitionBox μ c.1 hadd d).mp hd with hd | hd
  · subst d
    simpa only [← hrow] using hcν
  · exact hμν hd

theorem standardSkewTableauCount_pos_of_size {n : ℕ} {μ ν : YoungDiagram}
    (hμν : μ ≤ ν) (hν : PartitionFits n ν) (k : ℕ)
    (hsize : partitionSize ν = partitionSize μ + k) :
    0 < standardSkewTableauCount ν μ := by
  induction k generalizing μ with
  | zero =>
    have heq : μ = ν := partition_eq_of_le_of_size_le hμν (by omega)
    subst μ
    rw [standardSkewTableauCount_self]
    omega
  | succ k ih =>
    obtain ⟨r⟩ := nonempty_skewAddition_of_size_lt hμν hν (by omega)
    have hr : partitionSize r.enlarged = partitionSize μ + 1 :=
      partitionSize_addPartitionBox μ r.row r.legal
    have hpos : 0 < standardSkewTableauCount ν r.enlarged :=
      ih r.inside (by change partitionSize ν = partitionSize r.enlarged + k; omega)
    have hp : 0 < (ν.cells \ μ.cells).card := by
      rw [skewPartitionBoxes_card hμν]
      omega
    rw [standardSkewTableauCount_rec hμν hν hp]
    exact hpos.trans_le (Finset.single_le_sum
      (fun i _ => Nat.zero_le (standardSkewTableauCount ν i.enlarged)) (Finset.mem_univ r))

theorem standardSkewTableauCount_pos {n : ℕ} {μ ν : YoungDiagram}
    (hμν : μ ≤ ν) (hν : PartitionFits n ν) : 0 < standardSkewTableauCount ν μ := by
  apply standardSkewTableauCount_pos_of_size hμν hν (partitionSize ν - partitionSize μ)
  have := partitionSize_mono hμν
  omega

end
end ModifiedCartan


