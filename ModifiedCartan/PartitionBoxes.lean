import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Tactic

open scoped BigOperators

namespace ModifiedCartan

noncomputable section

/-- Number of boxes of a partition, used in LaTeX `eq:derivative-minor`. -/
def partitionSize (μ : YoungDiagram) : ℕ := μ.cells.card

/-- The partition has at most `n + 1` nonzero rows. -/
def PartitionFits (n : ℕ) (μ : YoungDiagram) : Prop := μ.rowLen (n + 1) = 0

/-- Increasing derivative orders in LaTeX `eq:derivative-minor`. -/
def partitionMinorOrders (n : ℕ) (μ : YoungDiagram) (i : Fin (n + 1)) : ℕ :=
  (i : ℕ) + μ.rowLen (n - (i : ℕ))

theorem partitionMinorOrders_strictMono (n : ℕ) (μ : YoungDiagram) :
    StrictMono (partitionMinorOrders n μ) := by
  intro i j hij
  have hij' : (i : ℕ) < (j : ℕ) := hij
  have hr := μ.rowLen_anti (n - (j : ℕ)) (n - (i : ℕ)) (by omega)
  dsimp [partitionMinorOrders]
  omega

@[simp] theorem partition_rowLen_bot (i : ℕ) : (⊥ : YoungDiagram).rowLen i = 0 := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen]
  simp

@[simp] theorem partitionMinorOrders_bot (n : ℕ) :
    partitionMinorOrders n ⊥ = fun i : Fin (n + 1) => (i : ℕ) := by
  funext i
  simp [partitionMinorOrders]

theorem PartitionFits.rowLen_eq_zero {n : ℕ} {μ : YoungDiagram}
    (h : PartitionFits n μ) {r : ℕ} (hr : n + 1 ≤ r) : μ.rowLen r = 0 := by
  have := μ.rowLen_anti (n + 1) r hr
  dsimp [PartitionFits] at h
  omega

theorem PartitionFits.row_lt_of_mem {n : ℕ} {μ : YoungDiagram}
    (h : PartitionFits n μ) {r c : ℕ} (hc : (r, c) ∈ μ) : r < n + 1 := by
  rw [YoungDiagram.mem_iff_lt_rowLen] at hc
  by_contra! hr
  rw [h.rowLen_eq_zero hr] at hc
  omega

/-- Adding the rightmost box in this row preserves the partition condition. -/
def AddablePartitionRow (μ : YoungDiagram) (r : ℕ) : Prop :=
  r = 0 ∨ μ.rowLen r < μ.rowLen (r - 1)

theorem mem_of_le_addable_box {μ : YoungDiagram} {r : ℕ}
    (h : AddablePartitionRow μ r) {d : ℕ × ℕ}
    (hd : d ≤ (r, μ.rowLen r)) (hne : d ≠ (r, μ.rowLen r)) : d ∈ μ := by
  rw [YoungDiagram.mem_iff_lt_rowLen]
  obtain ⟨hr, hc⟩ := hd
  by_cases heq : d.1 = r
  · have hcol : d.2 ≠ μ.rowLen r := by
      intro hh
      exact hne (Prod.ext heq hh)
    rw [heq]
    omega
  · have hdr : d.1 ≤ r - 1 := by omega
    rcases h with hzero | hlt
    · omega
    · have hmono := μ.rowLen_anti d.1 (r - 1) hdr
      omega

/-- One legal single-box addition to a Young diagram. -/
def addPartitionBox (μ : YoungDiagram) (r : ℕ) (h : AddablePartitionRow μ r) :
    YoungDiagram where
  cells := insert (r, μ.rowLen r) μ.cells
  isLowerSet := by
    intro c d hdc hc
    rcases Finset.mem_insert.mp hc with hc | hc
    · subst c
      by_cases hd : d = (r, μ.rowLen r)
      · exact Finset.mem_insert.mpr (Or.inl hd)
      · exact Finset.mem_insert_of_mem (mem_of_le_addable_box h hdc hd)
    · exact Finset.mem_insert_of_mem (μ.isLowerSet hdc hc)

@[simp] theorem mem_addPartitionBox (μ : YoungDiagram) (r : ℕ)
    (h : AddablePartitionRow μ r) (c : ℕ × ℕ) :
    c ∈ addPartitionBox μ r h ↔ c = (r, μ.rowLen r) ∨ c ∈ μ :=
  Finset.mem_insert

theorem le_addPartitionBox (μ : YoungDiagram) (r : ℕ)
    (h : AddablePartitionRow μ r) : μ ≤ addPartitionBox μ r h := by
  intro c hc
  exact (mem_addPartitionBox μ r h c).mpr (Or.inr hc)

@[simp] theorem partitionSize_addPartitionBox (μ : YoungDiagram) (r : ℕ)
    (h : AddablePartitionRow μ r) :
    partitionSize (addPartitionBox μ r h) = partitionSize μ + 1 := by
  apply Finset.card_insert_of_notMem
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
  exact lt_irrefl _

@[simp] theorem rowLen_addPartitionBox (μ : YoungDiagram) (r : ℕ)
    (h : AddablePartitionRow μ r) (i : ℕ) :
    (addPartitionBox μ r h).rowLen i = if i = r then μ.rowLen i + 1 else μ.rowLen i := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_addPartitionBox,
    YoungDiagram.mem_iff_lt_rowLen, Prod.mk.injEq]
  by_cases hir : i = r
  · subst i
    simp only [ite_true, true_and]
    omega
  · simp [hir]

theorem PartitionFits.addPartitionBox {n : ℕ} {μ : YoungDiagram}
    (hμ : PartitionFits n μ) {r : ℕ} (hr : r < n + 1)
    (h : AddablePartitionRow μ r) : PartitionFits n (addPartitionBox μ r h) := by
  unfold PartitionFits at *
  rw [rowLen_addPartitionBox, ite_eq_right (by omega)]
  exact hμ

end
end ModifiedCartan




