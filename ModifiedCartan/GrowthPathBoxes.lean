import ModifiedCartan.MinorGrowthPaths
import ModifiedCartan.SkewTableaux

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

def minorGrowthBox {n : ℕ} {μ : YoungDiagram} (i : LegalMinorRow n μ) : ℕ × ℕ :=
  (n - (i.val : ℕ), μ.rowLen (n - (i.val : ℕ)))

theorem minorGrowthBox_not_mem {n : ℕ} {μ : YoungDiagram} (i : LegalMinorRow n μ) :
    minorGrowthBox i ∉ μ := by
  simp [minorGrowthBox, YoungDiagram.mem_iff_lt_rowLen]

theorem minorGrowthBox_mem_grow {n : ℕ} {μ : YoungDiagram} (i : LegalMinorRow n μ) :
    minorGrowthBox i ∈ growMinorPartition i := by
  simp [growMinorPartition, minorGrowthBox]

def minorGrowthBoxes {n : ℕ} : {μ : YoungDiagram} → (k : ℕ) →
    MinorGrowthPath n μ k → Fin k → ℕ × ℕ
  | _, 0, _ => Fin.elim0
  | _, k + 1, p => Fin.cons (minorGrowthBox p.1) (minorGrowthBoxes k p.2)

theorem minorGrowthBoxes_not_mem_start {n : ℕ} {μ : YoungDiagram}
    (k : ℕ) (p : MinorGrowthPath n μ k) (j : Fin k) : minorGrowthBoxes k p j ∉ μ := by
  induction k generalizing μ with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    cases j using Fin.cases with
    | zero => simpa [minorGrowthBoxes] using minorGrowthBox_not_mem p.1
    | succ j =>
      intro hm
      apply ih p.2 j
      exact (le_addPartitionBox _ _ _) hm

theorem minorGrowthBoxes_mem_endpoint {n : ℕ} {μ : YoungDiagram}
    (k : ℕ) (p : MinorGrowthPath n μ k) (j : Fin k) :
    minorGrowthBoxes k p j ∈ minorGrowthEndpoint k p := by
  induction k generalizing μ with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    cases j using Fin.cases with
    | zero =>
      exact (le_minorGrowthEndpoint k p.2) (minorGrowthBox_mem_grow p.1)
    | succ j => exact ih p.2 j

theorem minorGrowthBoxes_injective {n : ℕ} {μ : YoungDiagram}
    (k : ℕ) (p : MinorGrowthPath n μ k) : Function.Injective (minorGrowthBoxes k p) := by
  induction k generalizing μ with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    apply Fin.cons_injective_of_injective
    · rintro ⟨j, hj⟩
      exact minorGrowthBoxes_not_mem_start k p.2 j
        (hj.symm ▸ minorGrowthBox_mem_grow p.1)
    · exact ih p.2

theorem mem_minorGrowthEndpoint_iff {n : ℕ} {μ : YoungDiagram}
    (k : ℕ) (p : MinorGrowthPath n μ k) (c : ℕ × ℕ) :
    c ∈ minorGrowthEndpoint k p ↔ c ∈ μ ∨ ∃ j, minorGrowthBoxes k p j = c := by
  induction k generalizing μ with
  | zero => simp [minorGrowthEndpoint]
  | succ k ih =>
    change c ∈ minorGrowthEndpoint k p.2 ↔ _
    rw [ih]
    simp only [growMinorPartition, mem_addPartitionBox, minorGrowthBoxes,
      Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ, minorGrowthBox]
    tauto

theorem mem_skew_endpoint_iff {n : ℕ} {μ : YoungDiagram}
    (k : ℕ) (p : MinorGrowthPath n μ k) (c : ℕ × ℕ) :
    c ∈ (minorGrowthEndpoint k p).cells \ μ.cells ↔
      ∃ j, minorGrowthBoxes k p j = c := by
  constructor
  · intro hc
    have hh := (mem_minorGrowthEndpoint_iff k p c).mp (Finset.mem_sdiff.mp hc).1
    exact hh.resolve_left (Finset.mem_sdiff.mp hc).2
  · rintro ⟨j, rfl⟩
    exact Finset.mem_sdiff.mpr
      ⟨minorGrowthBoxes_mem_endpoint k p j, minorGrowthBoxes_not_mem_start k p j⟩

/-- An insertion time cannot be later than the time of a box weakly below it. -/
theorem minorGrowthBoxes_index_le_of_le {n : ℕ} {μ : YoungDiagram}
    (k : ℕ) (p : MinorGrowthPath n μ k) {i j : Fin k}
    (h : minorGrowthBoxes k p i ≤ minorGrowthBoxes k p j) : i ≤ j := by
  induction k generalizing μ with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have hm : minorGrowthBoxes k p.2 i ∈ growMinorPartition p.1 :=
          (growMinorPartition p.1).isLowerSet h (minorGrowthBox_mem_grow p.1)
        exact (minorGrowthBoxes_not_mem_start k p.2 i hm).elim
      | succ j =>
        have hij : i ≤ j := ih p.2 h
        change (i : ℕ) + 1 ≤ (j : ℕ) + 1
        omega

end
end ModifiedCartan


