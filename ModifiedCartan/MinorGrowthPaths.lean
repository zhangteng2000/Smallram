import ModifiedCartan.PartitionMinorDerivative

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

/-- Legal row choices in the matrix order, opposite to the diagram row order. -/
abbrev LegalMinorRow (n : ℕ) (μ : YoungDiagram) :=
  {i : Fin (n + 1) // AddablePartitionRow μ (n - (i : ℕ))}

def growMinorPartition {n : ℕ} {μ : YoungDiagram} (i : LegalMinorRow n μ) :
    YoungDiagram := addPartitionBox μ (n - (i.val : ℕ)) i.property

def MinorGrowthPath (n : ℕ) : YoungDiagram → ℕ → Type
  | _, 0 => PUnit
  | μ, k + 1 => Σ i : LegalMinorRow n μ, MinorGrowthPath n (growMinorPartition i) k

instance minorGrowthPathFintype (n : ℕ) :
    (μ : YoungDiagram) → (k : ℕ) → Fintype (MinorGrowthPath n μ k)
  | _, 0 => inferInstanceAs (Fintype PUnit)
  | μ, k + 1 =>
    letI : ∀ i : LegalMinorRow n μ, Fintype (MinorGrowthPath n (growMinorPartition i) k) :=
      fun i => minorGrowthPathFintype n (growMinorPartition i) k
    inferInstanceAs (Fintype (Σ i : LegalMinorRow n μ, MinorGrowthPath n (growMinorPartition i) k))

def minorGrowthEndpoint {n : ℕ} : {μ : YoungDiagram} → (k : ℕ) →
    MinorGrowthPath n μ k → YoungDiagram
  | μ, 0, _ => μ
  | _, k + 1, p => minorGrowthEndpoint k p.2

theorem growMinorPartition_fits {n : ℕ} {μ : YoungDiagram}
    (h : PartitionFits n μ) (i : LegalMinorRow n μ) :
    PartitionFits n (growMinorPartition i) :=
  h.addPartitionBox (by omega) i.property

@[simp] theorem partitionSize_growMinorPartition {n : ℕ} {μ : YoungDiagram}
    (i : LegalMinorRow n μ) :
    partitionSize (growMinorPartition i) = partitionSize μ + 1 :=
  partitionSize_addPartitionBox _ _ _

theorem partitionSize_minorGrowthEndpoint {n : ℕ} {μ : YoungDiagram}
    (k : ℕ) (p : MinorGrowthPath n μ k) :
    partitionSize (minorGrowthEndpoint k p) = partitionSize μ + k := by
  induction k generalizing μ with
  | zero => rfl
  | succ k ih =>
    change partitionSize (minorGrowthEndpoint k p.2) = _
    rw [ih, partitionSize_growMinorPartition]
    omega

theorem minorGrowthEndpoint_fits {n : ℕ} {μ : YoungDiagram}
    (h : PartitionFits n μ) (k : ℕ) (p : MinorGrowthPath n μ k) :
    PartitionFits n (minorGrowthEndpoint k p) := by
  induction k generalizing μ with
  | zero => exact h
  | succ k ih => exact ih (growMinorPartition_fits h p.1) p.2

theorem le_minorGrowthEndpoint {n : ℕ} {μ : YoungDiagram}
    (k : ℕ) (p : MinorGrowthPath n μ k) : μ ≤ minorGrowthEndpoint k p := by
  induction k generalizing μ with
  | zero => exact le_rfl
  | succ k ih => exact (le_addPartitionBox _ _ _).trans (ih p.2)

theorem derivative_partitionPolynomialMinor_sum_legal {n : ℕ} {μ : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ) (hμ : PartitionFits n μ) :
    (partitionPolynomialMinor μ p).derivative =
      ∑ i : LegalMinorRow n μ, partitionPolynomialMinor (growMinorPartition i) p := by
  rw [derivative_partitionPolynomialMinor μ p hμ, Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  let e : {i : Fin (n + 1) // i ∈ Finset.univ.filter
      (fun i : Fin (n + 1) => AddablePartitionRow μ (n - (i : ℕ)))} ≃ LegalMinorRow n μ :=
    Equiv.subtypeEquivRight (by intro i; simp)
  exact e.sum_comp (fun i => partitionPolynomialMinor (growMinorPartition i) p)

/-- Each legal path of `k` single-box additions contributes exactly once. -/
theorem iterate_derivative_partitionPolynomialMinor {n : ℕ} {μ : YoungDiagram}
    (p : Fin (n + 1) → Polynomial ℂ) (hμ : PartitionFits n μ) (k : ℕ) :
    Polynomial.derivative^[k] (partitionPolynomialMinor μ p) =
      ∑ path : MinorGrowthPath n μ k,
        partitionPolynomialMinor (minorGrowthEndpoint k path) p := by
  induction k generalizing μ with
  | zero =>
    haveI : Unique (MinorGrowthPath n μ 0) := inferInstanceAs (Unique PUnit)
    simp [minorGrowthEndpoint]
  | succ k ih =>
    rw [Function.iterate_succ_apply,
      derivative_partitionPolynomialMinor_sum_legal p hμ,
      Polynomial.iterate_derivative_sum]
    change (∑ i : LegalMinorRow n μ,
      Polynomial.derivative^[k] (partitionPolynomialMinor (growMinorPartition i) p)) =
      ∑ path : (Σ i : LegalMinorRow n μ, MinorGrowthPath n (growMinorPartition i) k),
        partitionPolynomialMinor (minorGrowthEndpoint k path.2) p
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    exact ih (growMinorPartition_fits hμ i)

end
end ModifiedCartan



