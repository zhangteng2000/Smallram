import ModifiedCartan.DividedPowerPolynomials
import ModifiedCartan.OrderedDeltaDeterminant
import ModifiedCartan.MinorTranslation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem partitionMinorOrders_eq_iff {n : ℕ} (μ ν : YoungDiagram)
    (hμ : PartitionFits n μ) (hν : PartitionFits n ν) :
    partitionMinorOrders n μ = partitionMinorOrders n ν ↔ μ = ν := by
  constructor
  · intro h
    apply le_antisymm
    · exact (partition_le_iff_minorOrders_le hμ).mpr (fun i => (congrFun h i).le)
    · exact (partition_le_iff_minorOrders_le hν).mpr (fun i => (congrFun h i).ge)
  · rintro rfl
    rfl

theorem dividedPowerPartitionMinor_zero {n : ℕ} (μ ν : YoungDiagram)
    (hμ : PartitionFits n μ) (hν : PartitionFits n ν) :
    (partitionPolynomialMinor μ
      (fun j : Fin (n + 1) => complexDividedPowerPolynomial (partitionMinorOrders n ν j))).eval 0 =
        if μ = ν then 1 else 0 := by
  rw [partitionPolynomialMinor_of_fits hμ, polynomialDerivativeMinor_eval]
  simp only [complexDividedPowerPolynomial_jet_zero]
  erw [orderedDeltaMatrix_det _ _ (partitionMinorOrders_strictMono n μ)
    (partitionMinorOrders_strictMono n ν)]
  simp only [partitionMinorOrders_eq_iff μ ν hμ hν]

/-- The exact factorial and tableau coefficient of a translated divided-power
    minor, derived from the repository's finite minor translation theorem.
    Auxiliary to KP (4.8) for manuscript `lem:KP-correspondence`. -/
theorem dividedPowerPartitionMinor_eval {n : ℕ} (μ ν : YoungDiagram)
    (hν : PartitionFits n ν) (t : ℂ) :
    (partitionPolynomialMinor μ
      (fun j : Fin (n + 1) => complexDividedPowerPolynomial (partitionMinorOrders n ν j))).eval t =
        (standardSkewTableauCount ν μ : ℂ) /
          ((partitionSize ν - partitionSize μ).factorial : ℂ) * t ^ (partitionSize ν - partitionSize μ) := by
  have h := partitionPolynomialMinor_translation μ
    (fun j : Fin (n + 1) => complexDividedPowerPolynomial (partitionMinorOrders n ν j))
    hν (fun j => (complexDividedPowerPolynomial_natDegree _).le) 0 t
  rw [zero_add, Finset.sum_eq_single (⟨ν, le_rfl⟩ : Subpartition ν)] at h
  · simpa only [dividedPowerPartitionMinor_zero ν ν hν hν, ite_true, mul_one] using h
  · intro κ hκ hne
    have hv : κ.val ≠ ν := fun he => hne (Subtype.ext he)
    rw [dividedPowerPartitionMinor_zero κ.val ν (hν.of_le κ.property) hν,
      ite_eq_right hv, mul_zero]
  · simp

end
end ModifiedCartan

#print axioms ModifiedCartan.dividedPowerPartitionMinor_eval
