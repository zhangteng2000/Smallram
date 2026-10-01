import ModifiedCartan.DividedAlternantTranslation
import ModifiedCartan.KPJointDividedContraction

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finitePartitionDividedPolynomial_eq_sum (m N : ℕ) (χ : YoungDiagram → ℂ) :
    finitePartitionDividedPolynomial m N χ =
      ∑ μ : Subpartition (partitionSquare N), MvPolynomial.C (χ μ.val) *
        finiteDividedAlternant (partitionAlternantExponent m μ.val) := by
  simp only [finitePartitionDividedPolynomial, finitePartitionAlternatingPolynomial,
    map_sum, mvDividedPowerNormalize_C_mul, finiteDividedAlternant]

theorem finitePartitionDividedPolynomial_hasAlternatingCoefficients
    (m N : ℕ) (χ : YoungDiagram → ℂ) :
    HasAlternatingCoefficients (finitePartitionDividedPolynomial m N χ) := by
  rw [finitePartitionDividedPolynomial_eq_sum]
  exact HasAlternatingCoefficients.sum Finset.univ _ (fun μ _ =>
    (finiteDividedAlternant_hasAlternatingCoefficients _).C_mul _)

theorem finitePartitionDividedPolynomial_translate_hasAlternatingCoefficients
    (m N : ℕ) (χ : YoungDiagram → ℂ) (a : ℂ) :
    HasAlternatingCoefficients (mvPolynomialTranslate (Fin m) a
      (finitePartitionDividedPolynomial m N χ)) := by
  rw [finitePartitionDividedPolynomial_eq_sum]
  simp only [map_sum, map_mul, mvPolynomialTranslate_C]
  exact HasAlternatingCoefficients.sum Finset.univ _ (fun μ _ =>
    (finiteDividedAlternant_translate_hasAlternatingCoefficients _ a).C_mul _)

theorem finitePartitionDividedPolynomial_coeff {m N : ℕ} (hN : N ≤ m)
    (χ : YoungDiagram → ℂ) (κ : YoungDiagram) (hκ : κ.colLen 0 ≤ m) :
    MvPolynomial.coeff (finiteExponent (partitionAlternantExponent m κ))
      (finitePartitionDividedPolynomial m N χ) =
      multiDegreeInverseFactorial (finiteExponent (partitionAlternantExponent m κ)) *
        (if κ ≤ partitionSquare N then χ κ else 0) := by
  rw [finitePartitionDividedPolynomial_eq_sum]
  exact dividedAlternant_sum_partition_coeff _ κ
    ((subpartitionSquare_height_le ⟨partitionSquare N, le_rfl⟩).trans hN) hκ χ

theorem kpJointValuePolynomial_eval_zero_of_not_le_square (N : ℕ) (χ : YoungDiagram → ℂ)
    (κ : YoungDiagram) (hκ : ¬ κ ≤ partitionSquare N) (a : ℂ) :
    (kpJointValuePolynomial N χ κ).eval a = 0 := by
  rw [kpJointValuePolynomial_eval]
  apply Finset.sum_eq_zero
  intro ν _
  have hn : ¬ κ ≤ ν.val := fun h => hκ (h.trans ν.property)
  rw [standardSkewTableauCount_of_not_le hn]
  simp

theorem finitePartitionDividedPolynomial_translate_coeff {n N : ℕ} (hN : N ≤ n + 1)
    (χ : YoungDiagram → ℂ) (κ : YoungDiagram) (hκ : PartitionFits n κ) (a : ℂ) :
    MvPolynomial.coeff (finiteExponent (partitionAlternantExponent (n + 1) κ))
      (mvPolynomialTranslate (Fin (n + 1)) a (finitePartitionDividedPolynomial (n + 1) N χ)) =
      multiDegreeInverseFactorial (finiteExponent (partitionAlternantExponent (n + 1) κ)) *
        (kpJointValuePolynomial N χ κ).eval a := by
  rw [finitePartitionDividedPolynomial_eq_sum]
  simp only [map_sum, map_mul, mvPolynomialTranslate_C,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  have hc (ν : Subpartition (partitionSquare N)) := dividedAlternant_translate_partition_coeff
    κ ν.val hκ ((partitionFits_iff_height_le ν.val).mpr
      ((subpartitionSquare_height_le ν).trans hN)) a
  simp_rw [hc]
  rw [kpJointValuePolynomial_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  ring

/-- The assembled divided alternating polynomial has exactly the same
    tableau translation as the actual KP eigenvalue polynomials. No
    decomposability is required or assumed. Auxiliary to `lem:KP-correspondence`. -/
theorem finitePartitionDividedPolynomial_translation {n N : ℕ} (hN : N ≤ n + 1)
    (χ : YoungDiagram → ℂ) (a : ℂ) :
    mvPolynomialTranslate (Fin (n + 1)) a (finitePartitionDividedPolynomial (n + 1) N χ) =
      finitePartitionDividedPolynomial (n + 1) N
        (fun μ => (kpJointValuePolynomial N χ μ).eval a) := by
  apply alternatingPolynomial_ext
    (finitePartitionDividedPolynomial_translate_hasAlternatingCoefficients _ _ χ a)
    (finitePartitionDividedPolynomial_hasAlternatingCoefficients _ _ _)
  intro κ hκ
  rw [finitePartitionDividedPolynomial_translate_coeff hN χ κ
    ((partitionFits_iff_height_le κ).mpr hκ) a,
    finitePartitionDividedPolynomial_coeff hN _ κ hκ]
  by_cases hk : κ ≤ partitionSquare N
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, kpJointValuePolynomial_eval_zero_of_not_le_square N χ κ hk a]

end
end ModifiedCartan

#print axioms ModifiedCartan.finitePartitionDividedPolynomial_translation
