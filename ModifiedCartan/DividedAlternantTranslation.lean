import ModifiedCartan.PolynomialAlternantTranslation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem partition_colLen_mono {μ ν : YoungDiagram} (h : μ ≤ ν) (c : ℕ) :
    μ.colLen c ≤ ν.colLen c := by
  by_contra! hn
  have hc : (ν.colLen c, c) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hn
  have := YoungDiagram.mem_iff_lt_colLen.mp (h hc)
  omega

theorem finiteDividedAlternant_hasAlternatingCoefficients {m : ℕ} (e : Fin m → ℕ) :
    HasAlternatingCoefficients (finiteDividedAlternant e) := by
  rw [finiteDividedAlternant_eq_det]
  exact polynomialAlternant_hasAlternatingCoefficients
    (fun j => complexDividedPowerPolynomial (e j))

theorem finiteDividedAlternant_translate_hasAlternatingCoefficients {m : ℕ}
    (e : Fin m → ℕ) (a : ℂ) :
    HasAlternatingCoefficients (mvPolynomialTranslate (Fin m) a (finiteDividedAlternant e)) := by
  rw [finiteDividedAlternant_eq_det]
  change HasAlternatingCoefficients (mvPolynomialTranslate (Fin m) a
    (polynomialAlternant (fun j => complexDividedPowerPolynomial (e j))))
  rw [polynomialAlternant_translate]
  exact polynomialAlternant_hasAlternatingCoefficients _

theorem finiteDividedAlternant_partition_coeff {m : ℕ} (μ ν : YoungDiagram)
    (hμ : μ.colLen 0 ≤ m) (hν : ν.colLen 0 ≤ m) :
    MvPolynomial.coeff (finiteExponent (partitionAlternantExponent m ν))
      (finiteDividedAlternant (partitionAlternantExponent m μ)) =
      multiDegreeInverseFactorial (finiteExponent (partitionAlternantExponent m ν)) *
        (if μ = ν then 1 else 0) := by
  rw [finiteDividedAlternant, mvDividedPowerNormalize_coeff,
    finiteExponent_partitionAlternant, finiteAlternant_partition_coeff μ ν hμ hν]

theorem dividedAlternant_sum_partition_coeff {m : ℕ} (ω κ : YoungDiagram)
    (hω : ω.colLen 0 ≤ m) (hκ : κ.colLen 0 ≤ m) (c : YoungDiagram → ℂ) :
    MvPolynomial.coeff (finiteExponent (partitionAlternantExponent m κ))
      (∑ μ : Subpartition ω, MvPolynomial.C (c μ.val) *
        finiteDividedAlternant (partitionAlternantExponent m μ.val)) =
      multiDegreeInverseFactorial (finiteExponent (partitionAlternantExponent m κ)) *
        (if κ ≤ ω then c κ else 0) := by
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  have hc (μ : Subpartition ω) := finiteDividedAlternant_partition_coeff μ.val κ
    ((partition_colLen_mono μ.property 0).trans hω) hκ
  simp_rw [hc]
  by_cases hk : κ ≤ ω
  · rw [ite_eq_left hk, Finset.sum_eq_single (⟨κ, hk⟩ : Subpartition ω)]
    · simp only [ite_true, mul_one]
      exact mul_comm _ _
    · intro μ _ hne
      have hn : μ.val ≠ κ := fun h => hne (Subtype.ext h)
      simp only [ite_eq_right hn, mul_zero]
    · simp
  · rw [ite_eq_right hk, mul_zero]
    apply Finset.sum_eq_zero
    intro μ _
    have hn : μ.val ≠ κ := fun h => hk (h ▸ μ.property)
    simp only [ite_eq_right hn, mul_zero]

/-- Literal polynomial form of KP (4.8): simultaneous translation of all
    variables in the divided-power alternating basis. This is proved from
    derivative minors and coefficient extensionality, with no exterior-power
    formula assumed. Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem finiteDividedAlternant_translation {n : ℕ} (ν : YoungDiagram)
    (hν : PartitionFits n ν) (a : ℂ) :
    mvPolynomialTranslate (Fin (n + 1)) a
      (finiteDividedAlternant (partitionAlternantExponent (n + 1) ν)) =
      ∑ μ : Subpartition ν,
        MvPolynomial.C ((standardSkewTableauCount ν μ.val : ℂ) /
          ((partitionSize ν - partitionSize μ.val).factorial : ℂ) *
            a ^ (partitionSize ν - partitionSize μ.val)) *
          finiteDividedAlternant (partitionAlternantExponent (n + 1) μ.val) := by
  apply alternatingPolynomial_ext
    (finiteDividedAlternant_translate_hasAlternatingCoefficients _ a)
    (HasAlternatingCoefficients.sum Finset.univ _ (fun μ _ =>
      (finiteDividedAlternant_hasAlternatingCoefficients _).C_mul _))
  intro κ hκ
  rw [dividedAlternant_translate_partition_coeff κ ν
    ((partitionFits_iff_height_le κ).mpr hκ) hν a,
    dividedAlternant_sum_partition_coeff ν κ ((partitionFits_iff_height_le ν).mp hν) hκ
      (fun μ => (standardSkewTableauCount ν μ : ℂ) /
        ((partitionSize ν - partitionSize μ).factorial : ℂ) *
          a ^ (partitionSize ν - partitionSize μ))]
  by_cases hk : κ ≤ ν
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, standardSkewTableauCount_of_not_le hk]
    simp

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteDividedAlternant_translation
