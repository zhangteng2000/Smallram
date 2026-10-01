import ModifiedCartan.PolynomialValueSpan
import ModifiedCartan.KPCoefficientDegree
import ModifiedCartan.KPGeneratedCommutative
import ModifiedCartan.KPColumnSupportedExpansion

open scoped Classical BigOperators MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The coefficient of t^k in the actual KP operator polynomial. -/
def kpBetaPowerCoefficient (μ : YoungDiagram) (z : A → ℂ) (k : ℕ) : ℂ[Equiv.Perm A] :=
  ∑ I : SizedLetterSubset A (partitionSize μ),
    (kpWeightPolynomial z I.val).coeff k • kpAlpha μ I.val

theorem kpBeta_eq_polynomialCombination (μ : YoungDiagram) (z : A → ℂ) (a : ℂ) :
    kpBeta μ z a = ∑ I : SizedLetterSubset A (partitionSize μ),
      (kpWeightPolynomial z I.val).eval a • kpAlpha μ I.val := by
  simp only [kpWeightPolynomial_eval]
  exact sum_sizedLetterSubset (partitionSize μ)
    (fun I => (∏ l ∈ Finset.univ \ I, (a + z l)) • kpAlpha μ I)

theorem kpBeta_eq_sum_powerCoefficients (μ : YoungDiagram) (z : A → ℂ) (a : ℂ) :
    kpBeta μ z a = ∑ k ∈ Finset.range (Fintype.card A + 1),
      a ^ k • kpBetaPowerCoefficient μ z k := by
  rw [kpBeta_eq_polynomialCombination]
  apply polynomialCombination_eval_eq_sum
  intro I
  exact lt_of_le_of_lt (kpWeightPolynomial_natDegree_le z I.val)
    (by have hh := Finset.card_le_card (Finset.sdiff_subset (s := Finset.univ) (t := I.val))
        simpa only [Finset.card_univ] using Nat.lt_succ_of_le hh)

theorem kpBetaPowerCoefficient_mem_of_values (μ : YoungDiagram) (z : A → ℂ)
    (S : Submodule ℂ ℂ[Equiv.Perm A]) (h : ∀ a, kpBeta μ z a ∈ S) (k : ℕ) :
    kpBetaPowerCoefficient μ z k ∈ S := by
  apply polynomialCombination_coeff_mem _ _ S
  intro a
  rw [← kpBeta_eq_polynomialCombination]
  exact h a

/-- Traditional Bethe algebra: the single-column generators at every center,
    as defined in Karp--Purbhoo Section 2.4.1. This definition does not assert
    that arbitrary-partition KP generators lie in it. -/
def betheAlgebra (z : A → ℂ) : Subalgebra ℂ ℂ[Equiv.Perm A] :=
  Algebra.adjoin ℂ (Set.range fun kt : ℕ × ℂ => kpBeta (columnPartition kt.1) z kt.2)

theorem kpBeta_column_mem_bethe (z : A → ℂ) (k : ℕ) (t : ℂ) :
    kpBeta (columnPartition k) z t ∈ betheAlgebra z :=
  Algebra.subset_adjoin ⟨(k, t), rfl⟩

theorem kpBetaPowerCoefficient_column_mem_bethe (z : A → ℂ) (q k : ℕ) :
    kpBetaPowerCoefficient (columnPartition q) z k ∈ betheAlgebra z :=
  kpBetaPowerCoefficient_mem_of_values _ z (betheAlgebra z).toSubmodule
    (kpBeta_column_mem_bethe z q) k

/-- The coefficient and value definitions of the traditional Bethe algebra
    agree. No assertion from the literature is assumed. -/
theorem betheAlgebra_eq_adjoin_coefficients (z : A → ℂ) :
    betheAlgebra z = Algebra.adjoin ℂ
      (Set.range fun qk : ℕ × ℕ => kpBetaPowerCoefficient (columnPartition qk.1) z qk.2) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x ⟨⟨q, a⟩, rfl⟩
    dsimp only
    rw [kpBeta_eq_sum_powerCoefficients]
    apply Subalgebra.sum_mem
    intro k _
    have hm : kpBetaPowerCoefficient (columnPartition q) z k ∈ Algebra.adjoin ℂ
        (Set.range fun qk : ℕ × ℕ => kpBetaPowerCoefficient (columnPartition qk.1) z qk.2) :=
      Algebra.subset_adjoin ⟨(q, k), rfl⟩
    exact Subalgebra.smul_mem _ hm _
  · apply Algebra.adjoin_le
    rintro x ⟨⟨q, k⟩, rfl⟩
    exact kpBetaPowerCoefficient_column_mem_bethe z q k

theorem betheAlgebra_le_kpGeneratedAlgebra (z : A → ℂ) :
    betheAlgebra z ≤ kpGeneratedAlgebra z := by
  apply Algebra.adjoin_le
  rintro x ⟨⟨k, a⟩, rfl⟩
  exact kpBeta_mem_generated (columnPartition k) z a

theorem betheAlgebra_shift (z : A → ℂ) (t : ℂ) :
    betheAlgebra (fun i => z i + t) = betheAlgebra z := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x ⟨⟨k, a⟩, rfl⟩
    change kpBeta (columnPartition k) (fun i => z i + t) a ∈ betheAlgebra z
    rw [← kpBeta_parameter_shift]
    exact kpBeta_column_mem_bethe z k (a + t)
  · apply Algebra.adjoin_le
    rintro x ⟨⟨k, a⟩, rfl⟩
    have hm := kpBeta_column_mem_bethe (fun i => z i + t) k (a - t)
    rw [← kpBeta_parameter_shift, sub_add_cancel] at hm
    exact hm

end
end ModifiedCartan

#print axioms ModifiedCartan.betheAlgebra_eq_adjoin_coefficients
#print axioms ModifiedCartan.betheAlgebra_le_kpGeneratedAlgebra