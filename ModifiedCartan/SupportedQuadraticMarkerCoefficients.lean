import ModifiedCartan.AmbientFactorizationLaurentSeries
import ModifiedCartan.ComplementMarkerClassification

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem supportedPowerSumQuadratic_marker_coeff {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (d : A →₀ ℕ) :
    MvPolynomial.coeff d ((supportedPowerSumQuadratic A B).coeff θ) =
      ∑ p : SupportedPermutationData A × SupportedPermutationData A,
        if p.1.2.val * p.2.2.val = θ ∧ complementMarkerDegree p.1.1 p.2.1 = d
        then supportedPowerSumLaurentWeight B p else 0 := by
  rw [supportedPowerSumQuadratic]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hm : p.1.2.val * p.2.2.val = θ <;>
    by_cases hd : complementMarkerDegree p.1.1 p.2.1 = d <;>
    simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, hm, hd]

theorem supportedPowerSumQuadratic_union_inter_coeff {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (U Z : Finset A) (hZ : Z ⊆ U) :
    MvPolynomial.coeff (complementMarkerDegree U Z) ((supportedPowerSumQuadratic A B).coeff θ) =
      ambientFactorizationLaurentSeries B θ U Z := by
  rw [supportedPowerSumQuadratic_marker_coeff]
  calc
    _ = ∑ p : SupportedPermutationData A × SupportedPermutationData A,
        if h : p.1.1 ∪ p.2.1 = U ∧ p.1.1 ∩ p.2.1 = Z ∧ p.1.2.val * p.2.2.val = θ
        then supportedPowerSumLaurentWeight B p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [complementMarkerDegree_eq_iff p.1.1 p.2.1 U Z hZ]
      by_cases hm : p.1.2.val * p.2.2.val = θ <;>
        by_cases hu : p.1.1 ∪ p.2.1 = U <;> by_cases hi : p.1.1 ∩ p.2.1 = Z <;>
        simp [hm, hu, hi]
    _ = _ := sum_dite_eq_sum_subtype _ _

theorem supportedPowerSumQuadratic_marker_coeff_zero {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (d : A →₀ ℕ) (hd : ¬ ∀ a, d a ≤ 2) :
    MvPolynomial.coeff d ((supportedPowerSumQuadratic A B).coeff θ) = 0 := by
  rw [supportedPowerSumQuadratic_marker_coeff]
  apply Finset.sum_eq_zero
  intro p hp
  have hn : complementMarkerDegree p.1.1 p.2.1 ≠ d := by
    intro he
    apply hd
    intro a
    rw [← he]
    exact complementMarkerDegree_le_two p.1.1 p.2.1 a
  simp [hn]

end
end ModifiedCartan

