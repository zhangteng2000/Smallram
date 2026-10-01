import ModifiedCartan.PolynomialJetSupport
import ModifiedCartan.MvPolynomialTranslationJets
import Mathlib.LinearAlgebra.Matrix.Adjugate

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem matrix_det_updateRow_one {N : ℕ} (j : Fin N) (v : Fin N → ℂ) :
    ((1 : Matrix (Fin N) (Fin N) ℂ).updateRow j v).det = v j := by
  rw [← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
  rfl

theorem polynomialJet_zero_iff_coeff_zero (p : Polynomial ℂ) (k : ℕ) :
    (Polynomial.derivative^[k] p).eval 0 = 0 ↔ p.coeff k = 0 := by
  have h := polynomial_factorial_mul_taylor_coeff p 0 k
  rw [Polynomial.taylor_zero] at h
  rw [← h, mul_eq_zero]
  exact or_iff_right (by exact_mod_cast Nat.factorial_ne_zero k)

/-- A normalized jet basis cannot have any coefficient above its designated
    degree, because replacing that jet row would give a forbidden coordinate.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomialJet_zero_above_profile {n : ℕ} (τ : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ)
    (hp : ∀ i j, (Polynomial.derivative^[partitionMinorOrders n τ i] (p j)).eval 0 =
      if i = j then 1 else 0)
    (hs : ∀ μ : YoungDiagram, ¬ μ ≤ τ → (partitionPolynomialMinor μ p).eval 0 = 0)
    (j : Fin (n + 1)) (k : ℕ) (hk : partitionMinorOrders n τ j < k) :
    (Polynomial.derivative^[k] (p j)).eval 0 = 0 := by
  let e := Function.update (partitionMinorOrders n τ) j k
  have he : (∑ i, partitionMinorOrders n τ i) < ∑ i, e i := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i = j
      · subst i
        simpa only [e, Function.update_self] using hk.le
      · simp only [e, Function.update_of_ne hi, le_refl]
    · exact ⟨j, Finset.mem_univ j, by simpa only [e, Function.update_self] using hk⟩
  have hz := polynomialJetDet_zero_of_order_sum_gt τ p 0 hs e he
  have hM : (fun i l : Fin (n + 1) => (Polynomial.derivative^[e i] (p l)).eval 0) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).updateRow j
        (fun l => (Polynomial.derivative^[k] (p l)).eval 0) := by
    funext i l
    by_cases hi : i = j
    · subst i
      simp only [e, Function.update_self, Matrix.updateRow_self]
    · simp only [e, Function.update_of_ne hi, Matrix.updateRow_ne hi, hp, Matrix.one_apply]
  erw [hM, matrix_det_updateRow_one] at hz
  exact hz

/-- The degree profile follows from the normalized jets and coordinate support,
    rather than being imposed as a new hypothesis on the eigenspace. -/
theorem polynomial_natDegree_eq_of_identity_jets_support {n : ℕ} (τ : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ)
    (hp : ∀ i j, (Polynomial.derivative^[partitionMinorOrders n τ i] (p j)).eval 0 =
      if i = j then 1 else 0)
    (hs : ∀ μ : YoungDiagram, ¬ μ ≤ τ → (partitionPolynomialMinor μ p).eval 0 = 0)
    (j : Fin (n + 1)) : (p j).natDegree = partitionMinorOrders n τ j := by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    exact (polynomialJet_zero_iff_coeff_zero (p j) k).mp
      (polynomialJet_zero_above_profile τ p hp hs j k hk)
  · apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    have he := (polynomialJet_zero_iff_coeff_zero (p j) (partitionMinorOrders n τ j)).mpr hz
    rw [hp, if_pos rfl] at he
    exact one_ne_zero he

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomial_natDegree_eq_of_identity_jets_support