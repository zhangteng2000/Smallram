import ModifiedCartan.OrderedPartitionExponents
import ModifiedCartan.PolynomialDeterminantCoefficients

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def HasAlternatingCoefficients {m : ℕ} (P : MvPolynomial (Fin m) ℂ) : Prop :=
  ∀ (e : Fin m → ℕ) (σ : Equiv.Perm (Fin m)),
    MvPolynomial.coeff (finiteExponent (e ∘ σ)) P =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * MvPolynomial.coeff (finiteExponent e) P

theorem polynomialAlternant_hasAlternatingCoefficients {m : ℕ}
    (p : Fin m → Polynomial ℂ) : HasAlternatingCoefficients (polynomialAlternant p) := by
  intro e σ
  simp only [polynomialAlternant_coeff]
  convert Matrix.det_permute σ (fun i j : Fin m => (p j).coeff (e i)) using 1 <;> rfl

theorem HasAlternatingCoefficients.sum {m : ℕ} {I : Type*} (s : Finset I)
    (P : I → MvPolynomial (Fin m) ℂ) (hP : ∀ i ∈ s, HasAlternatingCoefficients (P i)) :
    HasAlternatingCoefficients (∑ i ∈ s, P i) := by
  intro e σ
  simp only [MvPolynomial.coeff_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => hP i hi e σ)

theorem HasAlternatingCoefficients.C_mul {m : ℕ} {P : MvPolynomial (Fin m) ℂ}
    (hP : HasAlternatingCoefficients P) (c : ℂ) :
    HasAlternatingCoefficients (MvPolynomial.C c * P) := by
  intro e σ
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, hP]
  ring

theorem HasAlternatingCoefficients.coeff_zero_of_not_injective {m : ℕ}
    {P : MvPolynomial (Fin m) ℂ} (hP : HasAlternatingCoefficients P)
    (e : Fin m → ℕ) (he : ¬ Function.Injective e) :
    MvPolynomial.coeff (finiteExponent e) P = 0 := by
  obtain ⟨i, j, heq, hij⟩ : ∃ i j, e i = e j ∧ i ≠ j := by
    simpa only [Function.Injective, not_forall, exists_prop] using he
  have hcomp : e ∘ Equiv.swap i j = e := funext (Equiv.apply_swap_eq_self heq)
  have h := hP e (Equiv.swap i j)
  rw [hcomp, Equiv.Perm.sign_swap hij] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at h
  exact CharZero.eq_neg_self_iff.mp h

/-- A finite alternating polynomial is determined by its coefficients at
    partition-plus-staircase exponents. Auxiliary to `lem:KP-correspondence`. -/
theorem alternatingPolynomial_ext {m : ℕ} {P Q : MvPolynomial (Fin m) ℂ}
    (hP : HasAlternatingCoefficients P) (hQ : HasAlternatingCoefficients Q)
    (hc : ∀ μ : YoungDiagram, μ.colLen 0 ≤ m →
      MvPolynomial.coeff (finiteExponent (partitionAlternantExponent m μ)) P =
        MvPolynomial.coeff (finiteExponent (partitionAlternantExponent m μ)) Q) : P = Q := by
  apply MvPolynomial.ext
  intro d
  let e : Fin m → ℕ := fun i => d i
  have hd : finiteExponent e = d := by ext i; rfl
  rw [← hd]
  by_cases he : Function.Injective e
  · obtain ⟨σ, hσ⟩ := exists_perm_strictAnti e he
    obtain ⟨μ, hμ, hμe⟩ := exists_partitionAlternantExponent (e ∘ σ) hσ
    have hh := hc μ hμ
    rw [hμe, hP, hQ] at hh
    exact mul_left_cancel₀ (by exact_mod_cast (Equiv.Perm.sign σ).ne_zero) hh
  · rw [hP.coeff_zero_of_not_injective e he, hQ.coeff_zero_of_not_injective e he]

end
end ModifiedCartan

#print axioms ModifiedCartan.alternatingPolynomial_ext
