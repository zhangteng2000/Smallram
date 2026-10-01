import ModifiedCartan.PolynomialAlternantTranslation
import ModifiedCartan.PartitionAlternatingPolynomial
import Mathlib.Algebra.Polynomial.Roots

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem mvPolynomialTranslate_add (B : Type*) (a b : ℂ) (P : MvPolynomial B ℂ) :
    mvPolynomialTranslate B b (mvPolynomialTranslate B a P) =
      mvPolynomialTranslate B (a + b) P := by
  have h : (mvPolynomialTranslate B b).comp (mvPolynomialTranslate B a) =
      mvPolynomialTranslate B (a + b) := by
    ext i : 1
    simp only [AlgHom.comp_apply, mvPolynomialTranslate_X, map_add, mvPolynomialTranslate_C]
    ring
  exact AlgHom.congr_fun h P

theorem mvPolynomialTranslate_zero (B : Type*) (P : MvPolynomial B ℂ) :
    mvPolynomialTranslate B 0 P = P := by
  simp only [mvPolynomialTranslate, map_zero, add_zero, MvPolynomial.aeval_X_left_apply]

theorem mvPolynomialTranslate_injective (B : Type*) (a : ℂ) :
    Function.Injective (mvPolynomialTranslate B a) := by
  intro P Q h
  have hh := congrArg (mvPolynomialTranslate B (-a)) h
  simpa only [mvPolynomialTranslate_add, add_neg_cancel, mvPolynomialTranslate_zero] using hh

theorem polynomial_factorial_mul_taylor_coeff {R : Type*} [CommSemiring R]
    (p : Polynomial R) (a : R) (k : ℕ) :
    (k.factorial : R) * (p.taylor a).coeff k = (Polynomial.derivative^[k] p).eval a := by
  rw [Polynomial.taylor_coeff, ← Polynomial.factorial_smul_hasseDeriv]
  simp [nsmul_eq_mul]

theorem finSuccEquiv_translate {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℂ) (a : ℂ) :
    MvPolynomial.finSuccEquiv ℂ m (mvPolynomialTranslate (Fin (m + 1)) a P) =
      ((MvPolynomial.finSuccEquiv ℂ m P).map (mvPolynomialTranslate (Fin m) a).toRingHom).taylor
        (MvPolynomial.C a) := by
  have h : (MvPolynomial.finSuccEquiv ℂ m).toRingHom.comp
      (mvPolynomialTranslate (Fin (m + 1)) a).toRingHom =
      (Polynomial.taylorAlgHom (MvPolynomial.C a)).toRingHom.comp
        ((Polynomial.mapRingHom (mvPolynomialTranslate (Fin m) a).toRingHom).comp
          (MvPolynomial.finSuccEquiv ℂ m).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [finSuccEquiv_constant]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [mvPolynomialTranslate_X, MvPolynomial.finSuccEquiv_X_zero, finSuccEquiv_constant]
      · simp [mvPolynomialTranslate_X, MvPolynomial.finSuccEquiv_X_succ, finSuccEquiv_constant]
  exact RingHom.congr_fun h P

/-- The translated first-variable coefficient, multiplied by its factorial,
    is the translated value of the corresponding ordinary derivative.
    Auxiliary to `lem:KP-correspondence`. -/
theorem finSuccEquiv_translate_factorial_coeff {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) ℂ) (a : ℂ) (k : ℕ) :
    MvPolynomial.C (k.factorial : ℂ) *
      (MvPolynomial.finSuccEquiv ℂ m (mvPolynomialTranslate (Fin (m + 1)) a P)).coeff k =
      mvPolynomialTranslate (Fin m) a
        ((Polynomial.derivative^[k] (MvPolynomial.finSuccEquiv ℂ m P)).eval (MvPolynomial.C a)) := by
  rw [finSuccEquiv_translate]
  rw [map_natCast, polynomial_factorial_mul_taylor_coeff, Polynomial.iterate_derivative_map]
  have h := Polynomial.eval_map_apply (mvPolynomialTranslate (Fin m) a).toRingHom
    (p := Polynomial.derivative^[k] (MvPolynomial.finSuccEquiv ℂ m P)) (MvPolynomial.C a)
  change ((Polynomial.derivative^[k] (MvPolynomial.finSuccEquiv ℂ m P)).map
    (mvPolynomialTranslate (Fin m) a).toRingHom).eval
    (mvPolynomialTranslate (Fin m) a (MvPolynomial.C a)) = _ at h
  rw [mvPolynomialTranslate_C] at h
  exact h

theorem polynomial_mvCoefficients_eq_zero_of_scalar_eval {B : Type*}
    (p : Polynomial (MvPolynomial B ℂ))
    (hp : ∀ a : ℂ, p.eval (MvPolynomial.C a) = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective (MvPolynomial.C_injective B ℂ)).mono
  rintro _ ⟨a, rfl⟩
  exact hp a

end
end ModifiedCartan

#print axioms ModifiedCartan.finSuccEquiv_translate_factorial_coeff
