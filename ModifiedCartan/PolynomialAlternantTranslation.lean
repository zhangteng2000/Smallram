import ModifiedCartan.AlternatingPolynomialExt
import ModifiedCartan.DividedPowerAlternants
import ModifiedCartan.DividedPowerPartitionMinors

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def mvPolynomialTranslate (B : Type*) (a : ℂ) :
    MvPolynomial B ℂ →ₐ[ℂ] MvPolynomial B ℂ :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C a)

theorem mvPolynomialTranslate_C (B : Type*) (a c : ℂ) :
    mvPolynomialTranslate B a (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [mvPolynomialTranslate]

theorem mvPolynomialTranslate_X (B : Type*) (a : ℂ) (i : B) :
    mvPolynomialTranslate B a (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C a := by
  simp [mvPolynomialTranslate]

theorem mvPolynomialTranslate_eval₂ {B : Type*} (a : ℂ) (i : B) (p : Polynomial ℂ) :
    mvPolynomialTranslate B a (p.eval₂ MvPolynomial.C (MvPolynomial.X i)) =
      (p.taylor a).eval₂ MvPolynomial.C (MvPolynomial.X i) := by
  rw [Polynomial.taylor_apply, Polynomial.eval₂_comp, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  have h := Polynomial.hom_eval₂ p MvPolynomial.C (mvPolynomialTranslate B a).toRingHom
    (MvPolynomial.X i)
  have hc : (mvPolynomialTranslate B a).toRingHom.comp MvPolynomial.C = MvPolynomial.C := by
    ext c : 1
    exact mvPolynomialTranslate_C B a c
  rw [hc] at h
  change mvPolynomialTranslate B a (p.eval₂ MvPolynomial.C (MvPolynomial.X i)) =
    p.eval₂ MvPolynomial.C (mvPolynomialTranslate B a (MvPolynomial.X i)) at h
  rw [mvPolynomialTranslate_X] at h
  exact h

theorem polynomialAlternant_translate {m : ℕ} (p : Fin m → Polynomial ℂ) (a : ℂ) :
    mvPolynomialTranslate (Fin m) a (polynomialAlternant p) =
      polynomialAlternant (fun j => (p j).taylor a) := by
  unfold polynomialAlternant
  erw [AlgHom.map_det]
  apply congrArg Matrix.det
  funext i j
  exact mvPolynomialTranslate_eval₂ a i (p j)

theorem polynomialAlternant_taylor_coeff {m : ℕ} (p : Fin m → Polynomial ℂ)
    (d : Fin m →₀ ℕ) (a : ℂ) :
    MvPolynomial.coeff d (polynomialAlternant (fun j => (p j).taylor a)) =
      multiDegreeInverseFactorial d * Matrix.det (fun i j : Fin m =>
        (Polynomial.derivative^[d i] (p j)).eval a) := by
  rw [polynomialAlternant_coeff]
  simp only [FewInflection.polynomial_taylor_coeff_eq_jet,
    FewInflection.iteratedDeriv_polynomial_eval, div_eq_mul_inv]
  have h := Matrix.det_mul_column (fun i : Fin m => ((d i).factorial : ℂ)⁻¹)
    (fun i j : Fin m => (Polynomial.derivative^[d i] (p j)).eval a)
  convert h using 1
  · apply congrArg Matrix.det
    funext i j
    exact mul_comm _ _
  · rfl

theorem partitionFits_iff_height_le {n : ℕ} (μ : YoungDiagram) :
    PartitionFits n μ ↔ μ.colLen 0 ≤ n + 1 := by
  constructor
  · intro h
    by_contra hn
    have hc : (n + 1, 0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hh := YoungDiagram.mem_iff_lt_rowLen.mp hc
    change μ.rowLen (n + 1) = 0 at h
    omega
  · intro h
    by_contra hn
    have hh : 0 < μ.rowLen (n + 1) := Nat.pos_of_ne_zero hn
    have hc : (n + 1, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hh
    have := YoungDiagram.mem_iff_lt_colLen.mp hc
    omega

theorem partitionAlternantExponent_rev {n : ℕ} (μ : YoungDiagram) (i : Fin (n + 1)) :
    partitionAlternantExponent (n + 1) μ i.rev = partitionMinorOrders n μ i := by
  simp only [partitionAlternantExponent, Fin.rev_rev, Fin.val_rev, partitionMinorOrders]
  rw [show n + 1 - (i.val + 1) = n - i.val by omega, add_comm]

/-- The ordered coefficient of a translated divided alternant is the exact
    tableau coefficient times the inverse factorial of its exponent.
    Auxiliary to KP (4.8), manuscript `lem:KP-correspondence`. -/
theorem dividedAlternant_translate_partition_coeff {n : ℕ} (μ ν : YoungDiagram)
    (hμ : PartitionFits n μ) (hν : PartitionFits n ν) (a : ℂ) :
    MvPolynomial.coeff (finiteExponent (partitionAlternantExponent (n + 1) μ))
      (mvPolynomialTranslate (Fin (n + 1)) a
        (finiteDividedAlternant (partitionAlternantExponent (n + 1) ν))) =
      multiDegreeInverseFactorial (finiteExponent (partitionAlternantExponent (n + 1) μ)) *
        ((standardSkewTableauCount ν μ : ℂ) /
          ((partitionSize ν - partitionSize μ).factorial : ℂ) *
            a ^ (partitionSize ν - partitionSize μ)) := by
  rw [finiteDividedAlternant_eq_det]
  change MvPolynomial.coeff _ (mvPolynomialTranslate _ a
    (polynomialAlternant (fun j => complexDividedPowerPolynomial
      (partitionAlternantExponent (n + 1) ν j)))) = _
  rw [polynomialAlternant_translate, polynomialAlternant_taylor_coeff]
  congr 1
  have h := dividedPowerPartitionMinor_eval μ ν hν a
  rw [partitionPolynomialMinor_of_fits hμ, polynomialDerivativeMinor_eval] at h
  rw [← h]
  have hd := Matrix.det_submatrix_equiv_self (Fin.revPerm : Equiv.Perm (Fin (n + 1)))
    (fun i j : Fin (n + 1) => (Polynomial.derivative^[partitionAlternantExponent (n + 1) μ i]
      (complexDividedPowerPolynomial (partitionAlternantExponent (n + 1) ν j))).eval a)
  change (Matrix.det (fun i j : Fin (n + 1) =>
    (Polynomial.derivative^[partitionAlternantExponent (n + 1) μ i.rev]
      (complexDividedPowerPolynomial (partitionAlternantExponent (n + 1) ν j.rev))).eval a)) = _ at hd
  simp only [partitionAlternantExponent_rev] at hd
  convert hd.symm using 1 <;> rfl

end
end ModifiedCartan

#print axioms ModifiedCartan.dividedAlternant_translate_partition_coeff
