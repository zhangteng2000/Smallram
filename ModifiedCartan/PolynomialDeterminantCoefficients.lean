import ModifiedCartan.SeparateVariableProducts
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem singleVariableSeries_polynomial {B R : Type*} [CommSemiring R]
    (j : B) (p : Polynomial R) :
    singleVariableSeries j (p : PowerSeries R) =
      ((p.eval₂ MvPolynomial.C (MvPolynomial.X j) : MvPolynomial B R) : MvPowerSeries B R) := by
  have h : (MvPowerSeries.rename (R := R) (unitVariableEmbedding j)).toRingHom.comp
      Polynomial.coeToPowerSeries.ringHom =
      MvPolynomial.coeToMvPowerSeries.ringHom.comp
        (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X j)) := by
    apply Polynomial.ringHom_ext
    · intro a
      change singleVariableSeries j ((Polynomial.C a : Polynomial R) : PowerSeries R) =
        ((Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X j) (Polynomial.C a) :
          MvPolynomial B R) : MvPowerSeries B R)
      rw [Polynomial.coe_C, Polynomial.eval₂_C, MvPolynomial.coe_C, singleVariableSeries_C]
    · change singleVariableSeries j ((Polynomial.X : Polynomial R) : PowerSeries R) =
        ((Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X j) Polynomial.X :
          MvPolynomial B R) : MvPowerSeries B R)
      rw [Polynomial.coe_X, Polynomial.eval₂_X, MvPolynomial.coe_X, singleVariableSeries_X]
  exact RingHom.congr_fun h p

theorem mvPolynomial_coeff_separate_product {B R : Type*} [Fintype B] [CommSemiring R]
    (p : B → Polynomial R) (d : B →₀ ℕ) :
    MvPolynomial.coeff d (∏ j : B, (p j).eval₂ MvPolynomial.C (MvPolynomial.X j)) =
      ∏ j : B, (p j).coeff (d j) := by
  have h := singleVariableSeries_coeff_prod (fun j => (p j : PowerSeries R)) d
  simp only [singleVariableSeries_polynomial, Polynomial.coeff_coe] at h
  have hp := map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := B) (R := R))
    (fun j => (p j).eval₂ MvPolynomial.C (MvPolynomial.X j)) Finset.univ
  change ((∏ j : B, (p j).eval₂ MvPolynomial.C (MvPolynomial.X j) :
    MvPolynomial B R) : MvPowerSeries B R) = ∏ j : B,
      (((p j).eval₂ MvPolynomial.C (MvPolynomial.X j) : MvPolynomial B R) : MvPowerSeries B R) at hp
  rw [← hp, MvPolynomial.coeff_coe] at h
  exact h

/-- The alternating polynomial associated to a tuple of univariate polynomials.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
def polynomialAlternant {R : Type*} [CommRing R] {m : ℕ}
    (p : Fin m → Polynomial R) : MvPolynomial (Fin m) R :=
  Matrix.det (fun i j : Fin m => (p j).eval₂ MvPolynomial.C (MvPolynomial.X i))

theorem polynomialAlternant_coeff {R : Type*} [CommRing R] {m : ℕ}
    (p : Fin m → Polynomial R) (d : Fin m →₀ ℕ) :
    MvPolynomial.coeff d (polynomialAlternant p) =
      Matrix.det (fun i j : Fin m => (p j).coeff (d i)) := by
  unfold polynomialAlternant
  erw [Matrix.det_apply, Matrix.det_apply]
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hc : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin m) R) =
      MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : R)) := (map_intCast _ _).symm
  simp only [Units.smul_def, zsmul_eq_mul, hc, MvPolynomial.coeff_C_mul]
  congr 1
  calc
    _ = MvPolynomial.coeff d (∏ j : Fin m,
        (p (σ.symm j)).eval₂ MvPolynomial.C (MvPolynomial.X j)) := by
      apply congrArg (MvPolynomial.coeff d)
      simpa only [Equiv.symm_apply_apply] using Equiv.prod_comp σ
        (fun j => (p (σ.symm j)).eval₂ MvPolynomial.C (MvPolynomial.X j))
    _ = ∏ j : Fin m, (p (σ.symm j)).coeff (d j) :=
      mvPolynomial_coeff_separate_product (fun j => p (σ.symm j)) d
    _ = _ := by
      simpa only [Equiv.symm_apply_apply] using (Equiv.prod_comp σ
        (fun j => (p (σ.symm j)).coeff (d j))).symm

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialAlternant_coeff
