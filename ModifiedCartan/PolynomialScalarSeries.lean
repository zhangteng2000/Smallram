import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Extend polynomial scalars and embed into formal series, for the two
    alphabets in paper `lem:KP-correspondence`. -/
def polynomialScalarExtensionSeries (A B R : Type*) [CommSemiring R] :
    MvPolynomial B R →+* MvPowerSeries B (MvPolynomial A R) :=
  MvPolynomial.coeToMvPowerSeries.ringHom.comp (MvPolynomial.map MvPolynomial.C)

theorem polynomialScalarExtensionSeries_apply {A B R : Type*} [CommSemiring R]
    (F : MvPolynomial B R) :
    polynomialScalarExtensionSeries A B R F =
      ((MvPolynomial.map MvPolynomial.C F : MvPolynomial B (MvPolynomial A R)) :
        MvPowerSeries B (MvPolynomial A R)) := rfl

theorem polynomialScalarExtensionSeries_X {A B R : Type*} [CommSemiring R] (j : B) :
    polynomialScalarExtensionSeries A B R (MvPolynomial.X j) = MvPowerSeries.X j := by
  rw [polynomialScalarExtensionSeries_apply, MvPolynomial.map_X, MvPolynomial.coe_X]

theorem polynomialScalarExtensionSeries_C {A B R : Type*} [CommSemiring R] (a : R) :
    polynomialScalarExtensionSeries A B R (MvPolynomial.C a) =
      MvPowerSeries.C (MvPolynomial.C a) := by
  rw [polynomialScalarExtensionSeries_apply, MvPolynomial.map_C, MvPolynomial.coe_C]

theorem polynomialScalarExtensionSeries_coeff {A B R : Type*} [CommSemiring R]
    (F : MvPolynomial B R) (d : B →₀ ℕ) :
    MvPowerSeries.coeff d (polynomialScalarExtensionSeries A B R F) =
      MvPolynomial.C (MvPolynomial.coeff d F) := by
  rw [polynomialScalarExtensionSeries_apply, MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

end
end ModifiedCartan
