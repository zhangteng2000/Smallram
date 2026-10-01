import ModifiedCartan.FiniteGeometricSeries
import ModifiedCartan.FiniteCauchyRing
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

abbrev finiteCauchySeriesMatrix {R : Type*} [CommSemiring R] {m : ℕ}
    (x : Fin m → R) : Matrix (Fin m) (Fin m) (MvPowerSeries (Fin m) R) :=
  fun i j => geometricMvSeries j (x i)

/-- Formal coefficient extraction from the actual Cauchy determinant.
    Auxiliary to paper `lem:KP-correspondence`. -/
theorem finiteCauchySeriesMatrix_coeff_det {R : Type*} [CommRing R] {m : ℕ}
    (x : Fin m → R) (d : Fin m →₀ ℕ) :
    MvPowerSeries.coeff d (finiteCauchySeriesMatrix x).det =
      Matrix.det (fun i j : Fin m => x i ^ d j) := by
  erw [Matrix.det_apply', Matrix.det_apply']
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hc : (((Equiv.Perm.sign σ : ℤ) : MvPowerSeries (Fin m) R)) =
      MvPowerSeries.C ((Equiv.Perm.sign σ : ℤ) : R) := (map_intCast _ _).symm
  rw [hc, MvPowerSeries.coeff_C_mul]
  congr 1
  exact geometricMvSeries_coeff_prod (fun i => x (σ i)) d

theorem finiteCauchySeriesMatrix_det {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}
    (x : Fin m → R) :
    (finiteCauchySeriesMatrix x).det =
      (finiteVandermondeProduct (fun i => MvPowerSeries.C (x i)) *
        finiteVandermondeProduct (fun j : Fin m => (MvPowerSeries.X j : MvPowerSeries (Fin m) R))) *
          (∏ i : Fin m, ∏ j : Fin m, geometricMvSeries j (x i)) := by
  letI : IsDomain (MvPowerSeries (Fin m) R) := NoZeroDivisors.to_isDomain _
  apply finiteCauchy_inverse_det
  intro i j
  exact geometricMvSeries_inverse j (x i)

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteCauchySeriesMatrix_coeff_det
#print axioms ModifiedCartan.finiteCauchySeriesMatrix_det
