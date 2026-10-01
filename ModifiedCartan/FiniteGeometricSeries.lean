import ModifiedCartan.SeparateVariableProducts
import Mathlib.RingTheory.PowerSeries.WellKnown

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def geometricPowerSeries {R : Type*} [CommSemiring R] (a : R) : PowerSeries R :=
  PowerSeries.rescale a (PowerSeries.mk (fun _ => 1))

@[simp] theorem geometricPowerSeries_coeff {R : Type*} [CommSemiring R] (a : R) (k : ℕ) :
    PowerSeries.coeff k (geometricPowerSeries a) = a ^ k := by
  simp [geometricPowerSeries]

theorem geometricPowerSeries_inverse {R : Type*} [CommRing R] (a : R) :
    geometricPowerSeries a * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale a) (PowerSeries.mk_one_mul_one_sub_eq_one R)
  simpa only [geometricPowerSeries, Pi.one_def, map_mul, map_sub, map_one,
    PowerSeries.rescale_X] using h

def geometricMvSeries {B R : Type*} [CommSemiring R] (j : B) (a : R) : MvPowerSeries B R :=
  singleVariableSeries j (geometricPowerSeries a)

theorem geometricMvSeries_inverse {B R : Type*} [CommRing R] (j : B) (a : R) :
    geometricMvSeries j a * (1 - MvPowerSeries.C a * MvPowerSeries.X j) = 1 := by
  have h := congrArg (MvPowerSeries.rename (unitVariableEmbedding j))
    (geometricPowerSeries_inverse a)
  simpa only [geometricMvSeries, singleVariableSeries, map_mul, map_sub, map_one,
    PowerSeries.C, PowerSeries.X, MvPowerSeries.rename_C, MvPowerSeries.rename_X,
    unitVariableEmbedding_apply] using h

theorem geometricMvSeries_coeff_prod {B R : Type*} [Fintype B] [CommSemiring R]
    (a : B → R) (d : B →₀ ℕ) :
    MvPowerSeries.coeff d (∏ j : B, geometricMvSeries j (a j)) = ∏ j : B, a j ^ d j := by
  simpa only [geometricMvSeries, geometricPowerSeries_coeff] using
    singleVariableSeries_coeff_prod (fun j => geometricPowerSeries (a j)) d

end
end ModifiedCartan

#print axioms ModifiedCartan.geometricMvSeries_inverse
#print axioms ModifiedCartan.geometricMvSeries_coeff_prod
