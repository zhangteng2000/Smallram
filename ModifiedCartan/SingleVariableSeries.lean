import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def unitVariableEmbedding {B : Type*} (j : B) : Unit ↪ B where
  toFun _ := j
  inj' _ _ _ := Subsingleton.elim _ _

@[simp] theorem unitVariableEmbedding_apply {B : Type*} (j : B) (u : Unit) :
    unitVariableEmbedding j u = j := rfl

/-- Embed a univariate formal series into one specified variable. This is an
    auxiliary construction for paper `lem:KP-correspondence`. -/
def singleVariableSeries {B R : Type*} [CommSemiring R] (j : B)
    (F : PowerSeries R) : MvPowerSeries B R :=
  MvPowerSeries.rename (unitVariableEmbedding j) F

theorem singleVariableSeries_coeff_single {B R : Type*} [CommSemiring R]
    (j : B) (F : PowerSeries R) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single j k) (singleVariableSeries j F) =
      PowerSeries.coeff k F := by
  simpa only [Finsupp.embDomain_single, unitVariableEmbedding_apply, singleVariableSeries,
    PowerSeries.coeff] using
    MvPowerSeries.coeff_embDomain_rename (unitVariableEmbedding j) F (Finsupp.single () k)

theorem singleVariableSeries_coeff {B R : Type*} [CommSemiring R]
    (j : B) (F : PowerSeries R) (d : B →₀ ℕ) :
    MvPowerSeries.coeff d (singleVariableSeries j F) =
      if d = Finsupp.single j (d j) then PowerSeries.coeff (d j) F else 0 := by
  by_cases hd : d = Finsupp.single j (d j)
  · rw [ite_eq_left hd, hd, singleVariableSeries_coeff_single]
    simp
  · rw [ite_eq_right hd]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨q, hq⟩
    have hsingle : q = Finsupp.single () (q ()) := Finsupp.unique_single q
    rw [hsingle, Finsupp.mapDomain_single] at hq
    change Finsupp.single j (q ()) = d at hq
    apply hd
    rw [← hq]
    simp

theorem singleVariableSeries_mul {B R : Type*} [CommSemiring R]
    (j : B) (F G : PowerSeries R) :
    singleVariableSeries j (F * G) = singleVariableSeries j F * singleVariableSeries j G :=
  map_mul _ _ _

theorem singleVariableSeries_one {B R : Type*} [CommSemiring R] (j : B) :
    singleVariableSeries j (1 : PowerSeries R) = 1 := map_one _

theorem singleVariableSeries_C {B R : Type*} [CommSemiring R] (j : B) (a : R) :
    singleVariableSeries j (PowerSeries.C a) = MvPowerSeries.C a := by
  exact MvPowerSeries.rename_C _ a

theorem singleVariableSeries_X {B R : Type*} [CommSemiring R] (j : B) :
    singleVariableSeries j (PowerSeries.X : PowerSeries R) = MvPowerSeries.X j := by
  exact MvPowerSeries.rename_X (unitVariableEmbedding j) ()

end
end ModifiedCartan

#print axioms ModifiedCartan.singleVariableSeries_coeff
