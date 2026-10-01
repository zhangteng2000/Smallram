import ModifiedCartan.SingleVariableSeries

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def singleVariableDegreeSplit {B : Type*} [Fintype B] (d : B →₀ ℕ) : B →₀ (B →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm (fun j => Finsupp.single j (d j))

theorem singleVariableDegreeSplit_sum {B : Type*} [Fintype B] (d : B →₀ ℕ) :
    ∑ j : B, singleVariableDegreeSplit d j = d := by
  ext i
  simp [singleVariableDegreeSplit, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]

theorem singleVariableDegreeSplit_mem {B : Type*} [Fintype B] (d : B →₀ ℕ) :
    singleVariableDegreeSplit d ∈ Finset.finsuppAntidiag Finset.univ d := by
  simp [Finset.mem_finsuppAntidiag, singleVariableDegreeSplit_sum]

theorem eq_singleVariableDegreeSplit {B : Type*} [Fintype B]
    (d : B →₀ ℕ) (l : B →₀ (B →₀ ℕ)) (hl : ∑ j : B, l j = d)
    (hs : ∀ j, l j = Finsupp.single j (l j j)) : l = singleVariableDegreeSplit d := by
  have hv : ∀ j, l j j = d j := by
    intro j
    have hsum : (∑ i : B, l i) j = l j j := by
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_single j
      · intro i _ hij
        rw [hs i, Finsupp.single_eq_of_ne hij.symm]
      · simp
    rw [hl] at hsum
    exact hsum.symm
  ext j k
  rw [hs j, hv j]
  rfl

/-- The coefficient of a product in independent variables is the product of
    its univariate coefficients. Auxiliary to paper `lem:KP-correspondence`. -/
theorem singleVariableSeries_coeff_prod {B R : Type*} [Fintype B] [CommSemiring R]
    (F : B → PowerSeries R) (d : B →₀ ℕ) :
    MvPowerSeries.coeff d (∏ j : B, singleVariableSeries j (F j)) =
      ∏ j : B, PowerSeries.coeff (d j) (F j) := by
  rw [MvPowerSeries.coeff_prod, Finset.sum_eq_single (singleVariableDegreeSplit d)]
  · apply Finset.prod_congr rfl
    intro j _
    exact singleVariableSeries_coeff_single j (F j) (d j)
  · intro l hl hne
    by_contra hp
    apply hne
    apply eq_singleVariableDegreeSplit d l (Finset.mem_finsuppAntidiag.mp hl).1
    intro j
    by_contra hj
    have hz : MvPowerSeries.coeff (l j) (singleVariableSeries j (F j)) = 0 := by
      rw [singleVariableSeries_coeff, ite_eq_right hj]
    exact hp (Finset.prod_eq_zero (Finset.mem_univ j) hz)
  · intro hnot
    exact False.elim (hnot (singleVariableDegreeSplit_mem d))

end
end ModifiedCartan

#print axioms ModifiedCartan.singleVariableSeries_coeff_prod
