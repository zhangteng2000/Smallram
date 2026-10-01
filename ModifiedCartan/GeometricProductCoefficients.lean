import ModifiedCartan.FiniteGeometricSeries
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem multiset_map_prod_counts {A R : Type*} [Fintype A] [CommMonoid R]
    (s : Multiset A) (a : A → R) : (s.map a).prod = ∏ i : A, a i ^ s.count i := by
  conv_lhs => rw [← Multiset.toFinsupp_toMultiset s]
  rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (fun b => pow_zero b) (fun b k l => pow_add b k l),
    Finsupp.prod_fintype _ _ (fun i => pow_zero (a i))]
  rfl

def degreeMultisetEquiv (A : Type*) [Fintype A] (n : ℕ) :
    {d : A →₀ ℕ // d ∈ Finset.finsuppAntidiag Finset.univ n} ≃ Sym A n where
  toFun d := ⟨d.val.toMultiset, (Finsupp.card_toMultiset d.val).trans
    ((Finsupp.sum_fintype _ _ (fun _ => rfl)).trans (Finset.mem_finsuppAntidiag.mp d.property).1)⟩
  invFun s := ⟨s.val.toFinsupp, Finset.mem_finsuppAntidiag.mpr ⟨by
    exact (Finsupp.sum_fintype s.val.toFinsupp (fun _ k => k) (fun _ => rfl)).symm.trans
      ((Multiset.toFinsupp_sum_eq s.val).trans s.property), Finset.subset_univ _⟩⟩
  left_inv d := Subtype.ext (Finsupp.toMultiset_toFinsupp d.val)
  right_inv s := Subtype.ext (Multiset.toFinsupp_toMultiset s.val)

/-- Geometric product coefficients are actual finite multiset sums.
    Auxiliary to the Cauchy kernel for paper `lem:KP-correspondence`. -/
theorem geometricPowerSeries_prod_coeff {A R : Type*} [Fintype A] [CommSemiring R]
    (a : A → R) (n : ℕ) :
    PowerSeries.coeff n (∏ i : A, geometricPowerSeries (a i)) =
      ∑ s : Sym A n, (s.val.map a).prod := by
  rw [PowerSeries.coeff_prod]
  simp only [geometricPowerSeries_coeff]
  rw [← Finset.sum_attach]
  apply Fintype.sum_equiv (degreeMultisetEquiv A n)
  intro d
  rw [multiset_map_prod_counts]
  change (∏ i : A, a i ^ d.val i) = ∏ i : A, a i ^ d.val.toMultiset.count i
  simp only [Finsupp.count_toMultiset]

theorem geometricPowerSeries_X_prod_coeff {A R : Type*} [Fintype A] [CommSemiring R]
    (n : ℕ) :
    PowerSeries.coeff n (∏ i : A, geometricPowerSeries (MvPolynomial.X i : MvPolynomial A R)) =
      MvPolynomial.hsymm A R n := geometricPowerSeries_prod_coeff _ n

end
end ModifiedCartan

#print axioms ModifiedCartan.geometricPowerSeries_prod_coeff
