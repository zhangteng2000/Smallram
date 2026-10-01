import ModifiedCartan.FiniteFrobeniusPolynomials

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finitePowerSumPolynomial_rename_equiv {B C : Type*}
    [Fintype B] [Fintype C] (e : B ≃ C) (j : ℕ) :
    MvPolynomial.rename e (finitePowerSumPolynomial B j) = finitePowerSumPolynomial C j := by
  simp only [finitePowerSumPolynomial, map_sum, map_pow, MvPolynomial.rename_X]
  exact Equiv.sum_comp e (fun c => (MvPolynomial.X c : MvPolynomial C ℂ) ^ j)

theorem finiteCyclePolynomial_rename_equiv {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] (e : B ≃ C) (σ : Equiv.Perm A) :
    MvPolynomial.rename e (finiteCyclePolynomial B σ) = finiteCyclePolynomial C σ := by
  simp only [finiteCyclePolynomial_cycles, map_prod, finitePowerSumPolynomial_rename_equiv]

/-- Relabeling the finite alphabet preserves the actual character transform.
    Auxiliary to paper `lem:KP-correspondence`. -/
theorem finiteFrobeniusPolynomial_rename_equiv {B C : Type*}
    [Fintype B] [Fintype C] (e : B ≃ C) (μ : YoungDiagram) :
    MvPolynomial.rename e (finiteFrobeniusPolynomial B μ) = finiteFrobeniusPolynomial C μ := by
  simp only [finiteFrobeniusPolynomial, finiteFrobeniusPolynomialOn, map_mul, map_sum,
    MvPolynomial.rename_C, finiteCyclePolynomial_rename_equiv]

end
end ModifiedCartan
