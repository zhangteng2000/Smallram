import ModifiedCartan.PolynomialSequence
import ModifiedCartan.NormComparison

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The identity initial jets determine the polynomial system uniquely,
as in the final Cauchy step of LaTeX `prop:small-order`. -/
theorem normalized_system_eq_monomials {n : ℕ} {y : Index n → ℂ → ℂ}
    (hy : ∀ j, Differentiable ℂ (y j))
    (hjets : ∀ i j : Index n, iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0)
    (hvanish : ∀ j, ∀ k : ℕ, n < k → iteratedDeriv k (y j) 0 = 0)
    (j : Index n) (z : ℂ) : y j z = z ^ j.val / (j.val.factorial : ℂ) := by
  classical
  rw [entire_eq_taylorPolynomial_of_deriv_vanishing (hy j)
    (N := n + 1) (fun k hk => hvanish j k (by omega)) z,
    FewInflection.taylorPolynomial_eval_eq_sum]
  simp only [sub_zero]
  rw [Finset.sum_eq_single j.val]
  · have hj : iteratedDeriv j.val (y j) 0 = 1 := by simpa using hjets j j
    rw [hj]
    ring
  · intro k hk hkj
    have hkn : k < n + 1 := Finset.mem_range.mp hk
    have he : (⟨k, hkn⟩ : Index n) ≠ j := by
      intro hh
      exact hkj (congrArg Fin.val hh)
    have hh := hjets ⟨k, hkn⟩ j
    rw [if_neg he] at hh
    simp only [hh, mul_zero, zero_mul]
  · intro hj
    exact (hj (Finset.mem_range.mpr j.isLt)).elim

theorem normalized_system_eq_monomials_of_power_sequence {n : ℕ}
    {y : Index n → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    (hjets : ∀ i j : Index n, iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0)
    {r : ℕ → ℝ} (hr : ∀ ν, 0 < r ν) (ht : Tendsto r atTop atTop) {C γ : ℝ}
    (hb : ∀ᶠ ν in atTop, ∀ j : Index n, maximumModulus (y j) (r ν) ≤ C * (r ν) ^ γ)
    (hγ : γ < (n + 1 : ℕ)) :
    ∀ j z, y j z = z ^ j.val / (j.val.factorial : ℂ) := by
  apply normalized_system_eq_monomials hy hjets
  intro j k hk
  have hcoeff : ∀ᶠ ν in atTop, maximumModulus (y j) (r ν) ≤ C * (r ν) ^ γ :=
    hb.mono (fun ν hν => hν j)
  exact iteratedDeriv_zero_of_power_sequence (hy j) hr ht hcoeff
    (hγ.trans_le (by exact_mod_cast (show n + 1 ≤ k by omega)))

end ModifiedCartan
#print axioms ModifiedCartan.normalized_system_eq_monomials_of_power_sequence
