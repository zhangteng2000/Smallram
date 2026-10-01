import FewInflection.EntireTaylor

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_polynomial_of_iteratedDeriv_eq_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (m : ℕ) (hm : iteratedDeriv m f = 0) :
    ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  have htail (j : ℕ) : iteratedDeriv (m + j) f = 0 := by
    induction j with
    | zero => simpa using hm
    | succ j ih =>
      rw [Nat.add_succ, iteratedDeriv_succ, ih]
      ext z
      simp
  refine ⟨FewInflection.taylorPolynomial f 0 m, fun z => ?_⟩
  have hs := Complex.hasSum_taylorSeries_of_entire hf 0 z
  have ht : HasSum
      (fun j : ℕ => (j.factorial : ℂ)⁻¹ • (z - 0) ^ j • iteratedDeriv j f 0)
      (∑ j ∈ Finset.range m,
        (j.factorial : ℂ)⁻¹ • (z - 0) ^ j • iteratedDeriv j f 0) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hmj : m ≤ j := by simpa using hj
    have hz : iteratedDeriv j f = 0 := by
      simpa only [Nat.add_sub_of_le hmj] using htail (j - m)
    simp [hz]
  rw [FewInflection.taylorPolynomial_eval_eq_sum]
  simpa only [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hs.unique ht

theorem entire_iteratedDeriv_not_identically_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hpoly : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) (m : ℕ) :
    ∃ z, iteratedDeriv m f z ≠ 0 := by
  by_contra hn
  push_neg at hn
  exact hpoly (entire_polynomial_of_iteratedDeriv_eq_zero hf m (funext hn))

end ModifiedCartan
#print axioms ModifiedCartan.entire_polynomial_of_iteratedDeriv_eq_zero
