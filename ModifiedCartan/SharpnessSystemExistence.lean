import ModifiedCartan.SharpnessBaseSolutions
import ModifiedCartan.EntirePrimitives
import ModifiedCartan.SharpnessWronskian

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- One entire solution with each of the prescribed initial jet vectors. -/
theorem sharpness_solution_with_initial_jet_exists {n k q : ℕ}
    (hq : 2 ≤ q) (hqn : q ≤ n + 1) (j : Index n) :
    ∃ w : ℂ → ℂ, Differentiable ℂ w ∧
      (∀ i : Index n, iteratedDeriv i.val w 0 = if i = j then 1 else 0) ∧
      ∀ z, iteratedDeriv (n + 1) w z = z ^ k * iteratedDeriv (n + 1 - q) w z := by
  let m := n + 1 - q
  have hmq : m + q = n + 1 := Nat.sub_add_cancel hqn
  by_cases hjm : j.val < m
  · refine ⟨fun z => ((j.val.factorial : ℕ) : ℂ)⁻¹ * z ^ j.val, by fun_prop, ?_, ?_⟩
    · intro i
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
      by_cases hij : i = j
      · subst i
        simp [Nat.factorial_ne_zero]
      · have hval : i.val ≠ j.val := fun he => hij (Fin.ext he)
        simp [hval, hij]
    · intro z
      have hjN : j.val < n + 1 := j.isLt
      have hjm' : j.val < n + 1 - q := hjm
      simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow,
        Nat.descFactorial_eq_zero_iff_lt.mpr hjN, Nat.descFactorial_eq_zero_iff_lt.mpr hjm',
        Nat.cast_zero, zero_mul, mul_zero]
  · have hmj : m ≤ j.val := by omega
    have hjbase : j.val - m < q := by have := j.isLt; omega
    obtain ⟨F, hF, hFm, hF0⟩ := entire_iteratedPrimitive_exists
      (sharpnessBaseSolution_differentiable (by omega : 1 ≤ q) k (j.val - m)) m
    refine ⟨F, hF, ?_, ?_⟩
    · intro i
      by_cases him : i.val < m
      · rw [hF0 i.val him]
        have hij : i ≠ j := by intro he; subst i; omega
        simp [hij]
      · have hmi : m ≤ i.val := by omega
        have hibase : i.val - m < q := by have := i.isLt; omega
        have hiorder : i.val = (i.val - m) + m := (Nat.sub_add_cancel hmi).symm
        rw [hiorder, iteratedDeriv_add_orders, hFm,
          sharpnessBaseSolution_initial (by omega : 1 ≤ q) k hjbase hibase]
        have he : i.val - m = j.val - m ↔ i = j := by
          constructor
          · intro hij
            apply Fin.ext
            omega
          · intro hij
            rw [hij]
        simp only [he]
    · intro z
      change iteratedDeriv (n + 1) F z = z ^ k * iteratedDeriv m F z
      have hN : n + 1 = q + m := by omega
      rw [hN, iteratedDeriv_add_orders, hFm]
      exact sharpnessBaseSolution_equation (by omega : 1 ≤ q) k hjbase z

/-- LaTeX `eq:sharpness-equation`: actual entire existence of the normalized
solution system used by `prop:sharpness-orders`, constructed by convergent
series and repeated entire primitives. -/
theorem sharpnessSystem_exists (n k q : ℕ) : SharpnessSystemExistenceTarget n k q := by
  intro _hn hq hqn
  choose g hhol hinit heq using (sharpness_solution_with_initial_jet_exists (k := k) hq hqn)
  exact ⟨g, hhol, (fun i j => hinit j i), heq⟩

end ModifiedCartan
#print axioms ModifiedCartan.sharpness_solution_with_initial_jet_exists
#print axioms ModifiedCartan.sharpnessSystem_exists
