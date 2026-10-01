import ModifiedCartan.NormComparison
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- A concrete coefficient-sum bound for an arbitrary polynomial. -/
theorem polynomial_eval_power_bound (p : Polynomial ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ ≤ r →
      ‖p.eval z‖ ≤ C * r ^ p.natDegree := by
  let C : ℝ := 1 + ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro r hr z hz
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * r ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      have hir : r ^ i ≤ r ^ p.natDegree := pow_le_pow_right₀ hr (by have := Finset.mem_range.mp hi; omega)
      exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) hz i).trans hir) (norm_nonneg _)
    _ ≤ C * r ^ p.natDegree := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [C]
      linarith

theorem polynomial_family_euclidean_power_bound {n : ℕ} (p : Index n → Polynomial ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ ≤ r →
      euclideanNorm (fun j => (p j).eval z) ≤ C * r ^ D := by
  choose C hC hbound using (fun j : Index n => polynomial_eval_power_bound (p j))
  let D : ℕ := ∑ j, (p j).natDegree
  let K : ℝ := 1 + ∑ j, C j
  have hK : 0 < K := by
    have hs : 0 ≤ ∑ j, C j := Finset.sum_nonneg (fun j _ => (hC j).le)
    dsimp [K]
    linarith
  refine ⟨Real.sqrt (n + 1 : ℝ) * K, by positivity, D, ?_⟩
  intro r hr z hz
  have hnorm : ‖fun j => (p j).eval z‖ ≤ K * r ^ D := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    have hD : (p j).natDegree ≤ D := Finset.single_le_sum (fun i _ => Nat.zero_le ((p i).natDegree)) (Finset.mem_univ j)
    have hCj : C j ≤ K := by
      have hh : C j ≤ ∑ i, C i := Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ j)
      dsimp [K]
      linarith
    exact (hbound j r hr z hz).trans
      (mul_le_mul hCj (pow_le_pow_right₀ hr hD) (by positivity) hK.le)
  calc
    _ ≤ Real.sqrt (n + 1 : ℝ) * ‖fun j => (p j).eval z‖ := euclideanNorm_le _
    _ ≤ Real.sqrt (n + 1 : ℝ) * (K * r ^ D) := mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
    _ = _ := by ring

end ModifiedCartan
#print axioms ModifiedCartan.polynomial_family_euclidean_power_bound

