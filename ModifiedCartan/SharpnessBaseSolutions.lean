import ModifiedCartan.SharpnessCoefficients
import ModifiedCartan.EntireSeries

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def sharpnessBaseTerm (q k j l : ℕ) (z : ℂ) : ℂ :=
  (sharpnessBaseCoeff q k j l : ℂ) * z ^ (j + (q + k) * l)

noncomputable def sharpnessBaseSolution (q k j : ℕ) (z : ℂ) : ℂ :=
  ∑' l : ℕ, sharpnessBaseTerm q k j l z

theorem sharpnessBaseTerm_differentiable (q k j l : ℕ) :
    Differentiable ℂ (sharpnessBaseTerm q k j l) := by
  unfold sharpnessBaseTerm
  fun_prop

theorem sharpnessBaseTerm_disk_bound {q : ℕ} (hq : 1 ≤ q) (k j : ℕ)
    (R : ℝ) (hR : 0 < R) : ∃ u : ℕ → ℝ, Summable u ∧
      ∀ l z, ‖z‖ ≤ R → ‖sharpnessBaseTerm q k j l z‖ ≤ u l := by
  refine ⟨fun l => sharpnessBaseCoeff q k j l * R ^ (j + (q + k) * l),
    sharpnessBaseCoeff_weighted_summable hq k j hR, ?_⟩
  intro l z hz
  rw [sharpnessBaseTerm, norm_mul, norm_pow,
    Complex.norm_of_nonneg (sharpnessBaseCoeff_pos hq k j l).le]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz _)
    (sharpnessBaseCoeff_pos hq k j l).le

theorem sharpnessBaseSolution_differentiable {q : ℕ} (hq : 1 ≤ q) (k j : ℕ) :
    Differentiable ℂ (sharpnessBaseSolution q k j) :=
  entireSeries_differentiable (sharpnessBaseTerm_differentiable q k j)
    (sharpnessBaseTerm_disk_bound hq k j)

theorem sharpnessBaseSolution_hasSum_iteratedDeriv {q : ℕ} (hq : 1 ≤ q)
    (k j m : ℕ) (z : ℂ) :
    HasSum (fun l => iteratedDeriv m (sharpnessBaseTerm q k j l) z)
      (iteratedDeriv m (sharpnessBaseSolution q k j) z) :=
  entireSeries_hasSum_iteratedDeriv (sharpnessBaseTerm_differentiable q k j)
    (sharpnessBaseTerm_disk_bound hq k j) m z

/-- The literal Kronecker initial jets of the explicitly constructed base solution. -/
theorem sharpnessBaseSolution_initial {q : ℕ} (hq : 1 ≤ q) (k : ℕ)
    {j i : ℕ} (hj : j < q) (hi : i < q) :
    iteratedDeriv i (sharpnessBaseSolution q k j) 0 = if i = j then 1 else 0 := by
  rw [← (sharpnessBaseSolution_hasSum_iteratedDeriv hq k j i 0).tsum_eq]
  rw [tsum_eq_single 0]
  · unfold sharpnessBaseTerm
    rw [iteratedDeriv_const_mul_field]
    simp only [Nat.mul_zero, Nat.add_zero,
      iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, sharpnessBaseCoeff]
    by_cases hij : i = j
    · simp [hij, Nat.factorial_ne_zero]
    · simp [hij]
  · intro l hl
    have he : i ≠ j + (q + k) * l := by
      have hll : 1 ≤ l := by omega
      have hm := Nat.mul_le_mul_left (q + k) hll
      omega
    unfold sharpnessBaseTerm
    rw [iteratedDeriv_const_mul_field]
    simp only [
      iteratedDeriv_fun_pow_zero, ite_eq_right he, Nat.cast_zero, mul_zero]

theorem sharpnessBaseTerm_deriv_shift {q : ℕ} (hq : 1 ≤ q)
    (k j l : ℕ) (z : ℂ) :
    iteratedDeriv q (sharpnessBaseTerm q k j (l + 1)) z = z ^ k * sharpnessBaseTerm q k j l z := by
  have hc : (sharpnessBaseCoeff q k j (l + 1) : ℂ) *
      ((j + (q + k) * (l + 1)).descFactorial q : ℂ) = (sharpnessBaseCoeff q k j l : ℂ) := by
    exact_mod_cast sharpnessBaseCoeff_recurrence hq k j l
  have he : j + (q + k) * (l + 1) - q = k + (j + (q + k) * l) := by
    have hh : j + (q + k) * (l + 1) = (k + (j + (q + k) * l)) + q := by ring
    omega
  unfold sharpnessBaseTerm
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow, ← mul_assoc, hc, he, pow_add]
  ring

/-- Constructive entire solutions of y^(q)=z^k*y with no ODE existence assumption. -/
theorem sharpnessBaseSolution_equation {q : ℕ} (hq : 1 ≤ q) (k : ℕ)
    {j : ℕ} (hj : j < q) (z : ℂ) :
    iteratedDeriv q (sharpnessBaseSolution q k j) z = z ^ k * sharpnessBaseSolution q k j z := by
  have hs := sharpnessBaseSolution_hasSum_iteratedDeriv hq k j q z
  rw [← hs.tsum_eq, hs.summable.tsum_eq_zero_add]
  have hz : iteratedDeriv q (sharpnessBaseTerm q k j 0) z = 0 := by
    unfold sharpnessBaseTerm
    rw [iteratedDeriv_const_mul_field]
    simp only [Nat.mul_zero, Nat.add_zero,
      iteratedDeriv_const_mul_field, iteratedDeriv_pow,
      Nat.descFactorial_eq_zero_iff_lt.mpr hj, Nat.cast_zero, zero_mul, mul_zero]
  rw [hz, zero_add]
  simp_rw [sharpnessBaseTerm_deriv_shift hq]
  rw [tsum_mul_left]
  rfl

end ModifiedCartan
#print axioms ModifiedCartan.sharpnessBaseSolution_initial
#print axioms ModifiedCartan.sharpnessBaseSolution_equation


