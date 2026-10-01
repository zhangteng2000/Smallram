import ModifiedCartan.PowerChartGeometry
import ModifiedCartan.ArbitraryPolynomialCoefficients
import ModifiedCartan.MonicPolynomialParameters

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem IsWeightedMonomial.powerChart_weighted {q : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    {b : ℂ → ℂ} (hb : IsWeightedMonomial ((q : ℝ) * (ρ - 1)) b)
    (a : ℂ) {w : ℂ} (hw : w ≠ 0) :
    b (powerChart a ρ w) * (a * ((ρ⁻¹ : ℝ) : ℂ) * w ^ (((ρ⁻¹ : ℝ) : ℂ) - 1)) ^ q =
      b a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ q := by
  rcases hb with ⟨m, hm, c, rfl⟩ | ⟨_, rfl⟩
  · have he : ρ⁻¹ * (m : ℝ) + (ρ⁻¹ - 1) * (q : ℝ) = 0 := by
      field_simp
      nlinarith [hm]
    have hec : ((ρ⁻¹ : ℝ) : ℂ) * (m : ℂ) + (((ρ⁻¹ : ℝ) : ℂ) - 1) * (q : ℂ) = 0 := by
      exact_mod_cast he
    have hp : (w ^ ((ρ⁻¹ : ℝ) : ℂ)) ^ m * (w ^ (((ρ⁻¹ : ℝ) : ℂ) - 1)) ^ q = 1 := by
      rw [← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat, ← Complex.cpow_add _ _ hw,
        hec, Complex.cpow_zero]
    simp only [powerChart, mul_pow]
    calc
      c * (a ^ m * (w ^ ((ρ⁻¹ : ℝ) : ℂ)) ^ m) *
          (a ^ q * (((ρ⁻¹ : ℝ) : ℂ) ^ q) * (w ^ (((ρ⁻¹ : ℝ) : ℂ) - 1)) ^ q) =
          (c * a ^ m) * (a ^ q * (((ρ⁻¹ : ℝ) : ℂ) ^ q)) *
            ((w ^ ((ρ⁻¹ : ℝ) : ℂ)) ^ m * (w ^ (((ρ⁻¹ : ℝ) : ℂ) - 1)) ^ q) := by ring
      _ = _ := by rw [hp, mul_one]
  · simp only [Pi.zero_apply, zero_mul]

theorem ArbitraryRadiusLimitData.fullCoefficient_powerChart
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : ρ ≠ 0) (a : ℂ) {w : ℂ} (hw : w ∈ powerChartDomain a ρ) (i : Index n) :
    d.fullCoefficient i (powerChart a ρ w) * (deriv (powerChart a ρ) w) ^ (n + 1 - i.val) =
      d.fullCoefficient i a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ (n + 1 - i.val) := by
  rw [powerChart_deriv hw]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [d.fullCoefficient_last, zero_mul]
  · rw [d.fullCoefficient_castSucc]
    exact (d.coefficient_monomial j).powerChart_weighted hρ a
      (by intro h; subst w; simpa using hw.1)

theorem monic_equation_mul {n : ℕ} (a : Index n → ℂ) {z m : ℂ}
    (he : z ^ (n + 1) + ∑ i, a i * z ^ i.val = 0) :
    (m * z) ^ (n + 1) + ∑ i, (a i * m ^ (n + 1 - i.val)) * (m * z) ^ i.val = 0 := by
  have ht (i : Index n) : (a i * m ^ (n + 1 - i.val)) * (m * z) ^ i.val =
      m ^ (n + 1) * (a i * z ^ i.val) := by
    rw [mul_pow]
    calc
      a i * m ^ (n + 1 - i.val) * (m ^ i.val * z ^ i.val) =
          (m ^ (n + 1 - i.val) * m ^ i.val) * (a i * z ^ i.val) := by ring
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel (by omega : i.val ≤ n + 1)]
  simp_rw [ht]
  rw [mul_pow, ← Finset.mul_sum, ← mul_add, he, mul_zero]

theorem exists_finite_roots_monic_equation {n : ℕ} (a : Index n → ℂ) :
    ∃ A : Finset ℂ, ∀ z : ℂ, z ^ (n + 1) + ∑ i, a i * z ^ i.val = 0 → z ∈ A := by
  classical
  let P := monicPolynomialFromCoefficients a
  refine ⟨P.roots.toFinset, fun z hz => Multiset.mem_toFinset.mpr ?_⟩
  apply (Polynomial.mem_roots (monicPolynomialFromCoefficients_monic a).ne_zero).mpr
  change P.eval z = 0
  simpa [P, monicPolynomialFromCoefficients, Polynomial.eval_finsetSum] using hz

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.fullCoefficient_powerChart
#print axioms ModifiedCartan.exists_finite_roots_monic_equation

