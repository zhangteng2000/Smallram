import ModifiedCartan.NormComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem common_growth_power_constant (T : ℝ → ℝ) {p q a D r0 : ℝ}
    (ha : 0 < a) (hD : 1 ≤ D)
    (hlower : ∀ x r, 1 ≤ x → r0 ≤ r → a * x ^ p ≤ T (x * r) / T r)
    (hupper : ∀ x r, 1 ≤ x → r0 ≤ r → T (x * r) / T r ≤ D * x ^ q) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x r, 1 ≤ x → r0 ≤ r →
      C⁻¹ * x ^ p ≤ T (x * r) / T r ∧ T (x * r) / T r ≤ C * x ^ q := by
  let C := max D a⁻¹
  have hC : 1 ≤ C := hD.trans (le_max_left _ _)
  have hCa : C⁻¹ ≤ a := by
    have h := one_div_le_one_div_of_le (inv_pos.mpr ha) (le_max_right D a⁻¹)
    simpa only [one_div, inv_inv] using h
  refine ⟨C, hC, ?_⟩
  intro x r hx hr
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  exact ⟨(mul_le_mul_of_nonneg_right hCa (Real.rpow_nonneg hx0 p)).trans (hlower x r hx hr),
    (hupper x r hx hr).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0 q))⟩

/-- Reversing the multiplier proves the symmetric min/max bound without
any continuity requirement on the positive growth function. -/
theorem symmetric_growth_power_bounds_of_ge_one (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {p q C r0 : ℝ} (hC : 1 ≤ C) (hr0 : 0 < r0)
    (hb : ∀ x r, 1 ≤ x → r0 ≤ r →
      C⁻¹ * x ^ p ≤ T (x * r) / T r ∧ T (x * r) / T r ≤ C * x ^ q) :
    ∀ t r, 0 < t → r0 ≤ r → r0 ≤ t * r →
      C⁻¹ * min (t ^ p) (t ^ q) ≤ T (t * r) / T r ∧
        T (t * r) / T r ≤ C * max (t ^ p) (t ^ q) := by
  intro t r ht hr htr
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  by_cases ht1 : 1 ≤ t
  · have hb' := hb t r ht1 hr
    exact ⟨(mul_le_mul_of_nonneg_left (min_le_left _ _) (inv_nonneg.mpr hC0.le)).trans hb'.1,
      hb'.2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hC0.le)⟩
  · have htinv : 1 ≤ t⁻¹ := by
      have h : (1 : ℝ) ≤ 1 / t := (le_div_iff₀ ht).mpr (by linarith)
      simpa only [one_div] using h
    have hrpos := hr0.trans_le hr
    have htrpos := hr0.trans_le htr
    have hTr := hT r hrpos
    have hTtr := hT (t * r) htrpos
    have hinv := hb t⁻¹ (t * r) htinv htr
    have he : t⁻¹ * (t * r) = r := by rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
    rw [he] at hinv
    have hl : C⁻¹ * t ^ q ≤ T (t * r) / T r := by
      have h := one_div_le_one_div_of_le (div_pos hTr hTtr) hinv.2
      simpa only [one_div, mul_inv_rev, Real.inv_rpow ht.le, inv_inv, inv_div, mul_comm] using h
    have hu : T (t * r) / T r ≤ C * t ^ p := by
      have h := one_div_le_one_div_of_le
        (mul_pos (inv_pos.mpr hC0) (Real.rpow_pos_of_pos (inv_pos.mpr ht) p)) hinv.1
      simpa only [one_div, mul_inv_rev, Real.inv_rpow ht.le, inv_inv, inv_div, mul_comm] using h
    exact ⟨(mul_le_mul_of_nonneg_left (min_le_right _ _) (inv_nonneg.mpr hC0.le)).trans hl,
      hu.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hC0.le)⟩

end
end ModifiedCartan
#print axioms ModifiedCartan.symmetric_growth_power_bounds_of_ge_one
