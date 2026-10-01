import ModifiedCartan.ScalarProfileCompactness

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The principal small correction transporting an m-th root from coefficient
C to coefficient D. Only ratios near one will be used for limiting estimates. -/
noncomputable def scalarRootCorrection (m : ℕ) (C D : ℂ) : ℂ :=
  (C / D) ^ ((m : ℂ)⁻¹)

theorem scalarRootCorrection_pow {m : ℕ} (hm : m ≠ 0) (C D : ℂ) :
    (scalarRootCorrection m C D) ^ m = C / D := Complex.cpow_nat_inv_pow _ hm

theorem scalarRootCorrection_norm (m : ℕ) {C D : ℂ} (hD : D ≠ 0) (hCD : ‖C‖ = ‖D‖) :
    ‖scalarRootCorrection m C D‖ = 1 := by
  have he : ((m : ℂ)⁻¹) = (((m : ℝ)⁻¹ : ℝ) : ℂ) := by simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [scalarRootCorrection, he, Complex.norm_cpow_real, norm_div, hCD,
    div_self (norm_ne_zero_iff.mpr hD), Real.one_rpow]

theorem scalarRootCorrection_transports_peak {m : ℕ} (hm : m ≠ 0)
    {C D a B : ℂ} (hD : D ≠ 0) (ha : C * a ^ m = B) :
    D * (a * scalarRootCorrection m C D) ^ m = B := by
  rw [mul_pow, scalarRootCorrection_pow hm]
  calc
    D * (a ^ m * (C / D)) = C * a ^ m := by field_simp
    _ = B := ha

/-- Fixed nonzero denominator modulus converts slow coefficient differences
to a quotient tending to one, even when the coefficients themselves rotate. -/
theorem complex_ratio_tendsto_one_of_difference {R : ℝ} (hR : 0 < R)
    {C D : ℕ → ℂ} (hD : ∀ ν, ‖D ν‖ = R)
    (hlim : Tendsto (fun ν => C ν - D ν) atTop (𝓝 0)) :
    Tendsto (fun ν => C ν / D ν) atTop (𝓝 1) := by
  have hDn (ν : ℕ) : D ν ≠ 0 := norm_ne_zero_iff.mp (by rw [hD ν]; exact hR.ne')
  have he (ν : ℕ) : C ν / D ν - 1 = (C ν - D ν) / D ν := by field_simp [hDn ν]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := hlim.norm.div_const R
  simpa only [he, norm_div, hD, norm_zero, zero_div] using hn

theorem scalarRootCorrection_tendsto_one (m : ℕ) {R : ℝ} (hR : 0 < R)
    {C D : ℕ → ℂ} (hD : ∀ ν, ‖D ν‖ = R)
    (hlim : Tendsto (fun ν => C ν - D ν) atTop (𝓝 0)) :
    Tendsto (fun ν => scalarRootCorrection m (C ν) (D ν)) atTop (𝓝 1) := by
  have hratio := complex_ratio_tendsto_one_of_difference hR hD hlim
  have hh := (continuousAt_cpow_const (b := (m : ℂ)⁻¹) Complex.one_mem_slitPlane).tendsto.comp hratio
  simpa only [Complex.one_cpow, Function.comp_def, scalarRootCorrection] using hh

end ModifiedCartan
#print axioms ModifiedCartan.scalarRootCorrection_transports_peak
#print axioms ModifiedCartan.scalarRootCorrection_tendsto_one

