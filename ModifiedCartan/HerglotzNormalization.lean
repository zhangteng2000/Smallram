import ModifiedCartan.PoissonMajorant
import ModifiedCartan.EuclideanJensen
import ModifiedCartan.RescaledGauge

open scoped Topology BigOperators
open Filter Set Metric Complex
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Auxiliary harmonic majorant used in the alternative proof of the upper
bound in `prop:representation`. The actual paper gauge remains H. -/
def curveHerglotz {n : ℕ} (f : Curve n) (R : ℝ) (z : ℂ) : ℂ :=
  Real.circleAverage (fun w => herglotzRieszKernel 0 z w •
    (Real.log (euclideanNorm (f.vector w)) : ℂ)) 0 R

theorem curveHerglotz_analytic {n : ℕ} (f : Curve n) (R : ℝ) :
    AnalyticOnNhd ℂ (curveHerglotz f R) (ball 0 R) := by
  apply analyticOnNhd_circleAverage_herglotzRieszKernel_smul
  exact (Complex.ofRealCLM.continuous.comp (curve_log_euclideanNorm_continuous f)).continuousOn.circleIntegrable'

theorem curveHerglotz_re {n : ℕ} (f : Curve n) {R : ℝ} {z : ℂ}
    (hz : z ∈ ball 0 R) :
    (curveHerglotz f R z).re = Real.circleAverage
      (fun w => poissonKernel 0 z w * Real.log (euclideanNorm (f.vector w))) 0 R := by
  have h := re_circleAverage_herglotzRieszKernel_smul
    (curve_log_euclideanNorm_continuous f).continuousOn.circleIntegrable' hz
  simpa only [curveHerglotz, ← poissonKernel_eq_re_herglotzRieszKernel,
    Pi.smul_apply, smul_eq_mul, Pi.mul_def] using! h

theorem curveHerglotz_re_zero {n : ℕ} (f : Curve n) {R : ℝ} (hR : 0 < R) :
    (curveHerglotz f R 0).re =
      Real.circleAverage (fun w => Real.log (euclideanNorm (f.vector w))) 0 R := by
  rw [curveHerglotz_re f (mem_ball_self hR)]
  apply Real.circleAverage_congr_sphere
  intro w hw
  have hwn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right, abs_of_pos hR] using hw
  simp only [poissonKernel_def, sub_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    hwn, sub_zero, div_self (pow_ne_zero 2 hR.ne'), one_mul]

theorem curve_log_norm_le_herglotz {n : ℕ} (f : Curve n) {R : ℝ} {z : ℂ}
    (hz : z ∈ ball 0 R) :
    Real.log (euclideanNorm (f.vector z)) ≤ (curveHerglotz f R z).re := by
  obtain ⟨h, hdiff, hnonzero, hcenter, hbound⟩ := exists_entire_euclidean_support f z
  have hUc : Continuous (fun w => euclideanNorm (f.vector w)) :=
    euclideanNorm_continuous.comp (continuous_pi (fun j => (f.holomorphic j).continuous))
  rw [curveHerglotz_re f hz, ← hcenter]
  exact log_norm_le_poisson_log_majorant hdiff hnonzero hUc
    (fun w => euclideanNorm_pos (f.vector_ne_zero w)) hbound hz

def rescaledHerglotz {n : ℕ} (f : Curve n) (t : ℝ) : ℂ → ℂ :=
  curveHerglotz (f.dilate (t : ℂ)) 256

theorem rescaledHerglotz_analytic {n : ℕ} (f : Curve n) (t : ℝ) :
    AnalyticOnNhd ℂ (rescaledHerglotz f t) (ball 0 256) :=
  curveHerglotz_analytic _ _

theorem rescaledHerglotz_re_zero {n : ℕ} (f : Curve n) (t : ℝ) :
    (rescaledHerglotz f t 0).re =
      characteristic f (256 * t) + Real.log (euclideanNorm (f.vector 0)) := by
  rw [rescaledHerglotz, curveHerglotz_re_zero _ (by norm_num)]
  change Real.circleAverage (fun w => Real.log (euclideanNorm (f.vector ((t : ℂ) * w)))) 0 256 = _
  rw [circleAverage_real_dilate (fun w => Real.log (euclideanNorm (f.vector w))) t 256]
  rw [show t * 256 = 256 * t by ring, characteristic]
  ring

theorem rescaledHerglotz_normalization_norm_le_one {n : ℕ} (f : Curve n) (t : ℝ)
    {z : ℂ} (hz : z ∈ ball 0 256) :
    euclideanNorm (fun j => rescaledRepresentation f t (rescaledHerglotz f t) j z) ≤ 1 := by
  apply (Real.log_nonpos_iff (euclideanNorm_nonneg _)).mp
  rw [rescaledRepresentation_log_norm]
  exact sub_nonpos.mpr (curve_log_norm_le_herglotz (f.dilate (t : ℂ)) hz)

end
end ModifiedCartan
#print axioms ModifiedCartan.rescaledHerglotz_normalization_norm_le_one
