import ModifiedCartan.ScalarSphericalDecay
import ModifiedCartan.GradientConvergence

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The raw spherical log potential of an actual pair. At isolated Wronskian
zeros the real logarithm convention supplies a finite representative. -/
noncomputable def scalarSphericalLogPotential (g : Index 1 → ℂ → ℂ) (z : ℂ) : ℝ :=
  2 * Real.log (euclideanNorm (fun j => g j z)) - Real.log ‖FewInflection.wronskian 1 g z‖

theorem scalarSphericalLogPotential_eq_neg_log_speed
    {g : Index 1 → ℂ → ℂ} {z : ℂ} (hne : (fun j => g j z) ≠ 0)
    (hW : FewInflection.wronskian 1 g z ≠ 0) :
    scalarSphericalLogPotential g z = -Real.log (scalarSphericalSpeed g z) := by
  have hnorm : euclideanNorm (fun j => g j z) ≠ 0 := (euclideanNorm_pos hne).ne'
  rw [scalarSphericalLogPotential, scalarSphericalSpeed,
    Real.log_div (norm_ne_zero_iff.mpr hW) (pow_ne_zero 2 hnorm), Real.log_pow]
  norm_num

/-- Exact cancellation of the actual gauge. The only remaining change is the
physical derivative factor from the dilation. -/
theorem scalarSphericalLogPotential_rescaled (f : Curve 1) {t : ℝ} (ht : 0 < t)
    {H : ℂ → ℂ} {z : ℂ} (hH : AnalyticAt ℂ H z)
    (hW : FewInflection.wronskian 1 f.coord ((t : ℂ) * z) ≠ 0) :
    scalarSphericalLogPotential (rescaledRepresentation f t H) z =
      scalarSphericalLogPotential f.coord ((t : ℂ) * z) - Real.log t := by
  have hfne : (fun j => f.coord j ((t : ℂ) * z)) ≠ 0 := f.vector_ne_zero _
  have hspeed : 0 < scalarSphericalSpeed f.coord ((t : ℂ) * z) :=
    div_pos (norm_pos_iff.mpr hW) (sq_pos_of_pos (euclideanNorm_pos hfne))
  have hFne : (fun j => rescaledRepresentation f t H j z) ≠ 0 := by
    obtain ⟨j, hj⟩ := rescaledRepresentation_reduced f t H z
    intro he
    exact hj (congrFun he j)
  have hFspeed : 0 < scalarSphericalSpeed (rescaledRepresentation f t H) z := by
    rw [scalarSphericalSpeed_rescaled f t hH, abs_of_pos ht]
    exact mul_pos ht hspeed
  have hFW : FewInflection.wronskian 1 (rescaledRepresentation f t H) z ≠ 0 := by
    intro he
    simp only [scalarSphericalSpeed, he, norm_zero, zero_div, lt_self_iff_false] at hFspeed
  calc
    _ = -Real.log (scalarSphericalSpeed (rescaledRepresentation f t H) z) :=
      scalarSphericalLogPotential_eq_neg_log_speed hFne hFW
    _ = -Real.log (t * scalarSphericalSpeed f.coord ((t : ℂ) * z)) := by
      rw [scalarSphericalSpeed_rescaled f t hH, abs_of_pos ht]
    _ = _ := by
      rw [Real.log_mul ht.ne' hspeed.ne', scalarSphericalLogPotential_eq_neg_log_speed hfne hW]
      ring

theorem scalarSphericalLogPotential_integrableOn_scaled (f : Curve 1) (t : ℝ)
    {K : Set ℂ} (hK : IsCompact K) :
    IntegrableOn (fun z => scalarSphericalLogPotential f.coord ((t : ℂ) * z)) K := by
  have hn : IntegrableOn (fun z => Real.log (euclideanNorm (fun j => f.coord j ((t : ℂ) * z)))) K :=
    ((curve_log_euclideanNorm_continuous f).comp
      (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact hK
  have hW : AnalyticOnNhd ℂ (fun z => FewInflection.wronskian 1 f.coord ((t : ℂ) * z)) univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((FewInflection.differentiable_wronskian f).comp (differentiable_id.const_mul (t : ℂ)))
  exact (hn.const_mul 2).sub (integrableOn_log_norm_on_compact hW (subset_univ K) hK)

noncomputable def scalarNormalizedSpherePotential (f : Curve 1) (t : ℝ) (z : ℂ) : ℝ :=
  scalarSphericalLogPotential f.coord ((t : ℂ) * z) / characteristic f t

/-- Exact dilation identity of the concrete potential, including its chosen
representatives at critical points. No limiting phase has been selected. -/
theorem scalarNormalizedSpherePotential_dilate (f : Curve 1) {c t : ℝ}
    (ht : characteristic f t ≠ 0) (hct : characteristic f (c * t) ≠ 0) (z : ℂ) :
    scalarNormalizedSpherePotential f (c * t) z =
      (characteristic f t / characteristic f (c * t)) *
        scalarNormalizedSpherePotential f t ((c : ℂ) * z) := by
  have hz : ((c * t : ℝ) : ℂ) * z = (t : ℂ) * ((c : ℂ) * z) := by push_cast; ring
  unfold scalarNormalizedSpherePotential
  rw [hz]
  field_simp

end ModifiedCartan
#print axioms ModifiedCartan.scalarSphericalLogPotential_rescaled
#print axioms ModifiedCartan.scalarSphericalLogPotential_integrableOn_scaled
#print axioms ModifiedCartan.scalarNormalizedSpherePotential_dilate
