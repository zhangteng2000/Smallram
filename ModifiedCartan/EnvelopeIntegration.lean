import ModifiedCartan.EnvelopeKernel
import ModifiedCartan.EnvelopeRadii

open scoped Topology
open Filter Set MeasureTheory Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

theorem envelope_integral_rescale (H : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    r * (∫ t in Ioi 0, H (3 * t) / (r + t) ^ 2) =
      ∫ u in Ioi 0, H (3 * r * u) / (1 + u) ^ 2 := by
  have h := integral_comp_mul_left_Ioi' (fun t => H (3 * t) / (r + t) ^ 2) 0 hr
  simp only [smul_eq_mul, mul_zero] at h
  calc
    _ = r * (r * ∫ u in Ioi 0, H (3 * (r * u)) / (r + r * u) ^ 2) := congrArg (fun x => r * x) h.symm
    _ = ∫ u in Ioi 0, r * (r * (H (3 * (r * u)) / (r + r * u) ^ 2)) := by
      rw [integral_const_mul, integral_const_mul]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      dsimp only
      rw [show r + r * u = r * (1 + u) by ring, mul_pow,
        show 3 * (r * u) = 3 * r * u by ring]
      calc
        _ = (r ^ 2 * H (3 * r * u)) / (r ^ 2 * (1 + u) ^ 2) := by ring
        _ = _ := mul_div_mul_left _ _ (pow_ne_zero 2 hr.ne')

/-- Integrability and the precise integral bound at a power-envelope
radius. In particular the Bochner integral is never used by defaulting an
unproved improper integral to zero. -/
theorem integral_envelope_at_radius {H : ℝ → ℝ} {r α : ℝ}
    (hr : 0 < r) (hα : 0 ≤ α) (hα1 : α < 1)
    (hH : ContinuousOn H (Ioi 0)) (hn : ∀ t, 0 < t → 0 ≤ H t)
    (hb : ∀ t, 0 < t → H t ≤ H r * max 1 ((t / r) ^ α)) :
    IntegrableOn (fun t => H (3 * t) / (r + t) ^ 2) (Ioi 0) ∧
      r * (∫ t in Ioi 0, H (3 * t) / (r + t) ^ 2) ≤ envelopeConstant α * H r := by
  have hscaled_cont : ContinuousOn (fun u => H (3 * r * u) / (1 + u) ^ 2) (Ioi (0 : ℝ)) := by
    apply (hH.comp (by fun_prop) (fun u hu => mul_pos (mul_pos (by norm_num) hr) hu)).div (by fun_prop)
    intro u hu
    exact pow_ne_zero 2 (by change 0 < u at hu; linarith)
  have hnonneg : ∀ u, 0 < u → 0 ≤ H (3 * r * u) / (1 + u) ^ 2 :=
    fun u hu => div_nonneg (hn _ (mul_pos (mul_pos (by norm_num) hr) hu)) (sq_nonneg _)
  have hle : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      H (3 * r * u) / (1 + u) ^ 2 ≤ H r * envelopeIntegrand α u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hh := hb (3 * r * u) (mul_pos (mul_pos (by norm_num) hr) hu)
    have harg : 3 * r * u / r = 3 * u := by field_simp
    rw [harg] at hh
    simpa only [envelopeIntegrand, mul_div_assoc] using div_le_div_of_nonneg_right hh (sq_nonneg (1 + u))
  have hmajorant : IntegrableOn (fun u => H r * envelopeIntegrand α u) (Ioi (0 : ℝ)) :=
    (envelope_integrand_integrable hα hα1).const_mul _
  have hscaled : IntegrableOn (fun u => H (3 * r * u) / (1 + u) ^ 2) (Ioi (0 : ℝ)) := by
    apply hmajorant.mono' (hscaled_cont.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [hle, ae_restrict_mem measurableSet_Ioi] with u hu hu0
    rwa [Real.norm_of_nonneg (hnonneg u hu0)]
  have hcomp : IntegrableOn (fun u => H (3 * (r * u)) / (r + r * u) ^ 2) (Ioi (0 : ℝ)) := by
    have hh : IntegrableOn (fun u => (r ^ 2)⁻¹ * (H (3 * r * u) / (1 + u) ^ 2)) (Ioi (0 : ℝ)) := hscaled.const_mul _
    apply hh.congr_fun _ measurableSet_Ioi
    intro u _
    dsimp only
    rw [show r + r * u = r * (1 + u) by ring, mul_pow,
      show 3 * (r * u) = 3 * r * u by ring]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨?_, ?_⟩
  · simpa only [mul_zero] using
      (integrableOn_Ioi_comp_mul_left_iff (fun t => H (3 * t) / (r + t) ^ 2) 0 hr).mp hcomp
  · rw [envelope_integral_rescale H hr]
    have hi := integral_mono_ae hscaled hmajorant hle
    rw [integral_const_mul] at hi
    exact hi.trans_eq (mul_comm _ _)

end ModifiedCartan
#print axioms ModifiedCartan.integral_envelope_at_radius
