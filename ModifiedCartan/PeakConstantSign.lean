import ModifiedCartan.DiskCircleUpper
import ModifiedCartan.CharacteristicPeaks
import ModifiedCartan.RescaledRepresentation

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Constant local L1 limits obey the upper bounds obtained from local
circle means of a dominating function. -/
theorem constant_log_limit_le_of_circle_means {f : ℕ → ℂ → ℂ}
    {L : ℕ → ℂ → ℝ} {s M : ℕ → ℝ} {a b R : ℝ}
    (hR : 0 < R) (hR3 : R < 3) (hs : ∀ ν, 0 < s ν)
    (hu : LocalLpConvergence 1 (ball (0 : ℂ) 3)
      (fun ν z => (s ν)⁻¹ * Real.log ‖f ν z‖) (fun _ => a))
    (hM : Tendsto M atTop (𝓝 b))
    (hd : ∀ᶠ ν in atTop, ContinuousOn (L ν) (closedBall (0 : ℂ) R) ∧
      (∀ r, 0 < r → r < R → Real.circleAverage (L ν) 0 r ≤ s ν * M ν) ∧
      ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) R), Real.log ‖f ν z‖ ≤ L ν z) : a ≤ b := by
  have hball := closedBall_subset_ball hR3 (x := (0 : ℂ))
  have hlu := hu.diskAverage_tendsto_const hR hball
  apply le_of_tendsto_of_tendsto hlu hM
  filter_upwards [hd] with ν hν
  have hleftC : IntegrableOn (fun z => (s ν)⁻¹ * Real.log ‖f ν z‖) (closedBall 0 R) :=
    memLp_one_iff_integrable.mp (hu.source_mem (closedBall 0 R) (isCompact_closedBall _ _) hball ν)
  have hleft := hleftC.mono_set ball_subset_closedBall
  have hright : IntegrableOn (L ν) (ball (0 : ℂ) R) := (hν.1.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hle := diskAverage_mono hR.le hleft (hright.const_mul (s ν)⁻¹)
    (hν.2.2.mono (fun _ hz => mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr (hs ν).le)))
  rw [diskAverage_const_mul hR.le (s ν)⁻¹ (L ν) 0] at hle
  calc
    _ ≤ (s ν)⁻¹ * diskAverage R (L ν) 0 := hle
    _ ≤ (s ν)⁻¹ * (s ν * M ν) := mul_le_mul_of_nonneg_left
      (diskAverage_le_of_circleAverage_le hR hν.1 hν.2.1) (inv_nonneg.mpr (hs ν).le)
    _ = M ν := by rw [← mul_assoc, inv_mul_cancel₀ (hs ν).ne', one_mul]

/-- The constant coordinate limits in Step 2 of `prop:indices` are
nonpositive. This uses the actual M9 circle mean identity and the exact
peak inequality on arbitrarily small fixed disks. -/
theorem peak_coordinate_constant_nonpos {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hf0 : ∀ j, f.coord j 0 ≠ 0)
    {r ε : ℕ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hrpos : ∀ ν, 0 < r ν)
    (hεpos : ∀ ν, 0 < ε ν) (hε : Tendsto ε atTop (𝓝 0))
    (hpeak : ∀ ν t, ε ν ≤ t → t ≤ (ε ν)⁻¹ →
      characteristic f (t * r ν) ≤ (1 + ε ν) * t ^ μ * characteristic f (r ν))
    {H : ℕ → ℂ → ℂ} {c : ℕ → ℝ}
    (hdata : ∀ᶠ ν in atTop, AnalyticOnNhd ℂ (H ν) (ball 0 3) ∧
      ∀ R, 0 < R → R < 3 → Real.circleAverage
        (fun z => Real.log (euclideanNorm (fun j => rescaledRepresentation f (r ν) (H ν) j z))) 0 R =
          characteristic f (R * r ν) + c ν)
    (hc : Tendsto (fun ν => c ν / characteristic f (r ν)) atTop (𝓝 0))
    (j : Index n) {a : ℝ}
    (hu : LocalLpConvergence 1 (ball (0 : ℂ) 3)
      (fun ν z => (characteristic f (r ν))⁻¹ *
        Real.log ‖rescaledRepresentation f (r ν) (H ν) j z‖) (fun _ => a)) : a ≤ 0 := by
  have hs (ν : ℕ) := characteristic_pos_of_transcendental f htrans (hrpos ν)
  have hb : ∀ b : ℝ, 0 < b → b < 3 → a ≤ b ^ μ := by
    intro b hb hb3
    apply constant_log_limit_le_of_circle_means hb hb3 hs hu
      (L := fun ν z => Real.log (euclideanNorm (fun j => rescaledRepresentation f (r ν) (H ν) j z)))
      (M := fun ν => (1 + ε ν) * b ^ μ + c ν / characteristic f (r ν))
    · simpa only [add_zero, one_mul] using
        ((((tendsto_const_nhds (x := (1 : ℝ))).add hε).mul_const (b ^ μ)).add hc)
    · filter_upwards [hdata, peak_window_eventually_contains hεpos hε hb] with ν hν hwindow
      have hL : ContinuousOn
          (fun z => Real.log (euclideanNorm (fun j => rescaledRepresentation f (r ν) (H ν) j z)))
          (ball (0 : ℂ) 3) := by
        simpa only [rescaledRepresentation_log_norm, Function.comp_def, Pi.mul_apply, Pi.sub_apply, id_eq] using!
          ((curve_log_euclideanNorm_continuous f).comp (continuous_const.mul continuous_id)).continuousOn.sub
            (Complex.continuous_re.comp_continuousOn hν.1.continuousOn)
      refine ⟨hL.mono (closedBall_subset_ball hb3), ?_, ?_⟩
      · intro t ht htb
        rw [hν.2 t ht (htb.trans hb3)]
        have hmono := characteristic_monotoneOn f (mul_pos ht (hrpos ν))
          (mul_pos hb (hrpos ν)) (mul_le_mul_of_nonneg_right htb.le (hrpos ν).le)
        have hp := hpeak ν b hwindow.1 hwindow.2
        have hcanc : characteristic f (r ν) * (c ν / characteristic f (r ν)) = c ν :=
          mul_div_cancel₀ _ (hs ν).ne'
        nlinarith
      · have hA : AnalyticOnNhd ℂ (rescaledRepresentation f (r ν) (H ν) j) (ball 0 3) :=
          fun z hz => rescaledRepresentation_analyticAt f (r ν) (hν.1 z hz) j
        have hn : rescaledRepresentation f (r ν) (H ν) j 0 ≠ 0 := by
          simpa only [rescaledRepresentation, mul_zero] using mul_ne_zero (Complex.exp_ne_zero _) (hf0 j)
        have hnAE := (analytic_ae_ne_zero isOpen_ball (convex_ball (0 : ℂ) 3).isPreconnected
          hA ⟨0, mem_ball_self (by norm_num), hn⟩).filter_mono
            (ae_mono (Measure.restrict_mono_set _ (ball_subset_ball hb3.le)))
        filter_upwards [hnAE] with z hz
        exact Real.log_le_log (norm_pos_iff.mpr hz)
          ((norm_le_pi_norm (fun k => rescaledRepresentation f (r ν) (H ν) k z) j).trans
            (norm_le_euclideanNorm _))
  have hlim : Tendsto (fun b : ℝ => b ^ μ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hμ.ne'] using
      ((Real.continuousAt_rpow_const 0 μ (Or.inr hμ.le)).tendsto.mono_left nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds (by norm_num : (0 : ℝ) < 3)).filter_mono
    nhdsWithin_le_nhds] with b hb0 hb3
  exact hb b hb0 hb3

end ModifiedCartan
#print axioms ModifiedCartan.peak_coordinate_constant_nonpos
