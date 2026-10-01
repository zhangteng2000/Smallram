import ModifiedCartan.UnitaryComponentRegularity
import ModifiedCartan.ScalarSharpScaleBounds
import ModifiedCartan.JetLogCompactness

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem subharmonic_eventually_upper_bound_eventual {U K V : Set ℂ}
    {u : ℕ → ℂ → EReal} {v : ℂ → ℝ}
    (hu : ∀ᶠ ν in atTop, IsSubharmonicOn U (u ν))
    (hconv : LocalLpConvergence 1 U (fun ν z => (u ν z).toReal) v)
    (hK : IsCompact K) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hKV : K ⊆ V) (hVU : closure V ⊆ U)
    {M : ℝ} (hM : ∀ᵐ z ∂volume.restrict V, v z ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ν in atTop, ∀ x ∈ K, u ν x ≤ ((M + ε : ℝ) : EReal) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  have hh := subharmonic_eventually_upper_bound (fun ν => hN (ν + N) (by omega))
    (hconv.comp_tendsto (tendsto_add_atTop_nat N)) hK hV hVc hKV hVU hM hε
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp hh
  refine eventually_atTop.mpr ⟨Q + N, ?_⟩
  intro ν hν
  have hh := hQ (ν - N) (by omega)
  simpa only [Nat.sub_add_cancel (show N ≤ ν by omega)] using hh

/-- A local upper bound on the actual continuous norm limit supplies the
sharp uniform exponential upper bound for the original gauged representation.
The finite-prefix analyticity and every original component are accounted for. -/
theorem ArbitraryRadiusLimitData.actual_norm_eventually_upper_bound
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {K V : Set ℂ} (hK : IsCompact K) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hKV : K ⊆ V) (hVU : closure V ⊆ ball (0 : ℂ) 4)
    {M ε : ℝ} (hM : ∀ z ∈ V, (d.U z).toReal ≤ M) (hε : 0 < ε) :
    ∀ᶠ ν in atTop, ∀ z ∈ K,
      euclideanNorm (fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z) ≤
        Real.exp ((M + ε) * characteristic f (r (d.subseq ν))) := by
  have hcoord (j : Index n) : ∀ᶠ ν in atTop, ∀ z ∈ K,
      normalizedExtendedLog (characteristic f (r (d.subseq ν)))
        (rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j) z ≤ ((M + ε / 2 : ℝ) : EReal) := by
    have hsub : ∀ᶠ ν in atTop, IsSubharmonicOn (ball (0 : ℂ) 4)
        (normalizedExtendedLog (characteristic f (r (d.subseq ν)))
          (rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j)) := by
      filter_upwards [d.replacement.gauge_analytic] with ν hν
      apply normalizedExtendedLog_isSubharmonicOn isOpen_ball (convex_ball (0 : ℂ) 4).isPreconnected
      · intro z hz
        exact rescaledRepresentation_analyticAt f (r (d.subseq ν))
          (hν z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) hz)) j
      · exact (d.coordinate_limit j).normalizedLog_nontrivial isOpen_ball
          ⟨0, mem_ball_self (by norm_num)⟩ (d.scale_pos ν)
      · exact d.scale_pos ν
    have hv : ∀ᵐ z ∂volume.restrict V, d.v j z ≤ M := by
      filter_upwards [(d.coordinate_representative j).filter_mono
        (ae_mono (Measure.restrict_mono_set _ (subset_closure.trans hVU))),
        ae_restrict_mem hV.measurableSet] with z hz hzV
      have hz4 := hVU (subset_closure hzV)
      have hh : d.u j z ≤ d.U z := by
        rw [d.maximum]
        exact Finset.le_sup (f := fun k => d.u k z) (Finset.mem_univ j)
      rw [hz, d.norm_limit_continuous.1 z hz4] at hh
      exact (EReal.coe_le_coe_iff.mp hh).trans (hM z hzV)
    exact subharmonic_eventually_upper_bound_eventual hsub (d.coordinate_limit j).real_convergence
      hK hV hVc hKV hVU hv (half_pos hε)
  have habs := constant_mul_exp_neg_le_eventually d.scale_tendsto
    (show -(M + ε) < -(M + ε / 2) by linarith) (Real.sqrt_nonneg (n + 1 : ℝ))
  filter_upwards [eventually_all.mpr hcoord, habs] with ν hν haν
  intro z hz
  have hvec : ‖(fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z)‖ ≤
      Real.exp ((M + ε / 2) * characteristic f (r (d.subseq ν))) := by
    apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).2
    intro j
    exact (normalizedExtendedLog_le_iff_norm_le_exp (d.scale_pos ν) _ z (M + ε / 2)).1 (hν j z hz)
  exact (euclideanNorm_le _).trans
    ((mul_le_mul_of_nonneg_left hvec (Real.sqrt_nonneg _)).trans
      (by simpa only [neg_neg] using haν))

theorem ArbitraryRadiusLimitData.actual_norm_near_point
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 4) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, closedBall z δ ⊆ ball (0 : ℂ) 4 ∧
      ∀ᶠ ν in atTop, ∀ w ∈ closedBall z δ,
        euclideanNorm (fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j w) ≤
          Real.exp (((d.U z).toReal + ε) * characteristic f (r (d.subseq ν))) := by
  have hcont := d.norm_limit_continuous.2.continuousAt (isOpen_ball.mem_nhds hz)
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ℂ) 4 ∧
      (d.U w).toReal < (d.U z).toReal + ε / 2 :=
    (show ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ℂ) 4 from isOpen_ball.mem_nhds hz).and
      (hcont.eventually (gt_mem_nhds (show (d.U z).toReal < (d.U z).toReal + ε / 2 by linarith)))
  obtain ⟨b, hb, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  have hK : closedBall z (b / 4) ⊆ ball (0 : ℂ) 4 := fun w hw =>
    (hball w ((closedBall_subset_ball (by linarith : b / 4 < b)) hw)).1
  have hV : closure (ball z (b / 2)) ⊆ ball (0 : ℂ) 4 := by
    rw [closure_ball z (half_pos hb).ne']
    exact fun w hw => (hball w ((closedBall_subset_ball (by linarith : b / 2 < b)) hw)).1
  have hupper := d.actual_norm_eventually_upper_bound (isCompact_closedBall z (b / 4)) isOpen_ball
    (by rw [closure_ball z (half_pos hb).ne']; exact isCompact_closedBall _ _)
    (closedBall_subset_ball (by linarith : b / 4 < b / 2)) hV
    (fun w hw => (hball w ((ball_subset_ball (by linarith : b / 2 ≤ b)) hw)).2.le) (half_pos hε)
  refine ⟨b / 4, by positivity, hK, ?_⟩
  simpa only [show (d.U z).toReal + ε / 2 + ε / 2 = (d.U z).toReal + ε by ring] using hupper

end ModifiedCartan
#print axioms ModifiedCartan.subharmonic_eventually_upper_bound_eventual
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.actual_norm_eventually_upper_bound
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.actual_norm_near_point
