import ModifiedCartan.LogAreaJensen
import ModifiedCartan.DivisorPolynomial

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

/-- The circular logarithmic kernel, including circles through the pole. -/
theorem circleAverage_log_norm_sub_eq_log_max (a : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun z : ℂ => Real.log ‖z - a‖) 0 r =
      Real.log (max r ‖a‖) := by
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne']
  simp only [zero_sub, norm_neg]
  rw [Real.posLog_eq_log_max_one (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg a)),
    ← Real.log_mul hr.ne' (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))]
  congr 1
  rw [mul_max_of_nonneg _ _ hr.le, mul_one, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-- A finite fixed-radius formula for analytic logarithmic circle means.
Auxiliary to the integral bridge for LaTeX `thm:A` (b). -/
theorem analytic_log_circleAverage_finite_formula {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (ho : ∀ z : closedBall (0 : ℂ) R, meromorphicOrderAt f z ≠ ⊤) :
    ∃ (S : Finset ℂ) (w : ℂ → ℝ) (C : ℝ), (∀ z, 0 ≤ w z) ∧
      ∀ r : ℝ, 0 < r → r ≤ R →
        Real.circleAverage (fun z => Real.log ‖f z‖) 0 r =
          (∑ a ∈ S, w a * Real.log (max r ‖a‖)) + C := by
  classical
  let D := divisor f (closedBall (0 : ℂ) R)
  have hfin := D.finiteSupport (isCompact_closedBall (0 : ℂ) R)
  obtain ⟨g, hg, hg0, he⟩ := hf.meromorphicOn.extract_zeros_poles ho hfin
  have heLog := MeromorphicOn.extract_zeros_poles_log hg0 he
  have hsum : (∑ᶠ a, (fun z : ℂ => (D a : ℝ) * Real.log ‖z - a‖)) =
      (fun z : ℂ => ∑ a ∈ hfin.toFinset, (D a : ℝ) * Real.log ‖z - a‖) := by
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by
      intro a ha
      apply hfin.mem_toFinset.mpr
      by_contra ha0
      apply ha
      simp only [Function.mem_support, not_not] at ha0
      simp [ha0, Pi.zero_def])]
    funext z
    simp only [Finset.sum_apply]
  refine ⟨hfin.toFinset, fun a => (D a : ℝ), Real.log ‖g 0‖,
    fun a => by change 0 ≤ (D a : ℝ); exact_mod_cast hf.divisor_nonneg a, ?_⟩
  intro r hr hrR
  have hsub : closedBall (0 : ℂ) |r| ⊆ closedBall 0 R := by
    rw [abs_of_pos hr]
    exact closedBall_subset_closedBall hrR
  have hk (a : ℂ) : CircleIntegrable (fun z : ℂ => Real.log ‖z - a‖) 0 r :=
    (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm
  have hkw (a : ℂ) : CircleIntegrable (fun z : ℂ => (D a : ℝ) * Real.log ‖z - a‖) 0 r := (hk a).const_mul _
  have hci : CircleIntegrable
      (fun z : ℂ => ∑ a ∈ hfin.toFinset, (D a : ℝ) * Real.log ‖z - a‖) 0 r :=
    by simpa only [CircleIntegrable, Finset.sum_apply] using CircleIntegrable.sum hfin.toFinset (fun a _ => hkw a)
  calc
    _ = Real.circleAverage
        (fun z => (∑ a ∈ hfin.toFinset, (D a : ℝ) * Real.log ‖z - a‖) + Real.log ‖g z‖) 0 r := by
      apply Real.circleAverage_congr_codiscreteWithin _ hr.ne'
      have hh := codiscreteWithin_mono (sphere_subset_closedBall.trans hsub) heLog
      change (fun z => Real.log ‖f z‖) =ᶠ[codiscreteWithin (sphere 0 |r|)] (∑ᶠ a, (fun z : ℂ => (D a : ℝ) * Real.log ‖z - a‖)) + (fun z => Real.log ‖g z‖) at hh
      filter_upwards [hh] with z hz
      change Real.log ‖f z‖ = (∑ᶠ a, (fun z : ℂ => (D a : ℝ) * Real.log ‖z - a‖)) z + Real.log ‖g z‖ at hz
      simpa only [hsum] using hz
    _ = (∑ a ∈ hfin.toFinset, (D a : ℝ) *
        Real.circleAverage (fun z : ℂ => Real.log ‖z - a‖) 0 r) + Real.log ‖g 0‖ := by
      rw [Real.circleAverage_fun_add hci
        ((hg.mono (sphere_subset_closedBall.trans hsub)).meromorphicOn.circleIntegrable_log_norm),
        Real.circleAverage_fun_sum (fun a _ => hkw a)]
      congr 1
      · apply Finset.sum_congr rfl
        intro a _
        simpa only [smul_eq_mul] using (Real.circleAverage_fun_smul (a := (D a : ℝ)) (f := fun z : ℂ => Real.log ‖z - a‖) (c := 0) (R := r))
      · exact (hg.mono hsub).circleAverage_log_norm_of_ne_zero (fun z hz => hg0 ⟨z, hsub hz⟩)
    _ = _ := by simp_rw [circleAverage_log_norm_sub_eq_log_max _ hr]

/-- Analytic logarithmic means remain continuous and monotone across zero radii. -/
theorem analytic_log_circleAverage_continuous_monotone {f : ℂ → ℂ} {B : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 B)) (hn : ∃ z ∈ ball (0 : ℂ) B, f z ≠ 0) :
    ContinuousOn (Real.circleAverage (fun z => Real.log ‖f z‖) 0) (Ioo 0 B) ∧
      MonotoneOn (Real.circleAverage (fun z => Real.log ‖f z‖) 0) (Ioo 0 B) := by
  obtain ⟨z₀, hz₀, hn₀⟩ := hn
  have ho₀ : meromorphicOrderAt f z₀ ≠ ⊤ := by
    rw [(hf z₀ hz₀).meromorphicOrderAt_eq, (hf z₀ hz₀).analyticOrderAt_eq_zero.mpr hn₀]
    simp
  have ho (z : ℂ) (hz : z ∈ ball (0 : ℂ) B) : meromorphicOrderAt f z ≠ ⊤ :=
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_ball (0 : ℂ) B).isPreconnected hz₀ hz ho₀
  have hlocal (R : ℝ) (hRB : R < B) :
      ContinuousOn (Real.circleAverage (fun z => Real.log ‖f z‖) 0) (Ioo 0 R) ∧
      MonotoneOn (Real.circleAverage (fun z => Real.log ‖f z‖) 0) (Ioo 0 R) := by
    obtain ⟨S, w, C, hw, he⟩ := analytic_log_circleAverage_finite_formula
      (hf.mono (closedBall_subset_ball hRB))
      (fun z => ho z (closedBall_subset_ball hRB z.property))
    have hc : ContinuousOn (fun r : ℝ => (∑ a ∈ S, w a * Real.log (max r ‖a‖)) + C)
        (Ioo 0 R) := by
      apply ContinuousOn.add _ continuousOn_const
      apply continuousOn_finsetSum
      intro a _
      exact continuousOn_const.mul ((continuousOn_id.sup continuousOn_const).log
        (fun r hr => ne_of_gt (hr.1.trans_le (le_max_left _ _))))
    refine ⟨hc.congr (fun r hr => he r hr.1 hr.2.le), ?_⟩
    intro a ha b hb hab
    rw [he a ha.1 ha.2.le, he b hb.1 hb.2.le]
    apply add_le_add <;> try rfl
    apply Finset.sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (ha.1.trans_le (le_max_left _ _)) (max_le_max_right _ hab)) (hw z)
  constructor
  · intro r hr
    let R := (r + B) / 2
    have hrR : r < R := by dsimp [R]; linarith [hr.2]
    have hRB : R < B := by dsimp [R]; linarith [hr.2]
    exact ((hlocal R hRB).1.continuousAt (isOpen_Ioo.mem_nhds ⟨hr.1, hrR⟩)).continuousWithinAt
  · intro a ha b hb hab
    let R := (b + B) / 2
    have hbR : b < R := by dsimp [R]; linarith [hb.2]
    have hRB : R < B := by dsimp [R]; linarith [hb.2]
    exact (hlocal R hRB).2 ⟨ha.1, hab.trans_lt hbR⟩ ⟨hb.1, hbR⟩ hab

end ModifiedCartan
#print axioms ModifiedCartan.analytic_log_circleAverage_continuous_monotone
