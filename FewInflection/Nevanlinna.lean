import FewInflection.VectorJensen
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

open scoped BigOperators Topology
open Filter Asymptotics MeromorphicAt MeromorphicOn MeasureTheory Metric Real Set Topology
open ValueDistribution

namespace FewInflection
noncomputable section

lemma quotient_log_pos_le_vector_sub_coord
    {n : ℕ} (f : Curve n) (j l : Index n) (z : ℂ)
    (hj : f.coord j z ≠ 0) :
    log⁺ ‖f.coord l z / f.coord j z‖ ≤
      Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖ := by
  have hvec : ‖f.coord l z‖ ≤ ‖Curve.vector f z‖ :=
    norm_le_pi_norm (Curve.vector f z) l
  have hjnorm : 0 < ‖f.coord j z‖ := norm_pos_iff.mpr hj
  have hvecpos : 0 < ‖Curve.vector f z‖ :=
    norm_pos_iff.mpr (Curve.vector_ne_zero f z)
  have hratio : ‖f.coord j z‖ ≤ ‖Curve.vector f z‖ :=
    norm_le_pi_norm (Curve.vector f z) j
  have hlog : Real.log ‖f.coord j z‖ ≤ Real.log ‖Curve.vector f z‖ :=
    (Real.strictMonoOn_log.le_iff_le hjnorm hvecpos).2 hratio
  have hlnonneg : 0 ≤ Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖ := by
    linarith
  rw [norm_div]
  by_cases hl : f.coord l z = 0
  · simp [hl]
    exact hlog
  · have hln : Real.log ‖f.coord l z‖ - Real.log ‖f.coord j z‖ ≤
        Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖ := by
      have hll : Real.log ‖f.coord l z‖ ≤ Real.log ‖Curve.vector f z‖ :=
        (Real.strictMonoOn_log.le_iff_le (norm_pos_iff.mpr hl) hvecpos).2 hvec
      linarith
    rw [Real.posLog_apply]
    rw [Real.log_div (norm_ne_zero_iff.mpr hl) (norm_ne_zero_iff.mpr hj)]
    exact max_le hlnonneg hln

theorem quotient_proximity_le_curve_log_difference
    {n : ℕ} (f : Curve n) (j l : Index n) (hj0 : f.coord j 0 ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    proximity (fun z => f.coord l z / f.coord j z) ⊤ r ≤
      Real.circleAverage (fun z : ℂ =>
        Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖) 0 r := by
  have hAj : AnalyticOnNhd ℂ (f.coord j) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)
  have hAl : AnalyticOnNhd ℂ (f.coord l) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic l)
  have hml : Meromorphic (f.coord l) := by
    intro z
    exact (hAl z (Set.mem_univ z)).meromorphicAt
  have hmj : Meromorphic (f.coord j) := by
    intro z
    exact (hAj z (Set.mem_univ z)).meromorphicAt
  have hq : Meromorphic (fun z => f.coord l z / f.coord j z) := hml.div hmj
  have hfinite0 : meromorphicOrderAt (f.coord j) 0 ≠ ⊤ := by
    have ho : analyticOrderAt (f.coord j) 0 = 0 :=
      (hAj 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hj0
    rw [(hAj 0 (Set.mem_univ _)).meromorphicOrderAt_eq, ho]
    norm_num
  have hfinite : ∀ u : ℂ, meromorphicOrderAt (f.coord j) u ≠ ⊤ := by
    intro u
    exact hAj.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) hfinite0
  have hAsj : MeromorphicOn (f.coord j) (sphere 0 |r|) := by
    intro u hu
    exact hAj.meromorphicOn u (Set.mem_univ _)
  have hfinite_s : ∀ u ∈ sphere (0 : ℂ) |r|,
      meromorphicOrderAt (f.coord j) u ≠ ⊤ := by
    intro u hu
    exact hfinite u
  have hnonzero : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|),
      f.coord j z ≠ 0 := by
    exact hAsj.codiscreteWithin_setOfPred_ne_zero hfinite_s
  have hq_int : CircleIntegrable
      (fun z : ℂ => log⁺ ‖f.coord l z / f.coord j z‖) 0 r :=
    hq.meromorphicOn.circleIntegrable_posLog_norm
  let hmod : ℂ → ℝ := fun z =>
    if f.coord j z = 0 then
      Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖
    else log⁺ ‖f.coord l z / f.coord j z‖
  have heq : hmod =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)]
      (fun z : ℂ => log⁺ ‖f.coord l z / f.coord j z‖) := by
    filter_upwards [hnonzero] with z hz
    simp [hmod, hz]
  have hmod_int : CircleIntegrable hmod 0 r :=
    CircleIntegrable.congr_codiscreteWithin heq.symm hq_int
  have hvec_cont : Continuous (fun z : ℂ => ‖Curve.vector f z‖) := by
    exact (continuous_pi (fun k => (f.holomorphic k).continuous)).norm
  have hvec_log_cont : Continuous
      (fun z : ℂ => Real.log ‖Curve.vector f z‖) := by
    apply hvec_cont.log
    intro z
    exact norm_ne_zero_iff.mpr (Curve.vector_ne_zero f z)
  have hvec_int : CircleIntegrable
      (fun z : ℂ => Real.log ‖Curve.vector f z‖) 0 r :=
    hvec_log_cont.continuousOn.circleIntegrable'
  have hcoord_int : CircleIntegrable
      (fun z : ℂ => Real.log ‖f.coord j z‖) 0 r :=
    hAsj.circleIntegrable_log_norm
  have hdiff_int : CircleIntegrable
      (fun z : ℂ => Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖) 0 r := by
    convert hvec_int.sub hcoord_int using 1 <;> rfl
  have hpoint : ∀ z ∈ sphere (0 : ℂ) |r|, hmod z ≤
      Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖ := by
    intro z hz
    by_cases hz0 : f.coord j z = 0
    · simp [hmod, hz0]
    · simp [hmod, hz0]
      simpa only [norm_div] using quotient_log_pos_le_vector_sub_coord f j l z hz0
  have havg_le : Real.circleAverage hmod 0 r ≤
      Real.circleAverage (fun z : ℂ =>
        Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖) 0 r :=
    Real.circleAverage_mono hmod_int hdiff_int hpoint
  rw [ValueDistribution.proximity_top]
  have havg_eq : Real.circleAverage hmod 0 r =
      Real.circleAverage (fun z : ℂ => log⁺ ‖f.coord l z / f.coord j z‖) 0 r :=
    Real.circleAverage_congr_codiscreteWithin heq hr
  rw [← havg_eq]
  exact havg_le

theorem quotient_logCounting_top_le_coord_zero
    {n : ℕ} (f : Curve n) (j l : Index n) (hj0 : f.coord j 0 ≠ 0) {r : ℝ} (hr : 1 ≤ r) :
    logCounting (fun z => f.coord l z / f.coord j z) ⊤ r ≤
      logCounting (f.coord j) 0 r := by
  have hAj : AnalyticOnNhd ℂ (f.coord j) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)
  have hAl : AnalyticOnNhd ℂ (f.coord l) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic l)
  have hmj : Meromorphic (f.coord j) := by
    intro z
    exact (hAj z (Set.mem_univ z)).meromorphicAt
  have hfinite0 : meromorphicOrderAt (f.coord j) 0 ≠ ⊤ := by
    have ho : analyticOrderAt (f.coord j) 0 = 0 :=
      (hAj 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hj0
    rw [(hAj 0 (Set.mem_univ _)).meromorphicOrderAt_eq, ho]
    norm_num
  have hfinite : ∀ u : ℂ, meromorphicOrderAt (f.coord j) u ≠ ⊤ := by
    intro u
    exact hAj.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) hfinite0
  have hmi : Meromorphic ((f.coord j)⁻¹) := by
    simpa only [Pi.inv_apply] using hmj.inv
  have hfinitei : ∀ u : ℂ, meromorphicOrderAt ((f.coord j)⁻¹) u ≠ ⊤ := by
    intro u
    change meromorphicOrderAt (f.coord j)⁻¹ u ≠ (⊤ : WithTop ℤ)
    rw [meromorphicOrderAt_inv]
    simp [hfinite u]
  by_cases hl : f.coord l = 0
  · have hquot : (fun z => f.coord l z / f.coord j z) = 0 := by
      funext z
      simp [hl]
    rw [hquot]
    simpa using (ValueDistribution.logCounting_nonneg (f := f.coord j)
      (e := (0 : WithTop ℂ)) hr)
  · obtain ⟨z₀, hz₀⟩ := Function.ne_iff.mp hl
    have hml : Meromorphic (f.coord l) := by
      intro z
      exact (hAl z (Set.mem_univ z)).meromorphicAt
    have hfiniteL0 : meromorphicOrderAt (f.coord l) z₀ ≠ ⊤ := by
      have ho : analyticOrderAt (f.coord l) z₀ = 0 :=
        (hAl z₀ (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hz₀
      rw [(hAl z₀ (Set.mem_univ _)).meromorphicOrderAt_eq, ho]
      norm_num
    have hfiniteL : ∀ u : ℂ, meromorphicOrderAt (f.coord l) u ≠ ⊤ := by
      intro u
      exact hAl.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
        isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) hfiniteL0
    have hmul := ValueDistribution.logCounting_mul_top_le (f₁ := f.coord l)
      (f₂ := (f.coord j)⁻¹) hr hml hfiniteL hmi hfinitei
    have hrew : (f.coord l * ((f.coord j)⁻¹)) =
        (fun z => f.coord l z / f.coord j z) := by
      funext z
      simp [div_eq_mul_inv]
    have hmul' : logCounting (fun z => f.coord l z / f.coord j z) ⊤ r ≤
        (logCounting (f.coord l) ⊤ + logCounting ((f.coord j)⁻¹) ⊤) r := by
      simpa only [hrew] using hmul
    have hltop : logCounting (f.coord l) ⊤ = 0 := by
      rw [ValueDistribution.logCounting_top, negPart_eq_zero.mpr hAl.divisor_nonneg]
      simp
    rw [hltop, zero_add, ValueDistribution.logCounting_inv] at hmul'
    exact hmul'

/-! A curve-coordinate quotient has characteristic controlled by the projective
    characteristic.  This is the precise finite-radius form of the estimate
    used in the first Nevanlinna reduction. -/
theorem quotient_characteristic_le_curve
    {n : ℕ} (f : Curve n) (j l : Index n) (hj0 : f.coord j 0 ≠ 0)
    {r : ℝ} (hr : 1 ≤ r) :
    ValueDistribution.characteristic (fun z => f.coord l z / f.coord j z) ⊤ r ≤
      characteristic f r + Real.log ‖Curve.vector f 0‖ - Real.log ‖f.coord j 0‖ := by
  have hAj : AnalyticOnNhd ℂ (f.coord j) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)
  have hvec_cont : Continuous (fun z : ℂ => ‖Curve.vector f z‖) := by
    exact (continuous_pi (fun k => (f.holomorphic k).continuous)).norm
  have hvec_log_cont : Continuous
      (fun z : ℂ => Real.log ‖Curve.vector f z‖) := by
    apply hvec_cont.log
    intro z
    exact norm_ne_zero_iff.mpr (Curve.vector_ne_zero f z)
  have hvec_int : CircleIntegrable
      (fun z : ℂ => Real.log ‖Curve.vector f z‖) 0 r :=
    hvec_log_cont.continuousOn.circleIntegrable'
  have hcoord_int : CircleIntegrable
      (fun z : ℂ => Real.log ‖f.coord j z‖) 0 r := by
    have hAsj : MeromorphicOn (f.coord j) (sphere (0 : ℂ) |r|) := by
      intro u hu
      exact hAj.meromorphicOn u (Set.mem_univ _)
    exact hAsj.circleIntegrable_log_norm
  have hdiff_int : CircleIntegrable
      (fun z : ℂ => Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖) 0 r := by
    convert hvec_int.sub hcoord_int using 1 <;> rfl
  have hprox := quotient_proximity_le_curve_log_difference f j l hj0
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))
  have hcount := quotient_logCounting_top_le_coord_zero f j l hj0 hr
  have hJ := logCounting_zero_eq_circleAverage_sub_const_of_entire
    (f.holomorphic j) (lt_of_lt_of_le zero_lt_one hr) hj0
  have hsub : Real.circleAverage (fun z : ℂ =>
      Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖) 0 r =
      Real.circleAverage (fun z : ℂ => Real.log ‖Curve.vector f z‖) 0 r -
        Real.circleAverage (fun z : ℂ => Real.log ‖f.coord j z‖) 0 r := by
    convert Real.circleAverage_sub hvec_int hcoord_int using 1 <;> rfl
  rw [ValueDistribution.characteristic]
  calc
    proximity (fun z => f.coord l z / f.coord j z) ⊤ r +
          logCounting (fun z => f.coord l z / f.coord j z) ⊤ r
        ≤ Real.circleAverage (fun z : ℂ =>
            Real.log ‖Curve.vector f z‖ - Real.log ‖f.coord j z‖) 0 r +
          logCounting (f.coord j) 0 r := add_le_add hprox hcount
    _ = (Real.circleAverage (fun z : ℂ => Real.log ‖Curve.vector f z‖) 0 r -
          Real.circleAverage (fun z : ℂ => Real.log ‖f.coord j z‖) 0 r) +
          (Real.circleAverage (fun z : ℂ => Real.log ‖f.coord j z‖) 0 r -
            Real.log ‖f.coord j 0‖) := by
          rw [hsub, hJ]
    _ = characteristic f r + Real.log ‖Curve.vector f 0‖ - Real.log ‖f.coord j 0‖ := by
          unfold characteristic
          ring

end
end FewInflection
