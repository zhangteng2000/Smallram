import FewInflection.WronskianRegularity

open scoped BigOperators Topology
open Filter MeromorphicAt MeromorphicOn MeasureTheory Metric Real Set Topology
open scoped ComplexConjugate

namespace FewInflection

noncomputable section

/-! ### Jensen's inequality for the projective vector norm

The norm on `Index n → ℂ` is the finite-product (sup) norm.  At the centre
one coordinate therefore attains the vector norm.  Its scalar Jensen formula
can be compared with the vector logarithm on a circle.  At the isolated zeros
of that coordinate we use the vector logarithm itself; the modification is
codiscrete on the circle and hence leaves the circle average unchanged.  This
keeps the convention `Real.log 0 = 0` from being used as a false monotonicity
rule.
-/

lemma exists_coord_norm_eq_vector_norm {n : ℕ} (f : Curve n) (c : ℂ) :
    ∃ j : Index n, ‖f.coord j c‖ = ‖f.vector c‖ := by
  classical
  let p : Index n → NNReal := fun j => ‖f.coord j c‖₊
  obtain ⟨j, hj, hsup⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Index n))
      Finset.univ_nonempty p
  refine ⟨j, ?_⟩
  have hsup' := congrArg (fun x : NNReal => (x : ℝ)) hsup
  simpa [p, Curve.vector, Pi.norm_def] using hsup'.symm

lemma exists_coord_norm_eq_vector_norm_zero {n : ℕ} (f : Curve n) :
    ∃ j : Index n, ‖f.coord j 0‖ = ‖f.vector 0‖ := by
  simpa using exists_coord_norm_eq_vector_norm f 0

theorem characteristic_nonneg_of_reduced_curve_at
    {n : ℕ} (f : Curve n) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    0 ≤ Real.circleAverage (fun z : ℂ => Real.log ‖f.vector z‖) c r -
      Real.log ‖f.vector c‖ := by
  classical
  obtain ⟨j, hj⟩ := exists_coord_norm_eq_vector_norm f c
  have hgc : f.coord j c ≠ 0 := by
    intro hzero
    apply f.vector_ne_zero c
    apply norm_eq_zero.mp
    rw [← hj, hzero]
    simp
  have hA : AnalyticOnNhd ℂ (f.coord j) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)
  have hAc : AnalyticAt ℂ (f.coord j) c := hA c (Set.mem_univ _)
  have hfinitec : meromorphicOrderAt (f.coord j) c ≠ ⊤ := by
    have ho : analyticOrderAt (f.coord j) c = 0 :=
      hAc.analyticOrderAt_eq_zero.mpr hgc
    rw [hAc.meromorphicOrderAt_eq, ho]
    norm_num
  have hfinite : ∀ u ∈ (Set.univ : Set ℂ),
      meromorphicOrderAt (f.coord j) u ≠ ⊤ := by
    intro u hu
    exact hA.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ _) hu hfinitec
  have hAs : MeromorphicOn (f.coord j) (sphere c |r|) := by
    intro u hu
    exact hA.meromorphicOn u (Set.mem_univ _)
  have hfinite_s : ∀ u ∈ sphere c |r|,
      meromorphicOrderAt (f.coord j) u ≠ ⊤ := by
    intro u hu
    exact hfinite u (Set.mem_univ _)
  have hnonzero : ∀ᶠ z in codiscreteWithin (sphere c |r|),
      f.coord j z ≠ 0 := by
    exact hAs.codiscreteWithin_setOfPred_ne_zero hfinite_s
  let hmod : ℂ → ℝ := fun z =>
    if f.coord j z = 0 then Real.log ‖f.vector z‖
    else Real.log ‖f.coord j z‖
  have heq : hmod =ᶠ[codiscreteWithin (sphere c |r|)]
      (fun z => Real.log ‖f.coord j z‖) := by
    filter_upwards [hnonzero] with z hz
    simp [hmod, hz]
  have hscalar_int : CircleIntegrable
      (fun z : ℂ => Real.log ‖f.coord j z‖) c r := by
    exact hAs.circleIntegrable_log_norm
  have hmod_int : CircleIntegrable hmod c r := by
    exact CircleIntegrable.congr_codiscreteWithin heq.symm hscalar_int
  have hvec_cont : Continuous (fun z : ℂ => ‖f.vector z‖) := by
    exact (continuous_pi (fun k => (f.holomorphic k).continuous)).norm
  have hvec_log_cont : Continuous (fun z : ℂ => Real.log ‖f.vector z‖) := by
    apply hvec_cont.log
    intro z
    exact norm_ne_zero_iff.mpr (f.vector_ne_zero z)
  have hvec_int : CircleIntegrable
      (fun z : ℂ => Real.log ‖f.vector z‖) c r :=
    hvec_log_cont.continuousOn.circleIntegrable'
  have hpoint : ∀ z ∈ sphere c |r|,
      hmod z ≤ Real.log ‖f.vector z‖ := by
    intro z hz
    by_cases hz0 : f.coord j z = 0
    · simp [hmod, hz0]
    · have hgz : 0 < ‖f.coord j z‖ := norm_pos_iff.mpr hz0
      have hvz : 0 < ‖f.vector z‖ := norm_pos_iff.mpr (f.vector_ne_zero z)
      have hnorm : ‖f.coord j z‖ ≤ ‖f.vector z‖ := by
        exact norm_le_pi_norm (f.vector z) j
      have hlog := (Real.strictMonoOn_log.le_iff_le hgz hvz).2 hnorm
      simpa [hmod, hz0] using hlog
  have havg_le : Real.circleAverage hmod c r ≤
      Real.circleAverage (fun z : ℂ => Real.log ‖f.vector z‖) c r :=
    Real.circleAverage_mono hmod_int hvec_int hpoint
  have havg_eq : Real.circleAverage hmod c r =
      Real.circleAverage (fun z : ℂ => Real.log ‖f.coord j z‖) c r := by
    exact Real.circleAverage_congr_codiscreteWithin heq (ne_of_gt hr)
  have hjensen := scalar_circleAverage_log_norm_sub_nonneg_at
    (f.holomorphic j) hr hgc
  have hcenter : Real.log ‖f.coord j c‖ =
      Real.log ‖f.vector c‖ := by rw [hj]
  rw [← hcenter]
  linarith

theorem characteristic_nonneg_of_reduced_curve
    {n : ℕ} (f : Curve n) {r : ℝ} (hr : 0 < r) :
    0 ≤ characteristic f r := by
  unfold characteristic
  exact characteristic_nonneg_of_reduced_curve_at f 0 hr

end

end FewInflection
