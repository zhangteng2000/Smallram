import ModifiedCartan.ClassicalWeakGradient
import ModifiedCartan.LocalLogHypotheses

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! The analytic log modulus has weak complex gradient h'/h, supporting
`lem:logderivlimit`. The constructed zero potential proves existence across
zeros; classical derivatives and AE uniqueness identify the gradient. Locality
then proves the statement on an arbitrary open connected complex domain. -/

theorem analytic_ae_ne_zero {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hnonzero : ∃ b ∈ U, f b ≠ 0) :
    ∀ᵐ z ∂volume.restrict U, f z ≠ 0 := by
  apply ae_restrict_le_codiscreteWithin hU.measurableSet
  apply (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hUc).resolve_left
  intro hz
  obtain ⟨b, hb, hb0⟩ := hnonzero
  exact hb0 (hz hb)

theorem HasWeakComplexGradient.eq_logDeriv {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hfnz : ∀ᵐ z ∂volume.restrict U, f z ≠ 0) {g : ℂ → ℂ}
    (hg : HasWeakComplexGradient U (fun z => Real.log ‖f z‖) g) :
    g =ᵐ[volume.restrict U] logDeriv f := by
  let V := U ∩ f ⁻¹' ({0}ᶜ : Set ℂ)
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hharm : HarmonicOnNhd (fun z => Real.log ‖f z‖) V := by
    intro z hz
    exact (hf z hz.1).harmonicAt_log_norm hz.2
  have hgrad := contDiffOn_hasWeakComplexGradient hV (hharm.contDiffOn.of_le (by norm_num))
  have heq := (hg.restrict (show V ⊆ U from inter_subset_left)).unique hV hgrad
  have heq' : g =ᵐ[volume.restrict V] logDeriv f := by
    filter_upwards [heq, ae_restrict_mem hV.measurableSet] with z hz hzV
    rw [hz, logDeriv_apply]
    exact classicalComplexGradient_log_norm (hf z hzV.1).differentiableAt.hasDerivAt hzV.2
  filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' hV.measurableSet).mp heq'),
    hfnz, ae_restrict_mem hU.measurableSet] with z hz hznz hzU
  exact hz ⟨hzU, hznz⟩

theorem logNorm_hasWeakComplexGradient_on_ball {f : ℂ → ℂ} {c b : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : b ∈ ball c R) (hb0 : f b ≠ 0) :
    HasWeakComplexGradient (ball c R) (fun z => Real.log ‖f z‖) (logDeriv f) := by
  obtain ⟨H, hH, hAE⟩ := logNorm_eq_logPotential_add_harmonic_on_ball hf hb hb0
  let ν := finiteZeroCountingMeasure f (ball c R) hf.meromorphicOn.divisor_ball_support_finite
  obtain ⟨S, hS, _, hsupp⟩ :=
    finiteZeroCountingMeasure_ae_mem_compact hf.meromorphicOn.divisor_ball_support_finite
  have hV : HasWeakComplexGradient (ball c R) (logPotential ν) (cauchyTransform ν) :=
    logPotential_hasWeakComplexGradient ν hS hsupp _
  have hHgrad := contDiffOn_hasWeakComplexGradient isOpen_ball (hH.contDiffOn.of_le (by norm_num))
  have hg := (hV.add hHgrad).congr_function_ae isOpen_ball hAE.symm
  have hfnz := analytic_ae_ne_zero isOpen_ball (convex_ball c R).isPreconnected
    (hf.mono ball_subset_closedBall) ⟨b, hb, hb0⟩
  exact hg.congr_gradient_ae isOpen_ball (hg.eq_logDeriv isOpen_ball
    (hf.mono ball_subset_closedBall) hfnz)

theorem logNorm_hasWeakComplexGradient {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hnonzero : ∃ b ∈ U, f b ≠ 0) :
    HasWeakComplexGradient U (fun z => Real.log ‖f z‖) (logDeriv f) := by
  apply HasWeakComplexGradient.of_locally
  intro c hc
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hc
  have hR : closedBall c (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
  obtain ⟨b, hb, hb0⟩ := analytic_exists_ne_zero_on_ball hUc hf hnonzero (half_pos hε)
    (ball_subset_closedBall.trans hR)
  exact ⟨ball c (ε / 2), isOpen_ball, mem_ball_self (half_pos hε),
    ball_subset_closedBall.trans hR, logNorm_hasWeakComplexGradient_on_ball (hf.mono hR) hb hb0⟩



end ModifiedCartan


