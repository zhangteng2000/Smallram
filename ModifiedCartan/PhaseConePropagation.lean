import ModifiedCartan.PhaseCutoffMonotonicity
import ModifiedCartan.StrictPhaseCone

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

def IsEssentialPhaseAt (g : ℂ → ℂ) (a c : ℂ) : Prop :=
  ∀ δ : ℝ, 0 < δ → volume {z | z ∈ ball c δ ∧ g z = a} ≠ 0

theorem ae_phaseCutoff_smoothing_tendsto {K : Set ℂ} (hK : IsCompact K)
    {g : ℂ → ℂ} (hg : IntegrableOn g K) (a : ℂ) :
    ∀ᵐ x ∂volume, Tendsto (fun ν => (phaseCutoff K g a ⋆[lsmul ℝ ℝ, volume]
      (shrinkingWeakBump ν).normed volume) x) atTop (𝓝 (phaseCutoff K g a x)) := by
  have hratio : ∀ ν, (shrinkingWeakBump ν).rOut ≤ 2 * (shrinkingWeakBump ν).rIn := by
    intro ν
    dsimp only [shrinkingWeakBump]
    linarith
  have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    shrinkingWeakBump_tendsto (Eventually.of_forall hratio) (integrable_phaseCutoff hK hg a).locallyIntegrable
  simpa only [real_convolution_comm (phaseCutoff K g a)] using hh

/-- A phase of positive measure in every neighborhood of the center fills
its strict supporting cone, using one common family of actual smoothings. -/
theorem IsSubharmonicOn.phase_eq_ae_on_strict_cone
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    {A : Finset ℂ} (hA : ∀ᵐ z ∂volume.restrict U, g z ∈ A)
    (a : ℂ) {c : ℂ} {s r R : ℝ} (hs : 0 < s) (hsr : s < r) (hrR : r < R)
    (hball : closedBall c R ⊆ U) (hess : IsEssentialPhaseAt g a c) :
    ∀ᵐ x ∂volume.restrict (ball c s ∩ (fun x => x - c) ⁻¹' strictPhaseCone A a), g x = a := by
  classical
  have hqi := hw.gradient_integrable _ (isCompact_closedBall c R) hball
  have hlim := ae_phaseCutoff_smoothing_tendsto (isCompact_closedBall c R) hqi a
  have hmono := hu.eventually_phaseCutoff_convolution_mono hU hc hw hC hbound a hsr hrR hball
  have hS : IsOpen (ball c s ∩ (fun x => x - c) ⁻¹' strictPhaseCone A a) :=
    isOpen_ball.inter ((isOpen_strictPhaseCone A a).preimage (continuous_id.sub continuous_const))
  filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem hS.measurableSet] with x hxlim hx
  have hnear : ball c s ∩ (fun y => x - y) ⁻¹' strictPhaseCone A a ∈ 𝓝 c := by
    apply IsOpen.mem_nhds
      (isOpen_ball.inter ((isOpen_strictPhaseCone A a).preimage (continuous_const.sub continuous_id)))
    exact ⟨mem_ball_self hs, hx.2⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨y, hy, hylim⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (hess δ hδ)
    (ae_restrict_of_ae hlim)
  have hyball : y ∈ ball c s := (hδsub hy.1).1
  have hycone : x - y ∈ strictPhaseCone A a := (hδsub hy.1).2
  have hcone := strictPhaseCone_ae_halfPlane hA hycone
  have hle := le_of_tendsto_of_tendsto hylim hxlim
    (hmono.mono (fun ν hν => hν y hyball x hx.1 hcone))
  have hsub : ball c s ⊆ closedBall c R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (hsr.trans hrR).le)
  rw [phaseCutoff_eq (hsub hyball), phaseIndicator_eq_ite, if_pos hy.2,
    phaseCutoff_eq (hsub hx.1), phaseIndicator_eq_ite] at hle
  by_contra hxa
  simp only [if_neg hxa] at hle
  norm_num at hle

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.phase_eq_ae_on_strict_cone
