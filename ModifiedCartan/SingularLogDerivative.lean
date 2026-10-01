import ModifiedCartan.FiniteCauchyDerivatives
import ModifiedCartan.HarmonicComplexDerivatives
import ModifiedCartan.AnalyticWeakGradient

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric MeromorphicOn InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! The exact singular sum and harmonic remainder identities, LaTeX label `eq:singular-logderivative`. Zero sets and finite poles are removed only on null sets; differentiation is justified by analytic equality on open neighborhoods. -/

theorem logDeriv_potential_harmonic_ae {f : ℂ → ℂ} {c b : ℂ} {r R s : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : b ∈ ball c R) (hb0 : f b ≠ 0)
    (hrR : r ≤ R) {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    {H : ℂ → ℝ} (hH : HarmonicOnNhd H (ball c r))
    (heq : (fun z => s⁻¹ * Real.log ‖f z‖) =ᵐ[volume.restrict (ball c r)]
      (fun z => logPotential (localizedZeroMeasure hf s χ hχ hχc) z + H z)) :
    (fun z => (s : ℂ)⁻¹ * logDeriv f z) =ᵐ[volume.restrict (ball c r)]
      (fun z => cauchyTransform (localizedZeroMeasure hf s χ hχ hχc) z + classicalComplexGradient H z) := by
  have hsource := ((logNorm_hasWeakComplexGradient_on_ball hf hb hb0).restrict
    (ball_subset_ball hrR)).const_mul s⁻¹
  have hv := logPotential_hasWeakComplexGradient
    (localizedZeroMeasure hf s χ hχ hχc : Measure ℂ) hχc
    (localizedZeroMeasure_ae_mem hf s hχ hχc) (ball c r)
  have hh := contDiffOn_hasWeakComplexGradient isOpen_ball (hH.contDiffOn.of_le (by norm_num))
  have hright := (hv.add hh).congr_function_ae isOpen_ball heq.symm
  simpa only [Complex.real_smul, Complex.ofReal_inv, Pi.add_apply] using! hsource.unique isOpen_ball hright

theorem iterated_logDeriv_singular_ae {f : ℂ → ℂ} {c b : ℂ} {r R s : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : b ∈ ball c R) (hb0 : f b ≠ 0)
    (hrR : r ≤ R) (hs : 0 ≤ s) {χ : ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ a, 0 ≤ χ a)
    {H : ℂ → ℝ} (hH : HarmonicOnNhd H (ball c r))
    (heq : (fun z => s⁻¹ * Real.log ‖f z‖) =ᵐ[volume.restrict (ball c r)]
      (fun z => logPotential (localizedZeroMeasure hf s χ hχ hχc) z + H z)) (j : ℕ) :
    (fun z => (s : ℂ)⁻¹ * iteratedDeriv j (logDeriv f) z) =ᵐ[volume.restrict (ball c r)]
      (fun z => (-1 : ℂ) ^ j * (j.factorial : ℂ) * (s : ℂ)⁻¹ *
        (∑ a ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
          ((χ a : ℂ) * (divisor f (ball c R) a : ℂ)) / (z - a) ^ (j + 1)) +
        iteratedDeriv j (classicalComplexGradient H) z) := by
  classical
  let S := hf.meromorphicOn.divisor_ball_support_finite.toFinset
  let w (a : ℂ) : ℂ := (s : ℂ)⁻¹ * (χ a : ℂ) * (divisor f (ball c R) a : ℂ)
  let V := (ball c r ∩ f ⁻¹' ({0}ᶜ : Set ℂ)) ∩ (S : Set ℂ)ᶜ
  have hfU := hf.mono ((ball_subset_ball hrR).trans ball_subset_closedBall)
  have hV : IsOpen V :=
    (hfU.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).inter
      S.finite_toSet.isClosed.isOpen_compl
  have hVU : V ⊆ ball c r := fun _ hz => hz.1.1
  have hza {z : ℂ} (hz : z ∈ V) (a : ℂ) (ha : a ∈ S) : z ≠ a := by
    intro h
    exact hz.2 (h ▸ ha)
  have hleft : AnalyticOnNhd ℂ (fun z => (s : ℂ)⁻¹ * logDeriv f z) V := by
    intro z hz
    simp only [logDeriv_apply]
    exact analyticAt_const.mul ((hfU.deriv z hz.1.1).div (hfU z hz.1.1) hz.1.2)
  have hsum {z : ℂ} (hz : z ∈ V) : AnalyticAt ℂ (fun z => ∑ a ∈ S, w a * (z - a)⁻¹) z := by
    apply Finset.analyticAt_fun_sum
    intro a ha
    exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (hza hz a ha)))
  have hgrad := harmonic_complexGradient_analytic hH
  have hright : AnalyticOnNhd ℂ
      (fun z => (∑ a ∈ S, w a * (z - a)⁻¹) + classicalComplexGradient H z) V :=
    fun z hz => (hsum hz).add (hgrad z hz.1.1)
  have hAE := logDeriv_potential_harmonic_ae hf hb hb0 hrR hχ hχc hH heq
  have hAEV : (fun z => (s : ℂ)⁻¹ * logDeriv f z) =ᵐ[volume.restrict V]
      (fun z => (∑ a ∈ S, w a * (z - a)⁻¹) + classicalComplexGradient H z) := by
    have hrestrict := hAE.filter_mono (ae_mono (Measure.restrict_mono_set _ hVU))
    filter_upwards [hrestrict] with z hz
    simpa only [cauchyTransform_localizedZeroMeasure hf hs hχ hχc hχ0, S, w] using hz
  have hD := iteratedDeriv_eqOn_of_ae_eq hV hleft hright hAEV j
  have hfnz := (analytic_ae_ne_zero isOpen_ball (convex_ball c R).isPreconnected
    (hf.mono ball_subset_closedBall) ⟨b, hb, hb0⟩).filter_mono
      (ae_mono (Measure.restrict_mono_set _ (ball_subset_ball hrR)))
  have hnotS : ∀ᵐ z ∂volume.restrict (ball c r), z ∉ (S : Set ℂ) :=
    ae_restrict_of_ae (S.finite_toSet.countable.ae_notMem volume)
  filter_upwards [ae_restrict_mem measurableSet_ball, hfnz, hnotS] with z hz hzf hzS
  have hzV : z ∈ V := ⟨⟨hz, hzf⟩, hzS⟩
  have hdz := hD hzV
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add (hsum hzV).contDiffAt (hgrad z hz).contDiffAt] at hdz
  have hsumD : iteratedDeriv j (fun z => ∑ a ∈ S, w a * (z - a)⁻¹) z =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) * ∑ a ∈ S, w a / (z - a) ^ (j + 1) := by
    simpa only [id_eq] using! iteratedDeriv_finite_cauchy_sum S id w j (hza hzV)
  rw [hsumD] at hdz
  have hscale : (∑ a ∈ S, w a / (z - a) ^ (j + 1)) = (s : ℂ)⁻¹ *
      ∑ a ∈ S, ((χ a : ℂ) * (divisor f (ball c R) a : ℂ)) / (z - a) ^ (j + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [w]
    ring
  rw [hscale] at hdz
  simpa only [S, mul_assoc] using hdz

theorem normalized_iterated_logDeriv_singular_ae {f : ℂ → ℂ} {c b : ℂ} {r R s : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : b ∈ ball c R) (hb0 : f b ≠ 0)
    (hrR : r ≤ R) (hs : 0 ≤ s) {χ : ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ a, 0 ≤ χ a)
    {H : ℂ → ℝ} (hH : HarmonicOnNhd H (ball c r))
    (heq : (fun z => s⁻¹ * Real.log ‖f z‖) =ᵐ[volume.restrict (ball c r)]
      (fun z => logPotential (localizedZeroMeasure hf s χ hχ hχc) z + H z)) (j : ℕ) :
    (fun z => iteratedDeriv j (logDeriv f) z / (s : ℂ) ^ (j + 1)) =ᵐ[volume.restrict (ball c r)]
      (fun z => (-1 : ℂ) ^ j * (j.factorial : ℂ) *
        ((∑ a ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
          ((χ a : ℂ) * (divisor f (ball c R) a : ℂ)) / (z - a) ^ (j + 1)) / (s : ℂ) ^ (j + 1)) +
        iteratedDeriv j (classicalComplexGradient H) z / (s : ℂ) ^ j) := by
  filter_upwards [iterated_logDeriv_singular_ae hf hb hb0 hrR hs hχ hχc hχ0 hH heq j] with z hz
  calc
    _ = ((s : ℂ)⁻¹ * iteratedDeriv j (logDeriv f) z) / (s : ℂ) ^ j := by
      simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [hz]
      simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
      ring


end ModifiedCartan

