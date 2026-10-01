import ModifiedCartan.HarmonicSmoothing
import ModifiedCartan.LocalConvergenceAlgebra
import ModifiedCartan.LocalSubsequence

open scoped Topology ENNReal ContDiff Convolution
open Filter MeasureTheory Set Metric InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! Local harmonic representatives and interior derivative convergence for
`lem:logderivlimit`. Cut off on a compact set, convolve with the explicit radial
kernel, and pass to limits in the function, its derivatives, and Laplacian.
An AE subsequence identifies the smooth representative with the original L1
limit. The disk theorem derives the required buffer geometry from r < R. -/

theorem scalarConvolution_indicator_radialKernel_eq {H : ℂ → ℝ} {K : Set ℂ} {x : ℂ} {R : ℝ}
    (hR : 0 < R) (hH : HarmonicOnNhd H K) (hball : closedBall x (2 * R) ⊆ K) :
    scalarConvolution (K.indicator H) (radialKernel R) x = H x := by
  calc
    _ = scalarConvolution H (radialKernel R) x := by
      unfold scalarConvolution
      rw [convolution_eq_swap, convolution_eq_swap]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      change K.indicator H (x - z) * radialKernel R z = H (x - z) * radialKernel R z
      by_cases hz : radialKernel R z = 0
      · simp only [hz, mul_zero]
      · have hnorm : ‖z‖ ≤ 2 * R := by
          simpa only [mem_closedBall, dist_zero_right] using
            radialKernel_tsupport hR (subset_closure hz)
        have hxz : x - z ∈ K := hball (by
          rw [mem_closedBall, dist_eq_norm, show (x - z) - x = -z by abel, norm_neg]
          exact hnorm)
        rw [indicator_of_mem hxz]
    _ = H x := scalarConvolution_radialKernel_eq hR (hH.mono hball)

theorem LocalLpConvergence.indicator_integral_norm_sub_tendsto_zero
    {U K : Set ℂ} {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    (h : LocalLpConvergence 1 U f g) (hK : IsCompact K) (hKU : K ⊆ U) :
    Tendsto (fun n => ∫ z : ℂ, ‖K.indicator (f n) z - K.indicator g z‖) atTop (𝓝 0) := by
  have heq (n : ℕ) : (fun z => ‖K.indicator (f n) z - K.indicator g z‖) =
      K.indicator (fun z => ‖f n z - g z‖) := by
    funext z
    by_cases hz : z ∈ K
    · simp only [indicator_of_mem hz]
    · simp only [indicator_of_notMem hz, sub_self, norm_zero]
  simpa only [heq, integral_indicator hK.measurableSet] using
    h.integral_norm_sub_tendsto_zero hK hKU

theorem LocalLpConvergence.harmonic_representative_on_interior
    {U K W : Set ℂ} {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {R : ℝ}
    (h : LocalLpConvergence 1 U f g) (hK : IsCompact K) (hKU : K ⊆ U)
    (hW : IsOpen W) (hR : 0 < R) (hball : ∀ x ∈ W, closedBall x (2 * R) ⊆ K)
    (hharm : ∀ n, HarmonicOnNhd (f n) U) :
    ∃ H : ℂ → ℝ, ContDiff ℝ ∞ H ∧ HarmonicOnNhd H W ∧
      g =ᵐ[volume.restrict W] H ∧
      TendstoUniformlyOn f H atTop W ∧
      TendstoUniformlyOn (fun n => fderiv ℝ (f n)) (fderiv ℝ H) atTop W ∧
      TendstoUniformlyOn (fun n => fderiv ℝ (fderiv ℝ (f n)))
        (fderiv ℝ (fderiv ℝ H)) atTop W := by
  let F (n : ℕ) := K.indicator (f n)
  let G := K.indicator g
  let H := scalarConvolution G (radialKernel R)
  let Hn (n : ℕ) := scalarConvolution (F n) (radialKernel R)
  have hF (n : ℕ) : Integrable (F n) :=
    IntegrableOn.integrable_indicator
      (memLp_one_iff_integrable.mp (h.source_mem K hK hKU n)) hK.measurableSet
  have hG : Integrable G :=
    IntegrableOn.integrable_indicator
      (memLp_one_iff_integrable.mp (h.limit_mem K hK hKU)) hK.measurableSet
  have hlim : Tendsto (fun n => ∫ z : ℂ, ‖F n z - G z‖) atTop (𝓝 0) :=
    h.indicator_integral_norm_sub_tendsto_zero hK hKU
  have hkc := radialKernel_hasCompactSupport hR
  have hkd := radialKernel_contDiff R
  have hconv := scalarConvolution_tendstoUniformly hF hG hkd.continuous hkc hlim
  have hconv₁ := scalarConvolution_fderiv_tendstoUniformly hF hG hkd hkc hlim
  have hconv₂ := scalarConvolution_second_fderiv_tendstoUniformly hF hG hkd hkc hlim
  have heq (n : ℕ) (z : ℂ) (hz : z ∈ W) : Hn n z = f n z :=
    scalarConvolution_indicator_radialKernel_eq hR ((hharm n).mono hKU) (hball z hz)
  have heqNhd (n : ℕ) (z : ℂ) (hz : z ∈ W) : Hn n =ᶠ[𝓝 z] f n := by
    filter_upwards [hW.mem_nhds hz] with w hw
    exact heq n w hw
  have hUnif : TendstoUniformlyOn f H atTop W := by
    exact hconv.tendstoUniformlyOn.congr (Eventually.of_forall fun n z hz => heq n z hz)
  have hSmooth : ContDiff ℝ ∞ H := scalarConvolution_contDiff hG.locallyIntegrable hkd hkc
  have hWU : W ⊆ U := fun z hz => hKU (hball z hz (mem_closedBall_self (by linarith)))
  have hLap (z : ℂ) (hz : z ∈ W) : Laplacian.laplacian H z = 0 := by
    have ht := scalarConvolution_laplacian_tendsto hF hG hkd hkc hlim z
    have hzero (n : ℕ) : Laplacian.laplacian (Hn n) z = 0 := by
      rw [(laplacian_congr_nhds (heqNhd n z hz)).eq_of_nhds]
      exact ((hharm n) z (hWU hz)).2.eq_of_nhds
    apply tendsto_nhds_unique ht
    change Tendsto (fun n => Laplacian.laplacian (Hn n) z) atTop (𝓝 0)
    simp_rw [hzero]
    exact tendsto_const_nhds
  have hHarm : HarmonicOnNhd H W := by
    have h2 : ContDiff ℝ 2 H :=
      hSmooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    intro z hz
    refine ⟨h2.contDiffAt, ?_⟩
    filter_upwards [hW.mem_nhds hz] with w hw
    exact hLap w hw
  have hAE : g =ᵐ[volume.restrict W] H := by
    obtain ⟨ns, hns, hnsLim⟩ := (h.restrict hWU).exists_seq_tendsto_ae (by simp) hW
    filter_upwards [hnsLim, ae_restrict_mem hW.measurableSet] with z hz hzW
    exact tendsto_nhds_unique hz ((hUnif.tendsto_at hzW).comp hns.tendsto_atTop)
  refine ⟨H, hSmooth, hHarm, hAE, hUnif, ?_, ?_⟩
  · exact hconv₁.tendstoUniformlyOn.congr
      (Eventually.of_forall fun n z hz => (heqNhd n z hz).fderiv_eq)
  · exact hconv₂.tendstoUniformlyOn.congr
      (Eventually.of_forall fun n z hz => (heqNhd n z hz).fderiv.fderiv_eq)


theorem LocalLpConvergence.harmonic_representative_on_ball
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {c : ℂ} {r R : ℝ} (hrR : r < R)
    (h : LocalLpConvergence 1 (ball c R) f g)
    (hharm : ∀ n, HarmonicOnNhd (f n) (ball c R)) :
    ∃ H : ℂ → ℝ, ContDiff ℝ ∞ H ∧ HarmonicOnNhd H (ball c r) ∧
      g =ᵐ[volume.restrict (ball c r)] H ∧
      TendstoUniformlyOn f H atTop (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℝ (f n)) (fderiv ℝ H) atTop (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℝ (fderiv ℝ (f n)))
        (fderiv ℝ (fderiv ℝ H)) atTop (ball c r) := by
  let S := (r + R) / 2
  let ρ := (R - r) / 8
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hSR : S < R := by dsimp [S]; linarith
  apply h.harmonic_representative_on_interior (isCompact_closedBall c S)
    (closedBall_subset_ball hSR) isOpen_ball hρ _ hharm
  intro x hx z hz
  change dist z c ≤ S
  have hx' : dist x c < r := hx
  have hz' : dist z x ≤ 2 * ρ := hz
  have hdist := dist_triangle z x c
  dsimp [S, ρ] at *
  linarith


end ModifiedCartan
