import ModifiedCartan.HarmonicInterior

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! Arbitrary-order harmonic interior convergence for `lem:logderivlimit`.
Iterated convolution derivatives are handled by induction using the actual
currying isometries for continuous multilinear maps, then localized on disks. -/




theorem scalarConvolution_iteratedFDeriv_tendstoUniformly (m : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {k : ℂ → E}
    (hf : ∀ n, Integrable (f n)) (hg : Integrable g) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k)
    (hlim : Tendsto (fun n => ∫ a : ℂ, ‖f n a - g a‖) atTop (𝓝 0)) :
    TendstoUniformly (fun n => iteratedFDeriv ℝ m (scalarConvolution (f n) k))
      (iteratedFDeriv ℝ m (scalarConvolution g k)) atTop := by
  induction m generalizing E with
  | zero =>
    have ht := scalarConvolution_tendstoUniformly hf hg hk.continuous hkc hlim
    simpa only [iteratedFDeriv_zero_eq_comp] using
      (continuousMultilinearCurryFin0 ℝ ℂ E).symm.isometry.uniformContinuous.comp_tendstoUniformly ht
  | succ m ih =>
    have hdk : ContDiff ℝ ∞ (fderiv ℝ k) := (contDiff_infty_iff_fderiv.mp hk).2
    have ht := ih hdk (hkc.fderiv ℝ)
    have heq (v : ℂ → ℝ) (hv : Integrable v) :
        fderiv ℝ (scalarConvolution v k) = scalarConvolution v (fderiv ℝ k) :=
      funext fun z => scalarConvolution_fderiv hv.locallyIntegrable
        (hk.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hkc z
    have ht' := (continuousMultilinearCurryRightEquiv' ℝ m ℂ E).symm.isometry.uniformContinuous.comp_tendstoUniformly ht
    change TendstoUniformly (fun n z => iteratedFDeriv ℝ (m + 1) (scalarConvolution (f n) k) z)
      (fun z => iteratedFDeriv ℝ (m + 1) (scalarConvolution g k) z) atTop
    simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, heq _ hg, heq _ (hf _)] using ht'

theorem LocalLpConvergence.harmonic_iteratedFDeriv_on_interior
    {U K W : Set ℂ} {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {R : ℝ}
    (h : LocalLpConvergence 1 U f g) (hK : IsCompact K) (hKU : K ⊆ U)
    (hW : IsOpen W) (hR : 0 < R) (hball : ∀ x ∈ W, closedBall x (2 * R) ⊆ K)
    (hharm : ∀ n, HarmonicOnNhd (f n) U) (hgharm : HarmonicOnNhd g U) (m : ℕ) :
    TendstoUniformlyOn (fun n => iteratedFDeriv ℝ m (f n)) (iteratedFDeriv ℝ m g) atTop W := by
  have hF (n : ℕ) : Integrable (K.indicator (f n)) :=
    IntegrableOn.integrable_indicator
      (memLp_one_iff_integrable.mp (h.source_mem K hK hKU n)) hK.measurableSet
  have hG : Integrable (K.indicator g) :=
    IntegrableOn.integrable_indicator
      (memLp_one_iff_integrable.mp (h.limit_mem K hK hKU)) hK.measurableSet
  have ht := scalarConvolution_iteratedFDeriv_tendstoUniformly m hF hG
    (radialKernel_contDiff R) (radialKernel_hasCompactSupport hR)
    (h.indicator_integral_norm_sub_tendsto_zero hK hKU)
  have heq (v : ℂ → ℝ) (hv : HarmonicOnNhd v U) (z : ℂ) (hz : z ∈ W) :
      scalarConvolution (K.indicator v) (radialKernel R) =ᶠ[𝓝 z] v := by
    filter_upwards [hW.mem_nhds hz] with w hw
    exact scalarConvolution_indicator_radialKernel_eq hR (hv.mono hKU) (hball w hw)
  exact (ht.tendstoUniformlyOn.congr (Eventually.of_forall fun n z hz =>
    ((heq _ (hharm n) z hz).iteratedFDeriv ℝ m).eq_of_nhds)).congr_right
      (fun z hz => ((heq _ hgharm z hz).iteratedFDeriv ℝ m).eq_of_nhds)

theorem LocalLpConvergence.harmonic_iteratedFDeriv_on_ball
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {c : ℂ} {r R : ℝ} (hrR : r < R)
    (h : LocalLpConvergence 1 (ball c R) f g)
    (hharm : ∀ n, HarmonicOnNhd (f n) (ball c R)) (hgharm : HarmonicOnNhd g (ball c R))
    (m : ℕ) : TendstoUniformlyOn (fun n => iteratedFDeriv ℝ m (f n))
      (iteratedFDeriv ℝ m g) atTop (ball c r) := by
  let S := (r + R) / 2
  let ρ := (R - r) / 8
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hSR : S < R := by dsimp [S]; linarith
  apply h.harmonic_iteratedFDeriv_on_interior (isCompact_closedBall c S)
    (closedBall_subset_ball hSR) isOpen_ball hρ _ hharm hgharm m
  intro x hx z hz
  change dist z c ≤ S
  have hx' : dist x c < r := hx
  have hz' : dist z x ≤ 2 * ρ := hz
  have hdist := dist_triangle z x c
  dsimp [S, ρ] at *
  linarith

theorem LocalLpConvergence.harmonic_representative_all_derivatives_on_ball
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {c : ℂ} {r R : ℝ} (hrR : r < R)
    (h : LocalLpConvergence 1 (ball c R) f g)
    (hharm : ∀ n, HarmonicOnNhd (f n) (ball c R)) :
    ∃ H : ℂ → ℝ, ContDiff ℝ ∞ H ∧ HarmonicOnNhd H (ball c r) ∧
      g =ᵐ[volume.restrict (ball c r)] H ∧
      ∀ m : ℕ, TendstoUniformlyOn (fun n => iteratedFDeriv ℝ m (f n))
        (iteratedFDeriv ℝ m H) atTop (ball c r) := by
  let ρ := (r + R) / 2
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  obtain ⟨H, hHd, hHh, hAE, _, _, _⟩ := h.harmonic_representative_on_ball hρR hharm
  have hρ := h.restrict (ball_subset_ball hρR.le)
  have hlim : LocalLpConvergence 1 (ball c ρ) f H :=
    hρ.congr_ae (fun _ => EventuallyEq.rfl) hAE
  refine ⟨H, hHd, hHh.mono (ball_subset_ball hrρ.le),
    hAE.filter_mono (ae_mono (Measure.restrict_mono_set _ (ball_subset_ball hrρ.le))), ?_⟩
  intro m
  exact hlim.harmonic_iteratedFDeriv_on_ball hrρ
    (fun n => (hharm n).mono (ball_subset_ball hρR.le)) hHh m




end ModifiedCartan


