import ModifiedCartan.SingularLogDerivative
import ModifiedCartan.MeasureConvergenceLocality
import ModifiedCartan.FractionalConvergence
import ModifiedCartan.ZeroFractionalMass
import ModifiedCartan.LogLimitRepresentation

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric MeromorphicOn InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! The higher logarithmic derivative tends to zero on a further subsequence,
LaTeX label `eq:higher-logderiv-measure`. All singular weights and harmonic
remainders are obtained from the actual analytic functions. -/

theorem exists_fractional_pole_exponent {q : ℕ} (hq : 2 ≤ q) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ 1 < (q : ℝ) * α ∧ (q : ℝ) * α < 2 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have heq : (q : ℝ) * (3 / (2 * (q : ℝ))) = 3 / 2 := by field_simp
  refine ⟨3 / (2 * (q : ℝ)), by positivity, ?_, ?_, ?_⟩
  · apply (div_le_one (by positivity : 0 < 2 * (q : ℝ))).mpr
    linarith
  · rw [heq]; norm_num
  · rw [heq]; norm_num

theorem LocalLpConvergence.higher_logDeriv_subseq_on_ball
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {c : ℂ} {r R : ℝ}
    (hu : LocalLpConvergence 1 (ball c R) (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0)
    (hs0 : ∀ n, 0 < s n) (hs : Tendsto s atTop atTop)
    (hr : 0 < r) (hrR : r < R) {j : ℕ} (hj : 0 < j) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ LocalMeasureConvergence (ball c r)
      (fun n z => iteratedDeriv j (logDeriv (f (ns n))) z / (s (ns n) : ℂ) ^ (j + 1)) (fun _ => 0) := by
  classical
  let ρ := (2 * r + R) / 3
  let η := (r + 2 * R) / 3
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρη : ρ < η := by dsimp [ρ, η]; linarith
  have hηR : η < R := by dsimp [η]; linarith
  have hρR : ρ ≤ R := (hρη.trans hηR).le
  obtain ⟨χ, hχ, hχc, hχη, hχbound, hχone⟩ := exists_smooth_disk_cutoff c hρ hρη
  obtain ⟨ξ, hξ, hξc, hξR, hξbound, hξone⟩ := exists_smooth_disk_cutoff c (hρ.trans hρη) hηR
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hξ2 : ContDiff ℝ 2 ξ := hξ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hχR : tsupport χ ⊆ ball c R := hχη.trans (ball_subset_ball hηR.le)
  have hξχ (a : ℂ) (ha : χ a ≠ 0) : ξ a = 1 :=
    hξone a (ball_subset_closedBall (hχη (subset_closure ha)))
  obtain ⟨M, _, hM⟩ := hu.zero_fractional_mass_bounded (Subset.refl _) hf hnonzero hs0
    hχbound hξ2 hξc hξR (fun a => (hξbound a).1) hξχ
  obtain ⟨ν₀, ns, Hn, H, hns, _, _, hHn, heq, _, _, _, _, hD, _⟩ :=
    hu.log_limit_representation_on_ball hf hnonzero (fun n => (hs0 n).le) hrρ hρR hχ2 hχc hχR
      (fun a => (hχbound a).1) (fun a ha => hχone a (ball_subset_closedBall ha))
  obtain ⟨α, hα, hα1, hqα, hqα2⟩ := exists_fractional_pole_exponent (q := j + 1) (by omega)
  let S (n : ℕ) := (hf (ns n)).meromorphicOn.divisor_ball_support_finite.toFinset
  let w (n : ℕ) (a : ℂ) : ℂ := (χ a : ℂ) * (divisor (f (ns n)) (ball c R) a : ℂ)
  let P (n : ℕ) (z : ℂ) : ℂ :=
    (∑ a ∈ S n, w n a / (z - a) ^ (j + 1)) / (s (ns n) : ℂ) ^ (j + 1)
  let G (n : ℕ) := iteratedDeriv j (classicalComplexGradient (Hn n))
  have hGn (n : ℕ) : AnalyticOnNhd ℂ (G n) (ball c r) :=
    analyticOnNhd_iteratedDeriv (harmonic_complexGradient_analytic
      ((hHn n).mono (ball_subset_ball hrρ.le))) j
  have hGloc := harmonicGradient_iteratedDeriv_tendsto isOpen_ball
    (fun n => (hHn n).mono (ball_subset_ball hrρ.le)) hD j
  have hnormw (n : ℕ) (a : ℂ) :
      ‖w n a‖ = χ a * (divisor (f (ns n)) (ball c R) a : ℝ) := by
    have hm : (0 : ℝ) ≤ (divisor (f (ns n)) (ball c R) a : ℝ) := by
      exact_mod_cast ((hf (ns n)).mono ball_subset_closedBall).divisor_nonneg a
    dsimp [w]
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχbound a).1 hm)]
  refine ⟨ns, hns, ?_⟩
  intro K hK hKU
  have hKR (n : ℕ) (a : ℂ) (ha : a ∈ S n) : K ⊆ ball a (2 * R) := by
    have haR : a ∈ ball c R :=
      (divisor (f (ns n)) (ball c R)).supportWithinDomain
        ((hf (ns n)).meromorphicOn.divisor_ball_support_finite.mem_toFinset.mp ha)
    intro z hz
    have hzR := hKU hz
    rw [mem_ball] at haR hzR ⊢
    have htri := dist_triangle z c a
    rw [dist_comm c a] at htri
    linarith
  have hmass (n : ℕ) : ∑ a ∈ S n, ‖w n a‖ ^ α ≤ s (ns n) * M := by
    simpa only [hnormw, S] using hM (ns n) α hα hα1
  have hP : TendstoInMeasure (volume.restrict K) P atTop (fun _ => 0) :=
    normalized_weighted_poles_tendstoInMeasure S (fun _ a => a) w hK (by linarith) hα hα1 hqα hqα2
      (fun n => hs0 (ns n)) (hs.comp hns.tendsto_atTop) hKR hmass
  have hPmeas (n : ℕ) : AEStronglyMeasurable (P n) (volume.restrict K) := by
    have hm : Measurable (fun z => ∑ a ∈ S n, w n a / (z - a) ^ (j + 1)) := by
      apply Finset.measurable_fun_sum
      intro a _
      fun_prop
    exact (hm.div measurable_const).aestronglyMeasurable
  have hGunif : TendstoUniformlyOn G (iteratedDeriv j (classicalComplexGradient H)) atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hGloc K hKU hK
  have hG := uniform_diverging_scale_tendstoInMeasure hK
    (fun n => (hGn n).continuousOn.mono hKU) hGunif (hs.comp hns.tendsto_atTop) hj
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  have hboth := tendstoInMeasure_continuous_map₂ hPmeas
    (fun n => (((hGn n).continuousOn.mono hKU).div_const _).aestronglyMeasurable hK.measurableSet)
    hP hG (Φ := fun x : ℂ × ℂ => ((-1 : ℂ) ^ j * (j.factorial : ℂ)) * x.1 + x.2) (by fun_prop)
  have hfinal : TendstoInMeasure (volume.restrict K)
      (fun n z => ((-1 : ℂ) ^ j * (j.factorial : ℂ)) * P n z + G n z / (s (ns n) : ℂ) ^ j)
      atTop (fun _ => 0) := by simpa only [mul_zero, add_zero, Function.comp_def] using! hboth
  apply hfinal.congr_left
  intro n
  obtain ⟨b, hb, hb0⟩ := hnonzero (ns n)
  have heqD := normalized_iterated_logDeriv_singular_ae (hf (ns n)) hb hb0 hρR
    (hs0 (ns n)).le hχ2.continuous hχc (fun a => (hχbound a).1) (hHn n) (heq n) j
  exact heqD.symm.filter_mono
    (ae_mono (Measure.restrict_mono_set _ (hKU.trans (ball_subset_ball hrρ.le))))


end ModifiedCartan

