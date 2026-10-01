import ModifiedCartan.RescaledZeroCoefficients
import ModifiedCartan.NormalizedFundamentalODE
import ModifiedCartan.WeakGradientConstancy
import ModifiedCartan.FiniteLogCompactness
import ModifiedCartan.PeakConstantSign
import ModifiedCartan.RepresentationMeanContradiction
import ModifiedCartan.CurveCoordinateNormalization

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Nonvanishing in Step 2 of `prop:indices` after the proved constant
coordinate normalization. The local mean/upper-bound alternative to the
manuscript's norm-log annular argument is recorded in FORMALIZATION_MAP.md. -/
theorem peak_zero_limits_impossible_normalized {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hf0 : ∀ j, f.coord j 0 ≠ 0)
    {r ε : ℕ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hrpos : ∀ ν, 0 < r ν) (hr : Tendsto r atTop atTop)
    (hεpos : ∀ ν, 0 < ε ν) (hε : Tendsto ε atTop (𝓝 0))
    (hpeak : ∀ ν t, ε ν ≤ t → t ≤ (ε ν)⁻¹ →
      characteristic f (t * r ν) ≤ (1 + ε ν) * t ^ μ * characteristic f (r ν))
    (hscaled : ∀ i : Fin n, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => ((r ν / characteristic f (r ν) : ℝ) : ℂ) ^ (n + 1 - i.val) *
        canonicalCoefficient n f.coord i.castSucc ((r ν : ℂ) * z)) (fun _ => 0)) : False := by
  obtain ⟨ht, hs, hlog, hT, hN⟩ := characteristic_peak_scale_hypotheses f htrans hsmall
    hμ hrpos hr hεpos hε hpeak (R := 1) zero_lt_one
  simp only [one_mul, Real.one_rpow] at ht hs hlog hT hN
  obtain ⟨_, _, hrep⟩ := Paper.prop_representation n (2 * (256 : ℝ) ^ μ) (by positivity)
  obtain ⟨H, P, c, hd, hm, hcenter, hc, _⟩ := hrep f hlin hf0 r
    (fun ν => characteristic f (r ν)) ht hs hlog hT hN
  let F := fun ν => rescaledRepresentation f (r ν) (H ν)
  have hF0 (ν : ℕ) (j : Index n) : F ν j 0 ≠ 0 := by
    simpa only [F, rescaledRepresentation, mul_zero] using mul_ne_zero (Complex.exp_ne_zero _) (hf0 j)
  have hcompactData : ∀ᶠ ν in atTop, ∀ j, AnalyticOnNhd ℂ (F ν j) (ball 0 4) ∧
      F ν j 0 ≠ 0 ∧ ∀ z ∈ ball (0 : ℂ) 4,
        ‖F ν j z‖ ≤ Real.exp ((5 * (2 * (256 : ℝ) ^ μ) + 1) * characteristic f (r ν)) := by
    filter_upwards [hd] with ν hν j
    rcases hν with ⟨hH, _, _, _, hb, _⟩
    refine ⟨fun z hz => rescaledRepresentation_analyticAt f (r ν)
      (hH z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) hz)) j, hF0 ν j, ?_⟩
    intro z hz
    exact (norm_le_pi_norm (fun k => F ν k z) j).trans ((norm_le_euclideanNorm _).trans
      (hb z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 32)) hz)))
  have hcoeff := rescaled_fundamental_coefficients_zero f ht hs hm (by
    filter_upwards [hd] with ν hν
    rcases hν with ⟨hH, hP, _, hW, hb, _⟩
    exact ⟨hH, hP, fun z hz => hW z ((ball_subset_ball (by norm_num : (32 : ℝ) ≤ 64)) hz), hb⟩) hscaled
  have hW : ∀ᶠ ν in atTop, ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4),
      FewInflection.wronskian n (F ν) z ≠ 0 :=
    eventually_wronskian_ae_ne_zero_of_monic measurableSet_ball (P := P) (by
      filter_upwards [hd] with ν hν
      rcases hν with ⟨_, hP, _, hW, _, _⟩
      exact ⟨hP, fun z hz => hW z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) hz)⟩)
  obtain ⟨ρ, hρ, hret, u, hu⟩ := exists_common_normalized_log_subsequence_eventual hs hcompactData hcenter
  have hFρ (ν : ℕ) (j : Index n) : AnalyticOnNhd ℂ (F (ρ ν) j) (ball 0 4) :=
    ((hret ν).2 j).1
  have hne (j : Index n) (ν : ℕ) : ∃ z ∈ ball (0 : ℂ) 4, F (ρ ν) j z ≠ 0 :=
    ⟨0, mem_ball_self (by norm_num), hF0 (ρ ν) j⟩
  have hconstants (j : Index n) : ∃ a : ℝ, LocalLpConvergence 1 (ball (0 : ℂ) 3)
      (fun ν z => (characteristic f (r (ρ ν)))⁻¹ * Real.log ‖F (ρ ν) j z‖) (fun _ => a) := by
    obtain ⟨v, hv, _⟩ := (hu j).log_limit_weak_gradient isOpen_ball
      (convex_ball (0 : ℂ) 4).isPreconnected (fun ν => hFρ ν j) (hne j) (hs.comp hρ.tendsto_atTop)
    have hv0 := normalized_ode_weak_gradient_zero isOpen_ball (convex_ball (0 : ℂ) 4).isPreconnected
      hFρ (hρ.tendsto_atTop.eventually hW) (hs.comp hρ.tendsto_atTop) j (hne j)
      (hu j) hv (fun i => (hcoeff i).comp hρ.tendsto_atTop)
    obtain ⟨a, ha⟩ := hv.exists_ae_const_of_gradient_ae_zero hv0
    exact ⟨a, ((hu j).restrict (ball_subset_ball (by norm_num : (3 : ℝ) ≤ 4))).congr_ae
      (fun _ => EventuallyEq.rfl) ha⟩
  choose a ha using hconstants
  have hd3 : ∀ᶠ ν in atTop, AnalyticOnNhd ℂ (H (ρ ν)) (ball 0 3) ∧
      ∀ R, 0 < R → R < 3 → Real.circleAverage
        (fun z => Real.log (euclideanNorm (fun j => F (ρ ν) j z))) 0 R =
          characteristic f (R * r (ρ ν)) + c (ρ ν) := by
    filter_upwards [hρ.tendsto_atTop.eventually hd] with ν hν
    rcases hν with ⟨hH, _, _, _, _, hmean⟩
    exact ⟨hH.mono (ball_subset_ball (by norm_num : (3 : ℝ) ≤ 64)),
      fun R hR hR3 => hmean R hR (hR3.trans (by norm_num : (3 : ℝ) < 64))⟩
  have hasign (j : Index n) : a j ≤ 0 :=
    peak_coordinate_constant_nonpos f htrans hf0 hμ (fun ν => hrpos (ρ ν))
      (fun ν => hεpos (ρ ν)) (hε.comp hρ.tendsto_atTop) (fun ν => hpeak (ρ ν))
      hd3 (hc.comp hρ.tendsto_atTop) j (ha j)
  apply representation_mean_contradicts_nonpositive_constants f htrans hf0
    (fun ν => hrpos (ρ ν)) (hs.comp hρ.tendsto_atTop)
    (fun ν j => (hFρ ν j).mono (ball_subset_ball (by norm_num : (3 : ℝ) ≤ 4))) ha hasign _
    (hc.comp hρ.tendsto_atTop)
  filter_upwards [hd3] with ν hν
  exact ⟨hν.1, by simpa only [one_mul] using hν.2 1 zero_lt_one (by norm_num)⟩

/-- Nonvanishing for every original curve and actual positive-order peak
sequence. No origin-coordinate normalization is assumed in the statement. -/
theorem peak_zero_limits_impossible {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {r ε : ℕ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hrpos : ∀ ν, 0 < r ν) (hr : Tendsto r atTop atTop)
    (hεpos : ∀ ν, 0 < ε ν) (hε : Tendsto ε atTop (𝓝 0))
    (hpeak : ∀ ν t, ε ν ≤ t → t ≤ (ε ν)⁻¹ →
      characteristic f (t * r ν) ≤ (1 + ε ν) * t ^ μ * characteristic f (r ν)) :
    ¬ (∀ i : Fin n, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => ((r ν / characteristic f (r ν) : ℝ) : ℂ) ^ (n + 1 - i.val) *
        canonicalCoefficient n f.coord i.castSucc ((r ν : ℂ) * z)) (fun _ => 0)) := by
  intro hzero
  obtain ⟨g, hg0, hgT, _, hgQ, hglin, hgtrans, hgsmall, _⟩ := exists_normalized_curve f
  apply peak_zero_limits_impossible_normalized g (hglin.mpr hlin) (hgtrans.mpr htrans)
    (hgsmall.mpr hsmall) hg0 hμ hrpos hr hεpos hε
  · simpa only [hgT] using hpeak
  · simpa only [hgT, hgQ] using hzero

/-- Some coefficient limit on D4 is nonzero, the precise nonvanishing
conclusion needed for the local Cauchy quantization proof of `prop:indices`. -/
theorem peak_coefficient_limit_nonzero {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {r ε : ℕ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hrpos : ∀ ν, 0 < r ν) (hr : Tendsto r atTop atTop)
    (hεpos : ∀ ν, 0 < ε ν) (hε : Tendsto ε atTop (𝓝 0))
    (hpeak : ∀ ν t, ε ν ≤ t → t ≤ (ε ν)⁻¹ →
      characteristic f (t * r ν) ≤ (1 + ε ν) * t ^ μ * characteristic f (r ν))
    {a : Fin n → ℂ → ℂ} (ha : ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => ((r ν / characteristic f (r ν) : ℝ) : ℂ) ^ (n + 1 - i.val) *
        canonicalCoefficient n f.coord i.castSucc ((r ν : ℂ) * z)) (a i)) :
    ∃ i : Fin n, ∃ z ∈ ball (0 : ℂ) 4, a i z ≠ 0 := by
  by_contra h
  push_neg at h
  apply peak_zero_limits_impossible f hlin htrans hsmall hμ hrpos hr hεpos hε hpeak
  intro i
  apply (ha i).congr_limit_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact h i z hz

end ModifiedCartan
#print axioms ModifiedCartan.peak_coefficient_limit_nonzero
