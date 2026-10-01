import ModifiedCartan.RescaledRepresentation
import ModifiedCartan.ReplacementTaylorData
import ModifiedCartan.ReplacementRootData
import ModifiedCartan.ReplacementCoefficientData
import ModifiedCartan.PolynomialApproximationLog

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Exact data of LaTeX `lem:replacement`. The polynomial P is the actual
Step 1 divisor polynomial; p is the actual Taylor vector. The representation
bounds are retained for these same gauges, for subsequent paper arguments. -/
structure PolynomialReplacementData {n : ℕ} (f : Curve n) (t s : ℕ → ℝ)
    (C A L : ℝ) (H : ℕ → ℂ → ℂ) (p : ℕ → Index n → Polynomial ℂ)
    (a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ)
    (η : ℕ → ℝ) : Prop where
  gauge_analytic : ∀ᶠ ν in atTop, AnalyticOnNhd ℂ (H ν) (ball 0 64)
  gauge_wronskian : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 64,
    FewInflection.wronskian n (rescaledRepresentation f (t ν) (H ν)) z =
      (rescaledWronskianPolynomial f (t ν)).eval z
  gauge_center : Tendsto (fun ν => (H ν 0).re / s ν) atTop (𝓝 0)
  coordinate_centers : ∀ j, Tendsto
    (fun ν => Real.log ‖rescaledRepresentation f (t ν) (H ν) j 0‖ / s ν) atTop (𝓝 0)
  gauge_norm : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 32,
    euclideanNorm (fun j => rescaledRepresentation f (t ν) (H ν) j z) ≤ Real.exp ((5 * C + 1) * s ν)
  mean_identity : ∃ c : ℕ → ℝ, Tendsto (fun ν => c ν / s ν) atTop (𝓝 0) ∧
    ∀ᶠ ν in atTop, ∀ R : ℝ, 0 < R → R < 64 →
      Real.circleAverage (fun z => Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (t ν) (H ν) j z))) 0 R =
          characteristic f (R * t ν) + c ν
  taylor : ∀ ν j, p ν j = FewInflection.taylorPolynomial
    (rescaledRepresentation f (t ν) (H ν) j) 0 (Nat.ceil (L * s ν))
  degree : ∀ᶠ ν in atTop, ∀ j, ((p ν j).natDegree : ℝ) ≤ (L + 1) * s ν
  wronskian_degree : ∀ᶠ ν in atTop,
    ((FewInflection.polynomialWronskian (p ν)).natDegree : ℝ) ≤ (n + 1) * (L + 1) * s ν
  wronskian_nonzero : ∀ᶠ ν in atTop, FewInflection.polynomialWronskian (p ν) ≠ 0
  jet_error : ∀ᶠ ν in atTop, ∀ j k, k ≤ n + 1 → ∀ z ∈ closedBall (0 : ℂ) 16,
    ‖iteratedDeriv k (fun w => (p ν j).eval w) z -
      iteratedDeriv k (rescaledRepresentation f (t ν) (H ν) j) z‖ ≤ Real.exp (-A * s ν)
  root_factorization : ∀ᶠ ν in atTop, normalize (FewInflection.polynomialWronskian (p ν)) =
    ∏ i, (Polynomial.X - Polynomial.C (a ν i))
  separating_radii : ∀ ν, 8 < η ν ∧ η ν < 10 ∧ (∀ i, ‖a ν i‖ ≠ η ν) ∧
    ∀ z, (rescaledWronskianPolynomial f (t ν)).eval z = 0 → ‖z‖ ≠ η ν
  inner_count : Tendsto (fun ν => (∑ᶠ z : ℂ, ((MeromorphicOn.divisor
    (fun w => (FewInflection.polynomialWronskian (p ν)).eval w) (ball 0 (η ν))) z : ℝ)) /
      s ν) atTop (𝓝 0)
  log_wronskian : LocalLpConvergence 1 (ball (0 : ℂ) 4)
    (fun ν z => Real.log ‖(FewInflection.polynomialWronskian (p ν)).eval z‖ / s ν) (fun _ => 0)
  inner_sum_lp : Tendsto (fun ν => eLpNorm
    (fun z => reciprocalDistanceSum (Finset.univ.filter (fun i => ‖a ν i‖ < η ν)) (a ν) z / s ν)
    (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (ball 0 6))) atTop (𝓝 0)
  inner_sum_measure : LocalMeasureConvergence (ball (0 : ℂ) 6)
    (fun ν z => reciprocalDistanceSum (Finset.univ.filter (fun i => ‖a ν i‖ < η ν)) (a ν) z / s ν)
    (fun _ => (0 : ℝ))
  outer_sum : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 6,
    reciprocalDistanceSum (Finset.univ.filter (fun i => η ν < ‖a ν i‖)) (a ν) z / s ν ≤
      ((n + 1) * (L + 1)) / 2
  first_coefficient : LocalMeasureConvergence (ball (0 : ℂ) 4)
    (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z (Fin.last n) /
      (s ν : ℂ)) (fun _ => 0)
  scaled_coefficients : ∀ i : Fin n, LocalMeasureConvergence (ball (0 : ℂ) 4)
    (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i.castSucc /
      (s ν : ℂ) ^ (n + 1 - i.val) -
        ((t ν / s ν : ℝ) : ℂ) ^ (n + 1 - i.val) *
          canonicalCoefficient n f.coord i.castSucc ((t ν : ℂ) * z)) (fun _ => 0)

/-- LaTeX `lem:replacement`, including `eq:replacement-data`,
`eq:rootbounds`, and `eq:polynomial-coefficients`. All data are constructed
from the manuscript's scale hypotheses, for every sufficiently large A. -/
theorem Paper.lem_replacement (n : ℕ) (C : ℝ) (_hC : 0 < C) :
    ∃ A0 : ℝ, 0 < A0 ∧ ∀ A : ℝ, A0 ≤ A → ∃ L : ℝ, 0 < L ∧
      ∀ (f : Curve n), f.linearlyNonDegenerate → (∀ j, f.coord j 0 ≠ 0) →
      ∀ (t s : ℕ → ℝ), Tendsto t atTop atTop → Tendsto s atTop atTop →
      Tendsto (fun ν => Real.log (t ν) / s ν) atTop (𝓝 0) →
      (∀ᶠ ν in atTop, characteristic f (256 * t ν) ≤ C * s ν) →
      Tendsto (fun ν => ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
        (0 : WithTop ℂ) (256 * t ν) / s ν) atTop (𝓝 0) →
      ∃ (H : ℕ → ℂ → ℂ) (p : ℕ → Index n → Polynomial ℂ)
        (a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ) (η : ℕ → ℝ),
        PolynomialReplacementData f t s C A L H p a η := by
  obtain ⟨A0, hA0, hTaylor⟩ := replacement_taylor_data n (5 * C + 1)
  refine ⟨A0, hA0, ?_⟩
  intro A hA
  obtain ⟨L, hL, hpoly⟩ := hTaylor A hA
  refine ⟨L, hL, ?_⟩
  intro f hlin hf0 t s ht hs hlog hT hN
  obtain ⟨H, c, hd, hm, hcenter, hcoord, hc⟩ :=
    representation_step_one f hlin hf0 ht hs hlog hN
  let P := fun ν => rescaledWronskianPolynomial f (t ν)
  let g := fun ν => rescaledRepresentation f (t ν) (H ν)
  have hP (ν : ℕ) : (P ν).Monic := rescaledWronskianPolynomial_monic f (t ν)
  have hroots (ν : ℕ) (z : ℂ) (hz : (P ν).eval z = 0) : ‖z‖ ≤ 64 := by
    have he := rescaledWronskianPolynomial_roots_mem f (t ν) hz
    exact (show ‖z‖ < 64 by simpa only [mem_ball, dist_zero_right] using he).le
  have hnorm := eq_representationbounds_norm f hs (P := P) (by
    filter_upwards [hd] with ν hν
    exact ⟨hν.1, hP ν, hν.2.1⟩) hT hcenter
  have hlocal : ∀ᶠ ν in atTop,
      (∀ j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) ∧
      (∀ z ∈ ball (0 : ℂ) 32, FewInflection.wronskian n (g ν) z = (P ν).eval z) ∧
      (∀ z ∈ ball (0 : ℂ) 32,
        euclideanNorm (fun j => g ν j z) ≤ Real.exp ((5 * C + 1) * s ν)) := by
    filter_upwards [hd, hnorm] with ν hν hnν
    refine ⟨fun j z hz => rescaledRepresentation_analyticAt f (t ν)
      (hν.1 z ((ball_subset_ball (by norm_num : (32 : ℝ) ≤ 64)) hz)) j, ?_, ?_⟩
    · intro z hz
      exact hν.2.1 z ((ball_subset_ball (by norm_num : (32 : ℝ) ≤ 64)) hz)
    · intro z hz
      exact hnν z (ball_subset_closedBall hz)
  obtain ⟨p, hpTaylor, hp, hcramer⟩ := hpoly g s P hs hP hm hlocal
  let R := fun ν => FewInflection.polynomialWronskian (p ν)
  have herr : ∀ᶠ ν in atTop, ∀ z ∈ closedBall (0 : ℂ) 12,
      ‖(R ν).eval z - (P ν).eval z‖ ≤ 1 / 2 := hp.mono (fun _ h => h.2.2.2.2)
  have hlogR := polynomial_approximation_log_localL1_zero P R hP hroots hs hm herr
  obtain ⟨a, η, hsep, hfac, hcount, hlp, hmeasure, hout⟩ :=
    replacement_root_data P R hP hs hm (hp.mono (fun _ h => ⟨h.2.2.1, h.2.1⟩)) herr
  have hcanonical := replacement_coefficient_canonical_comparison (5 * C + 1) g p s P hs hm (by
    filter_upwards [hlocal] with ν hν
    exact ⟨hν.1, hP ν, hν.2.1, hν.2.2⟩) hcramer
  refine ⟨H, p, a, η, {
    gauge_analytic := hd.mono (fun _ h => h.1)
    gauge_wronskian := hd.mono (fun _ h => h.2.1)
    gauge_center := hcenter
    coordinate_centers := hcoord
    gauge_norm := hlocal.mono (fun _ h => h.2.2)
    mean_identity := ⟨c, hc, hd.mono (fun _ h => h.2.2)⟩
    taylor := hpTaylor
    degree := hp.mono (fun _ h => h.1)
    wronskian_degree := hp.mono (fun _ h => h.2.1)
    wronskian_nonzero := hp.mono (fun _ h => h.2.2.1)
    jet_error := hp.mono (fun _ h => h.2.2.2.1)
    root_factorization := hfac
    separating_radii := hsep
    inner_count := hcount
    log_wronskian := hlogR
    inner_sum_lp := hlp
    inner_sum_measure := hmeasure
    outer_sum := hout
    first_coefficient := replacement_first_coefficient_small g p s
      (hlocal.mono (fun _ h => h.1)) (hcanonical (Fin.last n))
    scaled_coefficients := replacement_scaled_coefficient_comparison f p ht
      (hd.mono (fun _ h => h.1)) hcanonical
  }⟩

end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.lem_replacement
