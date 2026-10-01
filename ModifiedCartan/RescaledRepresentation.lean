import ModifiedCartan.RepresentationBound
import ModifiedCartan.CanonicalCompactness

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section
namespace Paper

/-- LaTeX `prop:representation`, all conclusions, including
`eq:representationbounds`, `eq:meanidentity`, and `eq:scaledcompact`.
The constants depend only on dimension and C. The monic polynomial is the
actual dilated Wronskian divisor polynomial, and H is the Step 1 gauge. -/
theorem prop_representation (n : ℕ) (C : ℝ) (_hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : Curve n),
      f.linearlyNonDegenerate → (∀ j, f.coord j 0 ≠ 0) →
      ∀ (t s : ℕ → ℝ), Tendsto t atTop atTop → Tendsto s atTop atTop →
      Tendsto (fun ν => Real.log (t ν) / s ν) atTop (𝓝 0) →
      (∀ᶠ ν in atTop, characteristic f (256 * t ν) ≤ C * s ν) →
      Tendsto (fun ν => ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
        (0 : WithTop ℂ) (256 * t ν) / s ν) atTop (𝓝 0) →
      ∃ (H : ℕ → ℂ → ℂ) (P : ℕ → Polynomial ℂ) (c : ℕ → ℝ),
        (∀ᶠ ν in atTop,
          AnalyticOnNhd ℂ (H ν) (ball 0 64) ∧ (P ν).Monic ∧
          (∀ z, (P ν).eval z = 0 → z ∈ ball (0 : ℂ) 64) ∧
          (∀ z ∈ ball (0 : ℂ) 64,
            FewInflection.wronskian n (rescaledRepresentation f (t ν) (H ν)) z = (P ν).eval z) ∧
          (∀ z ∈ ball (0 : ℂ) 32,
            euclideanNorm (fun j => rescaledRepresentation f (t ν) (H ν) j z) ≤
              Real.exp ((5 * C + 1) * s ν)) ∧
          (∀ R : ℝ, 0 < R → R < 64 →
            Real.circleAverage (fun z => Real.log (euclideanNorm
              (fun j => rescaledRepresentation f (t ν) (H ν) j z))) 0 R =
                characteristic f (R * t ν) + c ν)) ∧
        Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0) ∧
        (∀ j, Tendsto (fun ν => Real.log ‖rescaledRepresentation f (t ν) (H ν) j 0‖ / s ν)
          atTop (𝓝 0)) ∧
        Tendsto (fun ν => c ν / s ν) atTop (𝓝 0) ∧
        (∀ ρ : ℕ → ℕ, StrictMono ρ →
          ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b : Fin n → ℂ → ℂ,
            ∀ i, AnalyticOnNhd ℂ (b i) (ball 0 4) ∧
              LocalMeasureConvergence (ball (0 : ℂ) 4)
                (fun ν z => (((t (ρ (σ ν)) / s (ρ (σ ν))) : ℝ) : ℂ) ^ (n + 1 - i.val) *
                  canonicalCoefficient n f.coord i.castSucc ((t (ρ (σ ν)) : ℂ) * z)) (b i) ∧
              ∀ z ∈ ball (0 : ℂ) 1, ‖b i z‖ ≤ K) := by
  obtain ⟨K, hK, hcompact⟩ := canonical_coefficient_relative_compactness_eventual n (5 * C + 1)
  refine ⟨K, hK, ?_⟩
  intro f hlin hf0 t s ht hs hlog hT hN
  obtain ⟨H, c, hd, hm, hcenter, hcoord, hc⟩ := representation_step_one f hlin hf0 ht hs hlog hN
  let P := fun ν => rescaledWronskianPolynomial f (t ν)
  let g := fun ν => rescaledRepresentation f (t ν) (H ν)
  have hnorm := eq_representationbounds_norm f hs (P := P) (by
    filter_upwards [hd] with ν hν
    exact ⟨hν.1, rescaledWronskianPolynomial_monic f (t ν), hν.2.1⟩) hT hcenter
  have hd32 : ∀ᶠ ν in atTop,
      (∀ j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) ∧ (P ν).Monic ∧
      (∀ z ∈ ball (0 : ℂ) 32, FewInflection.wronskian n (g ν) z = (P ν).eval z) ∧
      (∀ z ∈ ball (0 : ℂ) 32, euclideanNorm (fun j => g ν j z) ≤ Real.exp ((5 * C + 1) * s ν)) := by
    filter_upwards [hd, hnorm] with ν hν hnν
    refine ⟨fun j z hz => rescaledRepresentation_analyticAt f (t ν)
      (hν.1 z ((ball_subset_ball (by norm_num : (32 : ℝ) ≤ 64)) hz)) j,
      rescaledWronskianPolynomial_monic f (t ν), ?_, ?_⟩
    · intro z hz
      exact hν.2.1 z ((ball_subset_ball (by norm_num : (32 : ℝ) ≤ 64)) hz)
    · intro z hz
      exact hnν z (ball_subset_closedBall hz)
  refine ⟨H, P, c, ?_, hm, hcoord, hc, ?_⟩
  · filter_upwards [hd, hnorm] with ν hν hnν
    exact ⟨hν.1, rescaledWronskianPolynomial_monic f (t ν),
      fun _ hz => rescaledWronskianPolynomial_roots_mem f (t ν) hz,
      hν.2.1, fun z hz => hnν z (ball_subset_closedBall hz), hν.2.2⟩
  · intro ρ hρ
    obtain ⟨σ, hσ, b, hb⟩ := hcompact g s P hs hm hd32 ρ hρ
    refine ⟨σ, hσ, fun i => b i.castSucc, ?_⟩
    intro i
    refine ⟨(hb i.castSucc).1, ?_, (hb i.castSucc).2.2⟩
    intro S hS hSU
    apply ((hb i.castSucc).2.1 S hS hSU).congr' _ EventuallyEq.rfl
    have hindices : Tendsto (fun ν => ρ (σ ν)) atTop atTop :=
      hρ.tendsto_atTop.comp hσ.tendsto_atTop
    filter_upwards [hindices.eventually hd,
      (ht.comp hindices).eventually_gt_atTop 0] with ν hν htν
    change 0 < t (ρ (σ ν)) at htν
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hzS
    have hz64 : z ∈ ball (0 : ℂ) 64 :=
      (ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) (hSU hzS)
    change canonicalCoefficient n (rescaledRepresentation f (t (ρ (σ ν))) (H (ρ (σ ν))))
      i.castSucc z / (s (ρ (σ ν)) : ℂ) ^ (n + 1 - i.castSucc.val) = _
    rw [eq_canonical_coefficient_identification f htν (hν.1 z hz64) i.castSucc]
    simp only [Fin.val_castSucc, Complex.ofReal_div, div_pow]
    ring

end Paper
end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.prop_representation
