import ModifiedCartan.GaugeCoefficientAlgebra
import ModifiedCartan.CoefficientMeasurability
import ModifiedCartan.CanonicalJetSmallness
import ModifiedCartan.FiniteMeasureTuples
import ModifiedCartan.LocalCoefficientCompactness
import ModifiedCartan.MeasureConvergenceLocality

open scoped Topology Classical BigOperators Matrix
open Filter MeasureTheory Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem gauge_difference_on_convergent_coefficients {n : ℕ}
    (g : ℕ → Index n → ℂ → ℂ) (P : ℕ → Polynomial ℂ) {s : ℕ → ℝ}
    (hg : ∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32))
    (hP : ∀ ν, (P ν).Monic)
    (hW : ∀ ν z, z ∈ ball (0 : ℂ) 32 → FewInflection.wronskian n (g ν) z = (P ν).eval z)
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    {b : Index n → ℂ → ℂ}
    (hb : ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => FewInflection.fundamentalCoefficients n (g ν) z i /
        (s ν : ℂ) ^ (n + 1 - i.val)) (b i)) :
    ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => (canonicalCoefficient n (g ν) i z -
        FewInflection.fundamentalCoefficients n (g ν) z i) /
          (s ν : ℂ) ^ (n + 1 - i.val)) (fun _ => 0) := by
  let B := fun ν z (i : Index n) => FewInflection.fundamentalCoefficients n (g ν) z i /
    (s ν : ℂ) ^ (n + 1 - i.val)
  let J := fun ν z (k : Fin (n + 2)) =>
    logarithmicJet (canonicalLogDerivative n (g ν)) k.val z / (s ν : ℂ) ^ k.val
  have hBl : LocalMeasureConvergence (ball (0 : ℂ) 4) B (fun z i => b i z) :=
    LocalMeasureConvergence.finite_pi hb
  have hJl : LocalMeasureConvergence (ball (0 : ℂ) 4) J (fun _ => zeroGaugeJet n) := by
    apply LocalMeasureConvergence.finite_pi
    intro k
    by_cases hk : k.val = 0
    · have hc : LocalMeasureConvergence (ball (0 : ℂ) 4)
          (fun (_ : ℕ) (_ : ℂ) => (1 : ℂ)) (fun _ => 1) :=
        uniformlyOn_localMeasureConvergence
          (tendsto_const_nhds.tendstoUniformlyOn_const (ball (0 : ℂ) 4)) (Subset.refl _)
      simpa [J, hk, logarithmicJet, zeroGaugeJet] using! hc
    · have hj := canonical_logarithmicJet_localMeasure_zero g P hg hP hW hs hm
        (by omega : 1 ≤ k.val)
      simpa only [zeroGaugeJet, ite_eq_right hk] using hj
  have hBm : ∀ K, IsCompact K → K ⊆ ball (0 : ℂ) 4 → ∀ ν,
      AEStronglyMeasurable (B ν) (volume.restrict K) := by
    intro K hK hKU ν
    have hKU32 : K ⊆ ball (0 : ℂ) 32 := hKU.trans (ball_subset_ball (by norm_num))
    apply AEMeasurable.aestronglyMeasurable
    apply aemeasurable_pi_lambda
    intro i
    exact (fundamentalCoefficient_aestronglyMeasurable (hg ν) hK.measurableSet hKU32 i).aemeasurable.div_const _
  have hJm : ∀ K, IsCompact K → K ⊆ ball (0 : ℂ) 4 → ∀ ν,
      AEStronglyMeasurable (J ν) (volume.restrict K) := by
    intro K hK hKU ν
    have hKU32 : K ⊆ ball (0 : ℂ) 32 := hKU.trans (ball_subset_ball (by norm_num))
    have ha := canonicalLogDerivative_aestronglyMeasurable (hg ν) hK.measurableSet hKU32
    apply AEMeasurable.aestronglyMeasurable
    apply aemeasurable_pi_lambda
    intro k
    exact (logarithmicJet_aestronglyMeasurable ha k.val).aemeasurable.div_const _
  let Φ := fun x : (Index n → ℂ) × (Fin (n + 2) → ℂ) =>
    coefficientGaugePolynomial n x.1 x.2 - x.1
  have hΦ : Continuous Φ := (coefficientGaugePolynomial_continuous n).sub continuous_fst
  have hlim := hBl.continuous_map₂ hJl hBm hJm hΦ
  have hzero (z : ℂ) : Φ ((fun i => b i z), zeroGaugeJet n) = 0 := by
    simp only [Φ, coefficientGaugePolynomial_zeroGaugeJet, sub_self]
  simp only [hzero] at hlim
  intro i K hK hKU
  have hi : TendstoInMeasure (volume.restrict K)
      (fun ν z => (Φ (B ν z, J ν z)) i) atTop (fun _ => 0) := by
    apply tendstoInMeasure_zero_of_norm_le_norm (hlim K hK hKU)
    exact Eventually.of_forall (fun ν => Eventually.of_forall
      (fun z => norm_le_pi_norm (Φ (B ν z, J ν z)) i))
  apply hi.congr_left
  intro ν
  have hnz : ∀ᵐ z ∂volume.restrict K, (P ν).eval z ≠ 0 :=
    (monic_polynomial_eval_ne_zero_ae (P ν) (hP ν)).filter_mono
      (ae_mono Measure.restrict_le_self)
  filter_upwards [hnz, ae_restrict_mem hK.measurableSet] with z hz hzK
  have hz32 : z ∈ ball (0 : ℂ) 32 :=
    (ball_subset_ball (by norm_num : (4 : ℝ) ≤ 32)) (hKU hzK)
  have hWz : FewInflection.wronskian n (g ν) z ≠ 0 := by rw [hW ν z hz32]; exact hz
  have he := congrFun (canonical_normalized_coefficient_eq_polynomial
    (fun j => hg ν j z hz32) hWz (s ν)) i
  change coefficientGaugePolynomial n (B ν z) (J ν z) i - B ν z i = _
  rw [← he]
  dsimp [B]
  ring

namespace Paper

/-- LaTeX `eq:gaugecomparison`, the final assertion of `prop:localcompact`.
The conditional convergence calculation above is applied to every
subsequence using the already constructed coefficient compactness. -/
theorem eq_gaugecomparison {n : ℕ} (C : ℝ)
    (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ)
    (hg : ∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32))
    (hs : Tendsto s atTop atTop) (hP : ∀ ν, (P ν).Monic)
    (hW : ∀ ν z, z ∈ ball (0 : ℂ) 32 → FewInflection.wronskian n (g ν) z = (P ν).eval z)
    (hnorm : ∀ ν z, z ∈ ball (0 : ℂ) 32 →
      euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν))
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0)) :
    ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => (canonicalCoefficient n (g ν) i z -
        FewInflection.fundamentalCoefficients n (g ν) z i) /
          (s ν : ℂ) ^ (n + 1 - i.val)) (fun _ => 0) := by
  obtain ⟨K, hK, hcompact⟩ := local_coefficient_holomorphic_subsequence n C
  intro i
  apply localMeasureConvergence_of_subseq
  intro ns hns
  obtain ⟨ms, hms, b, hb⟩ := hcompact (fun ν => g (ns ν)) (fun ν => s (ns ν))
    (fun ν => P (ns ν)) (hs.comp hns) (fun ν => hg (ns ν)) (fun ν => hnorm (ns ν))
    (fun ν => hP (ns ν)) (fun ν => hW (ns ν)) (hm.comp hns)
  refine ⟨ms, ?_⟩
  exact gauge_difference_on_convergent_coefficients (fun ν => g (ns (ms ν)))
    (fun ν => P (ns (ms ν))) (fun ν => hg (ns (ms ν))) (fun ν => hP (ns (ms ν)))
    (fun ν => hW (ns (ms ν))) (hs.comp (hns.comp hms.tendsto_atTop))
    (hm.comp (hns.comp hms.tendsto_atTop)) (fun i => (hb i).2.1) i

/-- LaTeX `prop:localcompact`, all assertions. The common bound precedes
all sequence data. Original assumptions produce coefficient compactness,
the vanishing first canonical coefficient, and the gauge comparison. -/
theorem prop_localcompact (n : ℕ) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ),
        (∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        Tendsto s atTop atTop → (∀ ν, (P ν).Monic) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 → FewInflection.wronskian n (g ν) z = (P ν).eval z) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0) →
        (∀ ρ : ℕ → ℕ, StrictMono ρ →
          ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b : Index n → ℂ → ℂ,
            ∀ i, AnalyticOnNhd ℂ (b i) (ball 0 4) ∧
              LocalMeasureConvergence (ball (0 : ℂ) 4)
                (fun ν z => FewInflection.fundamentalCoefficients n (g (ρ (σ ν))) z i /
                  (s (ρ (σ ν)) : ℂ) ^ (n + 1 - i.val)) (b i) ∧
              ∀ z ∈ ball (0 : ℂ) 1, ‖b i z‖ ≤ K) ∧
        (∀ ν z, z ∈ ball (0 : ℂ) 32 → canonicalCoefficient n (g ν) (Fin.last n) z = 0) ∧
        (∀ i, LocalMeasureConvergence (ball (0 : ℂ) 4)
          (fun ν z => (canonicalCoefficient n (g ν) i z -
            FewInflection.fundamentalCoefficients n (g ν) z i) /
              (s ν : ℂ) ^ (n + 1 - i.val)) (fun _ => 0)) := by
  obtain ⟨K, hK, hcompact⟩ := local_coefficient_relative_compactness n C
  refine ⟨K, hK, ?_⟩
  intro g s P hg hs hP hW hnorm hm
  refine ⟨hcompact g s P hs hg hnorm hP hW hm, ?_,
    eq_gaugecomparison C g s P hg hs hP hW hnorm hm⟩
  intro ν z hz
  exact canonicalCoefficient_last_eq_zero (fun j => hg ν j z hz)

end Paper
end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_gaugecomparison
#print axioms ModifiedCartan.Paper.prop_localcompact
