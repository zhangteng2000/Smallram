import ModifiedCartan.PolynomialRootCount
import ModifiedCartan.RootDistanceSums
import ModifiedCartan.LocalCramerComparison

open scoped Topology ENNReal BigOperators Classical
open Filter MeasureTheory Set Metric
set_option autoImplicit false

namespace ModifiedCartan
noncomputable section

def interiorRootIndices {M : ℕ} (a : Fin M → ℂ) : Finset (Fin M) :=
  Finset.univ.filter (fun i => ‖a i‖ ≤ 8)

def exteriorRootIndices {M : ℕ} (a : Fin M → ℂ) : Finset (Fin M) :=
  Finset.univ.filter (fun i => 8 < ‖a i‖)

theorem reciprocalDistanceSum_split {M : ℕ} (a : Fin M → ℂ) (z : ℂ) :
    reciprocalDistanceSum (interiorRootIndices a) a z +
      reciprocalDistanceSum (exteriorRootIndices a) a z =
        reciprocalDistanceSum Finset.univ a z := by
  simpa only [reciprocalDistanceSum, interiorRootIndices, exteriorRootIndices, not_le] using
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => ‖a i‖ ≤ 8)
      (fun i => ‖z - a i‖⁻¹)

theorem exists_eventual_normalized_root_lists (R : ℕ → Polynomial ℂ)
    (hR : ∀ᶠ ν in atTop, R ν ≠ 0) :
    ∃ a : (ν : ℕ) → Fin (R ν).natDegree → ℂ,
      ∀ᶠ ν in atTop, normalize (R ν) = ∏ i, (Polynomial.X - Polynomial.C (a ν i)) := by
  have hchoice (ν : ℕ) : ∃ a : Fin (R ν).natDegree → ℂ,
      R ν ≠ 0 → normalize (R ν) = ∏ i, (Polynomial.X - Polynomial.C (a i)) := by
    by_cases hν : R ν ≠ 0
    · obtain ⟨a, ha⟩ := exists_normalized_polynomial_root_list (R ν) hν
      exact ⟨a, fun _ => ha⟩
    · exact ⟨fun _ => 0, fun h => False.elim (hν h)⟩
  choose a ha using hchoice
  refine ⟨a, ?_⟩
  filter_upwards [hR] with ν hν
  exact ha ν hν

theorem exterior_root_sum_scaled_le {M : ℕ} (a : Fin M → ℂ)
    {L s : ℝ} (hs : 0 < s) (hM : (M : ℝ) ≤ L * s) {z : ℂ} (hz : z ∈ ball 0 6) :
    reciprocalDistanceSum (exteriorRootIndices a) a z / s ≤ L / 2 := by
  have he := reciprocalDistanceSum_exterior_le (exteriorRootIndices a) a
    (fun i hi => (Finset.mem_filter.mp hi).2) hz
  have hcard : ((exteriorRootIndices a).card : ℝ) ≤ M := by
    exact_mod_cast (show (exteriorRootIndices a).card ≤ M by
      simpa only [exteriorRootIndices, Finset.card_univ, Fintype.card_fin] using
        Finset.card_filter_le Finset.univ (fun i => 8 < ‖a i‖))
  apply (div_le_iff₀ hs).mpr
  nlinarith

namespace Paper

/-- LaTeX `eq:rootbounds`, Step 3 of `prop:localcompact`. Polynomial
approximants and their root lists are constructed from the original local
hypotheses. The Jensen alternative splits at radius eight and assigns
boundary roots to the inner part. Constants are chosen before sequence data. -/
theorem eq_rootbounds (n : ℕ) (C : ℝ) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ),
        Tendsto s atTop atTop →
        (∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        (∀ ν, (P ν).Monic) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 → FewInflection.wronskian n (g ν) z = (P ν).eval z) →
        Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0) →
        ∃ p : ℕ → Index n → Polynomial ℂ,
          ∃ a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ,
          (∀ᶠ ν in atTop,
            ((FewInflection.polynomialWronskian (p ν)).natDegree : ℝ) ≤ L * s ν ∧
            FewInflection.polynomialWronskian (p ν) ≠ 0 ∧
            normalize (FewInflection.polynomialWronskian (p ν)) =
              ∏ i, (Polynomial.X - Polynomial.C (a ν i))) ∧
          (∀ i, LocalMeasureConvergence (ball (0 : ℂ) 12)
            (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i -
              FewInflection.fundamentalCoefficients n (g ν) z i) (fun _ => 0)) ∧
          Tendsto (fun ν => ((interiorRootIndices (a ν)).card : ℝ) / s ν) atTop (𝓝 0) ∧
          Tendsto (fun ν => eLpNorm
            (fun z => reciprocalDistanceSum (interiorRootIndices (a ν)) (a ν) z / s ν)
            (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (ball 0 6))) atTop (𝓝 0) ∧
          LocalMeasureConvergence (ball (0 : ℂ) 6)
            (fun ν z => reciprocalDistanceSum (interiorRootIndices (a ν)) (a ν) z / s ν)
            (fun _ => (0 : ℝ)) ∧
          (∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 6,
            reciprocalDistanceSum (exteriorRootIndices (a ν)) (a ν) z / s ν ≤ L / 2) := by
  obtain ⟨B, hB, L, hL, happrox⟩ := eq_cramercomparison n C
  refine ⟨L, hL, ?_⟩
  intro g s P hs hg hnorm hP hW hm
  obtain ⟨p, hp, hcomp⟩ := happrox g s P hs hg hnorm hP hW hm
  let R := fun ν => FewInflection.polynomialWronskian (p ν)
  have hR : ∀ᶠ ν in atTop, R ν ≠ 0 := hp.mono (fun _ h => h.2.1)
  obtain ⟨a, ha⟩ := exists_eventual_normalized_root_lists R hR
  have herr : ∀ᶠ ν in atTop, ∀ z ∈ closedBall (0 : ℂ) 12,
      ‖(R ν).eval z - (P ν).eval z‖ ≤ 1 / 2 := by
    have hexp := (exponential_decay_of_scale hs hB).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hp, hexp] with ν hν heν z hz
    exact (hν.2.2 z hz).trans heν.le
  have hcount := polynomial_approximation_root_count_tendsto_zero P R hP a ha hs hm herr
  have hain (ν : ℕ) (i : Fin (R ν).natDegree) (hi : i ∈ interiorRootIndices (a ν)) :
      ‖a ν i‖ ≤ 8 := (Finset.mem_filter.mp hi).2
  refine ⟨p, a, ?_, hcomp, hcount, ?_, ?_, ?_⟩
  · filter_upwards [hp, ha] with ν hν haν
    exact ⟨hν.1, hν.2.1, haν⟩
  · exact inner_root_sum_eLpNorm_tendsto_zero (fun ν => interiorRootIndices (a ν)) a hain hs hcount
      (by norm_num) (by norm_num)
  · exact inner_root_sum_localMeasure_zero (fun ν => interiorRootIndices (a ν)) a hain hs hcount
  · filter_upwards [hp, hs.eventually_gt_atTop 0] with ν hν hsν z hz
    exact exterior_root_sum_scaled_le (a ν) hsν hν.1 hz

end Paper
end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_rootbounds
