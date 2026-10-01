import ModifiedCartan.LocalCoefficientSplit
import ModifiedCartan.HolomorphicCompactness
import ModifiedCartan.MeasureLimitTransfer

open scoped Topology Classical BigOperators
open Filter MeasureTheory Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem exists_eventual_polynomial_coefficient_expansions {n : ℕ}
    (p : ℕ → Index n → Polynomial ℂ)
    (a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ)
    (hp : ∀ᶠ ν in atTop, FewInflection.polynomialWronskian (p ν) ≠ 0 ∧
      normalize (FewInflection.polynomialWronskian (p ν)) =
        ∏ j, (Polynomial.X - Polynomial.C (a ν j))) :
    ∃ γ : (ν : ℕ) → ℕ → Finset (Fin (FewInflection.polynomialWronskian (p ν)).natDegree) → ℂ,
      (∀ ν q I, ‖γ ν q I‖ ≤ (q.factorial : ℝ)) ∧
      ∀ᶠ ν in atTop, ∀ (i : Index n) (s : ℝ),
        (fun z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i /
          (s : ℂ) ^ (n + 1 - i.val)) =ᵐ[volume]
        (fun z => rootSubsetSum (exteriorRootIndices (a ν)) (a ν) (γ ν (n + 1 - i.val))
          s (n + 1 - i.val) z +
          interiorRootSubsetSum (a ν) (γ ν (n + 1 - i.val)) s (n + 1 - i.val) z) := by
  have hchoice (ν : ℕ) : ∃ γ : ℕ → Finset (Fin (FewInflection.polynomialWronskian (p ν)).natDegree) → ℂ,
      (∀ q I, ‖γ q I‖ ≤ (q.factorial : ℝ)) ∧
      ((FewInflection.polynomialWronskian (p ν) ≠ 0 ∧
        normalize (FewInflection.polynomialWronskian (p ν)) =
          ∏ j, (Polynomial.X - Polynomial.C (a ν j))) →
      ∀ (q : ℕ) (hq0 : 1 ≤ q) (hqn : q ≤ n + 1) (s : ℝ),
        (fun z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z
          ⟨n + 1 - q, by omega⟩ / (s : ℂ) ^ q) =ᵐ[volume]
        (fun z => rootSubsetSum (exteriorRootIndices (a ν)) (a ν) (γ q) s q z +
          interiorRootSubsetSum (a ν) (γ q) s q z)) := by
    by_cases hν : FewInflection.polynomialWronskian (p ν) ≠ 0 ∧
        normalize (FewInflection.polynomialWronskian (p ν)) =
          ∏ j, (Polynomial.X - Polynomial.C (a ν j))
    · obtain ⟨γ, hb, he⟩ := polynomialFamily_normalized_coefficient_split_ae (p ν) hν.1 (a ν) hν.2
      exact ⟨γ, hb, fun _ => he⟩
    · refine ⟨fun _ _ => 0, ?_, fun h => (hν h).elim⟩
      intro q I
      simp only [norm_zero]
      positivity
  choose γ hγ he using hchoice
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hp] with ν hν i s
  have hq0 : 1 ≤ n + 1 - i.val := by omega
  have hqn : n + 1 - i.val ≤ n + 1 := by omega
  have hindex : (⟨n + 1 - (n + 1 - i.val), by omega⟩ : Index n) = i := by
    apply Fin.ext
    dsimp only
    omega
  simpa only [hindex] using he ν hν (n + 1 - i.val) hq0 hqn s

namespace Paper

/-- LaTeX `eq:splitcoeff` and the vanishing consequence of `eq:F-bound`.
All polynomial approximants, root expansions, and coefficient pieces are
constructed from `eq:localhyp`. The bound is chosen before the sequence data. -/
theorem eq_splitcoeff (n : ℕ) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ),
        Tendsto s atTop atTop →
        (∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        (∀ ν, (P ν).Monic) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 → FewInflection.wronskian n (g ν) z = (P ν).eval z) →
        Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0) →
        ∃ (p : ℕ → Index n → Polynomial ℂ) (B F : ℕ → Index n → ℂ → ℂ),
          (∀ i, LocalMeasureConvergence (ball (0 : ℂ) 12)
            (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i -
              FewInflection.fundamentalCoefficients n (g ν) z i) (fun _ => 0)) ∧
          (∀ ν i, AnalyticOnNhd ℂ (B ν i) (ball 0 8)) ∧
          (∀ᶠ ν in atTop, ∀ i,
            (fun z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i /
              (s ν : ℂ) ^ (n + 1 - i.val)) =ᵐ[volume]
              (fun z => B ν i z + F ν i z)) ∧
          (∀ᶠ ν in atTop, ∀ i z, z ∈ ball (0 : ℂ) 6 → ‖B ν i z‖ ≤ K) ∧
          (∀ i, LocalMeasureConvergence (ball (0 : ℂ) 6) (fun ν => F ν i) (fun _ => 0)) := by
  obtain ⟨L, hL, hroot⟩ := eq_rootbounds n C
  let K : ℝ := ((n + 1).factorial : ℝ) * Real.exp 1 * (1 + L / 2) ^ (n + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro g s P hs hg hnorm hP hW hm
  obtain ⟨p, a, hp, hcomp, hcount, _, _, houter⟩ := hroot g s P hs hg hnorm hP hW hm
  obtain ⟨γ, hγ, hsplit⟩ := exists_eventual_polynomial_coefficient_expansions p a
    (hp.mono (fun _ h => h.2))
  let B := fun ν (i : Index n) => rootSubsetSum (exteriorRootIndices (a ν)) (a ν)
    (γ ν (n + 1 - i.val)) (s ν) (n + 1 - i.val)
  let F := fun ν (i : Index n) => interiorRootSubsetSum (a ν)
    (γ ν (n + 1 - i.val)) (s ν) (n + 1 - i.val)
  refine ⟨p, B, F, hcomp, ?_, ?_, ?_, ?_⟩
  · intro ν i
    exact exteriorRootSubsetSum_analytic _ _ _ _
  · filter_upwards [hsplit] with ν hν i
    exact hν i (s ν)
  · filter_upwards [houter, hs.eventually_gt_atTop 0] with ν hν hsν i z hz
    have hb := norm_exteriorRootSubsetSum_le (a ν) (γ ν (n + 1 - i.val)) hsν.le
      (by positivity : (0 : ℝ) ≤ ((n + 1 - i.val).factorial : ℝ))
      (hγ ν (n + 1 - i.val)) (n + 1 - i.val) z (hν z hz)
    apply hb.trans
    have hfac : ((n + 1 - i.val).factorial : ℝ) ≤ ((n + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.sub_le _ _)
    have hpow : (1 + L / 2) ^ (n + 1 - i.val) ≤ (1 + L / 2) ^ (n + 1) :=
      pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
    dsimp [K]
    gcongr
  · intro i
    exact interiorRootSubsetSum_localMeasure_zero a (fun ν => γ ν (n + 1 - i.val))
      hs hcount (by positivity) (fun ν => hγ ν (n + 1 - i.val)) houter (n + 1 - i.val)

/-- Step 4 of LaTeX `prop:localcompact`: one common subsequence of the
actual normalized differential coefficients converges locally in measure
to bounded holomorphic functions. -/
theorem local_coefficient_holomorphic_subsequence (n : ℕ) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ),
        Tendsto s atTop atTop →
        (∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        (∀ ν, (P ν).Monic) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 → FewInflection.wronskian n (g ν) z = (P ν).eval z) →
        Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0) →
        ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ b : Index n → ℂ → ℂ,
          ∀ i, AnalyticOnNhd ℂ (b i) (ball 0 4) ∧
            LocalMeasureConvergence (ball (0 : ℂ) 4)
              (fun ν z => FewInflection.fundamentalCoefficients n (g (ns ν)) z i /
                (s (ns ν) : ℂ) ^ (n + 1 - i.val)) (b i) ∧
            ∀ z ∈ ball (0 : ℂ) 1, ‖b i z‖ ≤ K := by
  obtain ⟨K, hK, hsplit⟩ := eq_splitcoeff n C
  refine ⟨K, hK, ?_⟩
  intro g s P hs hg hnorm hP hW hm
  obtain ⟨p, B, F, hcomp, hB, heq, hbound, hF⟩ := hsplit g s P hs hg hnorm hP hW hm
  obtain ⟨ns, hns, b, hb, hconv, hbbound⟩ :=
    exists_simultaneous_holomorphic_uniform_limits hK.le hB hbound
  have h46 : ball (0 : ℂ) 4 ⊆ ball 0 6 := ball_subset_ball (by norm_num)
  have h412 : ball (0 : ℂ) 4 ⊆ ball 0 12 := ball_subset_ball (by norm_num)
  refine ⟨ns, hns, b, ?_⟩
  intro i
  refine ⟨(hb i).mono (ball_subset_ball (by norm_num : (4 : ℝ) ≤ 5)), ?_, ?_⟩
  · have hBlim : LocalMeasureConvergence (ball (0 : ℂ) 4)
        (fun ν => B (ns ν) i) (b i) := uniformlyOn_localMeasureConvergence (hconv i)
          (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num : (4 : ℝ) ≤ 5)))
    have hFlim := ((hF i).mono h46).comp hns.tendsto_atTop
    have hBF : LocalMeasureConvergence (ball (0 : ℂ) 4)
        (fun ν z => B (ns ν) i z + F (ns ν) i z) (b i) := by
      simpa only [add_zero] using hBlim.add hFlim
    have hpconv : LocalMeasureConvergence (ball (0 : ℂ) 4)
        (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p (ns ν) j).eval w) z i /
          (s (ns ν) : ℂ) ^ (n + 1 - i.val)) (b i) := by
      apply hBF.congr_ae
      filter_upwards [hns.tendsto_atTop.eventually heq] with ν hν
      exact (hν i).symm
    have herr := (((hcomp i).mono h412).div_pow_scale_zero hs (n + 1 - i.val)).comp hns.tendsto_atTop
    have hresult := hpconv.add herr.neg_zero
    convert! hresult using 1
    · funext ν z
      ring
    · funext z
      simp only [add_zero]
  · intro z hz
    exact hbbound i z ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 5))) hz)

/-- Simultaneous relative compactness, the first assertion of
LaTeX `prop:localcompact`, with a constant independent of the selected sequence. -/
theorem local_coefficient_relative_compactness (n : ℕ) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ),
        Tendsto s atTop atTop →
        (∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        (∀ ν, (P ν).Monic) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 → FewInflection.wronskian n (g ν) z = (P ν).eval z) →
        Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0) →
        ∀ ρ : ℕ → ℕ, StrictMono ρ →
          ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b : Index n → ℂ → ℂ,
            ∀ i, AnalyticOnNhd ℂ (b i) (ball 0 4) ∧
              LocalMeasureConvergence (ball (0 : ℂ) 4)
                (fun ν z => FewInflection.fundamentalCoefficients n (g (ρ (σ ν))) z i /
                  (s (ρ (σ ν)) : ℂ) ^ (n + 1 - i.val)) (b i) ∧
              ∀ z ∈ ball (0 : ℂ) 1, ‖b i z‖ ≤ K := by
  obtain ⟨K, hK, hcompact⟩ := local_coefficient_holomorphic_subsequence n C
  refine ⟨K, hK, ?_⟩
  intro g s P hs hg hnorm hP hW hm ρ hρ
  exact hcompact (fun ν => g (ρ ν)) (fun ν => s (ρ ν)) (fun ν => P (ρ ν))
    (hs.comp hρ.tendsto_atTop) (fun ν => hg (ρ ν)) (fun ν => hnorm (ρ ν))
    (fun ν => hP (ρ ν)) (fun ν => hW (ρ ν)) (hm.comp hρ.tendsto_atTop)

end Paper
end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_splitcoeff
#print axioms ModifiedCartan.Paper.local_coefficient_relative_compactness
