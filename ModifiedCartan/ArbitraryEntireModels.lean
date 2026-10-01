import ModifiedCartan.ArbitraryLimitModels
import ModifiedCartan.MonomialExtension
import ModifiedCartan.LocalMeasureUniqueness

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Entire monomial extensions of the actual local coefficient limits,
with full-disk model identities at every positive scale. -/
theorem arbitrary_coefficient_entire_models {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    ∃ ι : ℕ → ℕ, StrictMono ι ∧ ∃ A : Fin n → ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (A i) univ ∧
        LocalMeasureConvergence (ball (0 : ℂ) 4)
          (fun ν z => (((r (ι ν) / characteristic f (r (ι ν))) : ℝ) : ℂ) ^
            (n + 1 - i.val) * canonicalCoefficient n f.coord i.castSucc ((r (ι ν) : ℂ) * z)) (A i) ∧
        IsWeightedMonomial ((n + 1 - i.val : ℕ) * (ρ - 1)) (A i)) ∧
      ∀ ε : ℝ, 0 < ε → ε < ρ → ∃ K : ℝ, 0 < K ∧
        ∀ R : ℝ, 0 < R → ∀ i : Fin n, ∃ b : ℂ → ℂ,
          AnalyticOnNhd ℂ b (ball 0 4) ∧ (∀ z ∈ ball (0 : ℂ) 1, ‖b z‖ ≤ K) ∧
          EqOn (fun z : ℂ => A i ((R : ℂ) * z))
            (fun z => ((arbitraryScaleWeight ρ ε R / R : ℝ) : ℂ) ^ (n + 1 - i.val) * b z)
            (ball 0 4) := by
  obtain ⟨ι, hι, a, ha, hscale⟩ :=
    arbitrary_coefficient_limit_scale_models f hlin htrans hsmall hρ hl hu hr
  have hext (i : Fin n) : ∃ A : ℂ → ℂ, AnalyticOnNhd ℂ A univ ∧
      EqOn (a i) A (ball 0 4) ∧ IsWeightedMonomial ((n + 1 - i.val : ℕ) * (ρ - 1)) A := by
    apply exists_entire_weighted_monomial_extension (ha i).1
    intro m hm
    apply derivative_weight_eq_of_two_power_scale_models hρ (ha i).1 (n + 1 - i.val) m ?_ hm
    intro ε hε hερ
    obtain ⟨K, _, hK⟩ := hscale ε hε hερ
    exact ⟨K, fun R hR => hK R hR i⟩
  choose A hA hEq hMono using hext
  refine ⟨ι, hι, A, ?_, ?_⟩
  · intro i
    refine ⟨hA i, (ha i).2.congr_limit_ae ?_, hMono i⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hEq i hz
  · intro ε hε hερ
    obtain ⟨K, hK, hmodels⟩ := hscale ε hε hερ
    refine ⟨K, hK, ?_⟩
    intro R hR i
    obtain ⟨b, hb, hbound, hrel⟩ := hmodels R hR i
    refine ⟨b, hb, hbound, entire_dilation_model_eqOn (hA i) hb ?_⟩
    have ht : Tendsto (fun z : ℂ => (R : ℂ) * z) (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero] using
        (show Tendsto (fun z : ℂ => z) (𝓝 0) (𝓝 0) from tendsto_id).const_mul (R : ℂ)
    have he : (fun z : ℂ => A i ((R : ℂ) * z)) =ᶠ[𝓝 0]
        (fun z : ℂ => a i ((R : ℂ) * z)) := by
      filter_upwards [ht.eventually (isOpen_ball.mem_nhds
        (mem_ball_self (by norm_num : (0 : ℝ) < 4)))] with z hz
      exact (hEq i hz).symm
    exact he.trans hrel

end ModifiedCartan
#print axioms ModifiedCartan.arbitrary_coefficient_entire_models
