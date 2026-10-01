import ModifiedCartan.TwoPowerCauchy
import ModifiedCartan.TwoPowerExponents

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The Cauchy step in LaTeX `eq:monomial-coefficients`, on the local germ. -/
theorem derivative_weight_eq_of_two_power_scale_models {a : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (ha : AnalyticOnNhd ℂ a (ball 0 4)) (q m : ℕ)
    (hscale : ∀ ε : ℝ, 0 < ε → ε < ρ → ∃ K : ℝ, ∀ R : ℝ, 0 < R →
      ∃ b : ℂ → ℂ, AnalyticOnNhd ℂ b (ball 0 4) ∧
        (∀ z ∈ ball (0 : ℂ) 1, ‖b z‖ ≤ K) ∧
        (fun z : ℂ => a ((R : ℂ) * z)) =ᶠ[𝓝 0]
          (fun z => ((arbitraryScaleWeight ρ ε R / R : ℝ) : ℂ) ^ q * b z))
    (hm : iteratedDeriv m a 0 ≠ 0) : (q : ℝ) * (ρ - 1) = m := by
  apply sub_eq_zero.mp
  apply weight_zero_of_two_power_bounds (norm_pos_iff.mpr hm)
    (show 0 ≤ (q : ℝ) by positivity) hρ
  intro ε hε hερ
  obtain ⟨K, hK⟩ := hscale ε hε hερ
  refine ⟨(m.factorial : ℝ) * K / (1 / 2 : ℝ) ^ m, ?_⟩
  intro R hR
  obtain ⟨b, hb, hbound, hrel⟩ := hK R hR
  have hh := norm_iteratedDeriv_le_of_two_power_germ hR
    (ha 0 (mem_ball_self (by norm_num))) hb hbound q m hrel
  have he₁ : (q : ℝ) * (ρ - 1 - ε) - m =
      ((q : ℝ) * (ρ - 1) - m) - q * ε := by ring
  have he₂ : (q : ℝ) * (ρ - 1 + ε) - m =
      ((q : ℝ) * (ρ - 1) - m) + q * ε := by ring
  simpa only [he₁, he₂] using hh

/-- A local Taylor series with just one possible nonzero coefficient. -/
theorem analytic_eq_monomial_of_deriv_support {a : ℂ → ℂ} {p : ℝ}
    (ha : AnalyticOnNhd ℂ a (ball 0 4))
    (hsupport : ∀ m : ℕ, iteratedDeriv m a 0 ≠ 0 → p = m) :
    (∃ m : ℕ, p = m ∧ ∃ c : ℂ,
      ∀ z ∈ ball (0 : ℂ) 4, a z = c * z ^ m) ∨
    ((¬ ∃ m : ℕ, p = m) ∧ ∀ z ∈ ball (0 : ℂ) 4, a z = 0) := by
  classical
  by_cases hp : ∃ m : ℕ, p = m
  · obtain ⟨m, hm⟩ := hp
    refine Or.inl ⟨m, hm, (m.factorial : ℂ)⁻¹ * iteratedDeriv m a 0, ?_⟩
    intro z hz
    have he := Complex.taylorSeries_eq_on_ball' hz ha.differentiableOn
    rw [tsum_eq_single m] at he
    · simpa only [sub_zero] using he.symm
    · intro k hkm
      have hk : iteratedDeriv k a 0 = 0 := by
        by_contra hk
        have hmk : (m : ℝ) = k := hm.symm.trans (hsupport k hk)
        exact hkm (Nat.cast_injective hmk.symm)
      simp only [hk, mul_zero, zero_mul]
  · refine Or.inr ⟨hp, ?_⟩
    intro z hz
    have he := Complex.taylorSeries_eq_on_ball' hz ha.differentiableOn
    have hzder : ∀ m : ℕ, iteratedDeriv m a 0 = 0 := by
      intro m
      by_contra hh
      exact hp ⟨m, hsupport m hh⟩
    simpa only [hzder, mul_zero, zero_mul, tsum_zero] using he.symm

end ModifiedCartan
#print axioms ModifiedCartan.derivative_weight_eq_of_two_power_scale_models
#print axioms ModifiedCartan.analytic_eq_monomial_of_deriv_support
