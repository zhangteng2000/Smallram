import ModifiedCartan.PositiveRateCompactness
import ModifiedCartan.ScalarRectangleCrosses

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A fixed multiplicative constant is absorbed by half of a positive
exponential decay rate. -/
theorem constant_mul_exp_neg_le_half_eventually {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) :
    ∀ᶠ ν in atTop, C * Real.exp (-δ * s ν) ≤ Real.exp (-(δ / 2) * s ν) := by
  rcases eq_or_lt_of_le hC with hzero | hpos
  · rw [← hzero]
    exact Eventually.of_forall (fun ν => by simpa only [zero_mul] using (Real.exp_pos _).le)
  · filter_upwards [hs.eventually_ge_atTop (2 * Real.log C / δ)] with ν hν
    have hlog : Real.log C ≤ (δ / 2) * s ν := by
      have hh := (div_le_iff₀ hδ).mp hν
      nlinarith
    have hCe : C ≤ Real.exp ((δ / 2) * s ν) := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.mpr hlog
    calc
      _ ≤ Real.exp ((δ / 2) * s ν) * Real.exp (-δ * s ν) :=
        mul_le_mul_of_nonneg_right hCe (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Exponential bounds on refinements of every escaping sequence give one
positive exponential rate for the entire sequence. -/
theorem exists_exponential_bound_of_subsequences {d s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, Tendsto ms atTop atTop ∧ ∃ δ > 0, ∃ C ≥ 0,
        ∀ᶠ ν in atTop, d (ns (ms ν)) ≤ C * Real.exp (-δ * s (ns (ms ν)))) :
    ∃ δ > 0, ∀ᶠ ν in atTop, d ν ≤ Real.exp (-δ * s ν) := by
  apply exists_eventually_positive_rate_of_subsequences
  · filter_upwards [hs.eventually_ge_atTop 0] with ν hν
    intro δ ε hε hεδ hh
    exact hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hεδ) hν))
  · intro ns hns
    obtain ⟨ms, hms, δ, hδ, C, hC, hb⟩ := hsub ns hns
    have habsorb := constant_mul_exp_neg_le_half_eventually ((hs.comp hns).comp hms) hδ hC
    refine ⟨ms, hms, δ / 2, half_pos hδ, ?_⟩
    filter_upwards [hb, habsorb] with ν hbν haν
    exact hbν.trans haν

/-- Finite concatenation preserves a positive exponential distance rate. -/
theorem exponential_distance_trans {E : Type*} [NormedAddCommGroup E]
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) {x y z : ℕ → E}
    (hxy : ∃ δ > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop, ‖x ν - y ν‖ ≤ C * Real.exp (-δ * s ν))
    (hyz : ∃ δ > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop, ‖y ν - z ν‖ ≤ C * Real.exp (-δ * s ν)) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop, ‖x ν - z ν‖ ≤ C * Real.exp (-δ * s ν) := by
  obtain ⟨δ₁, hδ₁, C₁, hC₁, h₁⟩ := hxy
  obtain ⟨δ₂, hδ₂, C₂, hC₂, h₂⟩ := hyz
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  filter_upwards [h₁, h₂, hs.eventually_ge_atTop 0] with ν h₁ν h₂ν hsν
  have he₁ := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left δ₁ δ₂)) hsν)
  have he₂ := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right δ₁ δ₂)) hsν)
  calc
    _ ≤ ‖x ν - y ν‖ + ‖y ν - z ν‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C₁ * Real.exp (-min δ₁ δ₂ * s ν) + C₂ * Real.exp (-min δ₁ δ₂ * s ν) :=
      add_le_add (h₁ν.trans (mul_le_mul_of_nonneg_left he₁ hC₁))
        (h₂ν.trans (mul_le_mul_of_nonneg_left he₂ hC₂))
    _ = _ := by ring

theorem HasSmallRectangleCrosses.mono_scale {f : Curve 1} {r s t : ℕ → ℝ} {Ω : Set ℂ}
    (h : HasSmallRectangleCrosses f r t Ω) (hst : ∀ᶠ ν in atTop, s ν ≤ t ν) :
    HasSmallRectangleCrosses f r s Ω := by
  intro R hR
  obtain ⟨δ, hδ, hh⟩ := h R hR
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hh, hst] with ν hν hstν
  obtain ⟨x, hx, y, hy, hH, hV⟩ := hν
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hstν (neg_nonpos.mpr hδ.le))
  exact ⟨x, hx, y, hy, fun u hu => (hH u hu).trans he, fun u hu => (hV u hu).trans he⟩

end ModifiedCartan
#print axioms ModifiedCartan.exists_exponential_bound_of_subsequences
#print axioms ModifiedCartan.exponential_distance_trans