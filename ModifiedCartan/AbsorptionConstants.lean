import ModifiedCartan.Envelope

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem exists_small_absorption_coefficient (n : ℕ) {I : ℝ} (hI : 0 < I) :
    ∃ ε : ℝ, 0 < ε ∧ ε * I < 1 ∧ (n : ℝ) / (1 - ε * I) < (n + 1 : ℕ) := by
  let ε : ℝ := 1 / (2 * ((n : ℝ) + 1) * I)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he : ((n : ℝ) + 1) * (ε * I) = 1 / 2 := by
    dsimp [ε]
    field_simp
    <;> ring
  have hnprod : 0 ≤ (n : ℝ) * (ε * I) := mul_nonneg hn (mul_nonneg hε.le hI.le)
  have hεI : ε * I < 1 := by nlinarith
  refine ⟨ε, hε, hεI, ?_⟩
  rw [Nat.cast_add, Nat.cast_one]
  apply (div_lt_iff₀ (sub_pos.mpr hεI)).mpr
  nlinarith

/-- Choosing the envelope exponent at order zero uses its proved limit
one, as in `prop:zero-order-ramification`. -/
theorem exists_envelope_exponent_for_ratio {c : ℝ} (hc : c < 1) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ c * envelopeConstant α < 1 := by
  have hlim : Tendsto (fun α => c * envelopeConstant α) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    simpa only [mul_one] using envelopeConstant_tendsto_one.const_mul c
  have he : ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α ∧ α < 1 ∧ c * envelopeConstant α < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
      hlim.eventually (gt_mem_nhds hc)] with α hα hα1 hbound
    exact ⟨hα, hα1, hbound⟩
  exact he.exists

end ModifiedCartan
#print axioms ModifiedCartan.exists_small_absorption_coefficient
#print axioms ModifiedCartan.exists_envelope_exponent_for_ratio
