import ModifiedCartan.CircleSingularSums

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem inverse_log_ratio_le {R ρ : ℝ} (hR : 0 < R) (hRρ : R < ρ) :
    (Real.log (ρ / R))⁻¹ ≤ ρ / (ρ - R) := by
  have hρ := hR.trans hRρ
  have hl : (ρ - R) / ρ ≤ Real.log (ρ / R) := by
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hρ hR)
    have he : 1 - (ρ / R)⁻¹ = (ρ - R) / ρ := by field_simp
    rwa [he] at hh
  have hh := one_div_le_one_div_of_le (div_pos (sub_pos.mpr hRρ) hρ) hl
  simpa only [one_div, inv_div] using hh

theorem nonnegative_rpow_le_one_add {x α : ℝ} (hx : 0 ≤ x) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    x ^ α ≤ 1 + x := by
  rcases le_total x 1 with hx1 | h1x
  · exact (Real.rpow_le_one hx hx1 hα).trans (by linarith)
  · exact (Real.rpow_le_self_of_one_le h1x hα1).trans (by linarith)

theorem inverse_half_power_le_one_add_inv {r : ℝ} (hr : 0 < r) :
    r ^ (-(1 / 2 : ℝ)) ≤ 1 + r⁻¹ := by
  rw [Real.rpow_neg hr.le, ← Real.inv_rpow hr.le]
  exact nonnegative_rpow_le_one_add (inv_nonneg.mpr hr.le) (by norm_num) (by norm_num)

theorem int_abs_rpow_le_self (d : ℤ) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    |(d : ℝ)| ^ α ≤ |(d : ℝ)| := by
  by_cases hd : d = 0
  · simp [hd, Real.zero_rpow hα.ne']
  have hone : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast Int.one_le_abs hd
  exact Real.rpow_le_self_of_one_le hone hα1

theorem singular_derivative_coefficient_moment_le (d : ℤ) (m : ℕ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ‖(d : ℂ) * (-1 : ℂ) ^ m * (m.factorial : ℂ)‖ ^ α ≤
      (m.factorial : ℝ) * |(d : ℝ)| := by
  have hn : ‖(d : ℂ)‖ = |(d : ℝ)| := by simp [Complex.norm_intCast]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, norm_natCast, hn,
    Real.mul_rpow (abs_nonneg _) (by positivity)]
  have hfac : (1 : ℝ) ≤ (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hh := mul_le_mul (int_abs_rpow_le_self d hα hα1)
    (Real.rpow_le_self_of_one_le hfac hα1) (Real.rpow_nonneg (by positivity) _) (abs_nonneg _)
  simpa only [mul_comm] using hh

theorem log_one_add_mul_pow_le {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) (p : ℕ) :
    Real.log (1 + C * B ^ p) ≤ Real.log (1 + C) + (p : ℝ) * Real.log B := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hp : 1 ≤ B ^ p := one_le_pow₀ hB
  calc
    _ ≤ Real.log ((1 + C) * B ^ p) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = _ := by rw [Real.log_mul (by positivity) (pow_pos hBp p).ne', Real.log_pow]

theorem posLog_mul_pow_le {C B : ℝ} (hB : 1 ≤ B) (p : ℕ) :
    Real.posLog (C * B ^ p) ≤ Real.posLog C + (p : ℝ) * Real.log B := by
  have hh := Real.posLog_mul (x := C) (y := B ^ p)
  rwa [Real.posLog_pow, Real.posLog_eq_log (x := B) (by simpa only [abs_of_nonneg (zero_le_one.trans hB)] using hB)] at hh

/-- The absolute integral divisor weights and factorial derivative coefficients
enter the singular proximity estimate only inside a logarithm. -/
theorem integer_poles_derivative_proximity_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset ℂ) (d : ℂ → ℤ) (m : ℕ) (r : ℝ), 0 < r →
      ValueDistribution.proximity (fun z : ℂ =>
        ∑ a ∈ S, ((d a : ℂ) * (-1 : ℂ) ^ m * (m.factorial : ℂ)) / (z - a) ^ (m + 1)) ⊤ r ≤
      (2 * ((m : ℝ) + 1)) *
        (Real.log (1 + K * r ^ (-(1 / 2 : ℝ)) * (m.factorial : ℝ) * ∑ a ∈ S, |(d a : ℝ)|) + 1) := by
  obtain ⟨K, hK, hprox⟩ := circle_weighted_poles_proximity_bound (ι := ℂ)
  refine ⟨K, hK, fun S d m r hr => ?_⟩
  let α : ℝ := 1 / (2 * ((m : ℝ) + 1))
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by
    dsimp [α]
    apply (div_le_one (by positivity : 0 < 2 * ((m : ℝ) + 1))).mpr
    linarith
  have hpow : ((m + 1 : ℕ) : ℝ) * α = 1 / 2 := by
    dsimp [α]
    push_cast
    field_simp
    <;> ring
  have hαinv : α⁻¹ = 2 * ((m : ℝ) + 1) := by simp [α]
  have hs : (∑ a ∈ S, ‖(d a : ℂ) * (-1 : ℂ) ^ m * (m.factorial : ℂ)‖ ^ α) ≤
      (m.factorial : ℝ) * ∑ a ∈ S, |(d a : ℝ)| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => singular_derivative_coefficient_moment_le (d a) m hα hα1)
  have hh := hprox S id (fun a => (d a : ℂ) * (-1 : ℂ) ^ m * (m.factorial : ℂ))
    r α (m + 1) hr hα hα1 hpow
  simp only [id_eq, hαinv] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ le_rfl
  apply Real.log_le_log (by positivity)
  have he := mul_le_mul_of_nonneg_left hs
    (mul_nonneg hK.le (Real.rpow_nonneg hr.le (-(1 / 2 : ℝ))))
  nlinarith

end ModifiedCartan
#print axioms ModifiedCartan.integer_poles_derivative_proximity_bound


