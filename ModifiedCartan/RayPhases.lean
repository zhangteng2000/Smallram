import ModifiedCartan.RayFourierSystem

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def rayPhase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem rayPhase_ne_zero (θ : ℝ) : rayPhase θ ≠ 0 := Complex.exp_ne_zero _

theorem rayPhase_norm (θ : ℝ) : ‖rayPhase θ‖ = 1 := by
  simp [rayPhase, Complex.norm_exp]

theorem rayPhase_mul (θ φ : ℝ) : rayPhase θ * rayPhase φ = rayPhase (θ + φ) := by
  unfold rayPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rayPhase_pow (θ : ℝ) (q : ℕ) : rayPhase θ ^ q = rayPhase ((q : ℝ) * θ) := by
  unfold rayPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem rayPhases_power_balance {q k : ℕ} {β : ℝ} (hβ : β * (q : ℝ) = k) (θ : ℝ) :
    rayPhase (β * θ) ^ q = rayPhase θ ^ k := by
  rw [rayPhase_pow, rayPhase_pow]
  congr 1
  calc
    (q : ℝ) * (β * θ) = (β * q) * θ := by ring
    _ = (k : ℝ) * θ := by rw [hβ]

theorem rayPhases_product {ρ β : ℝ} (hρβ : ρ = 1 + β) (θ : ℝ) :
    rayPhase θ * rayPhase (β * θ) = rayPhase (ρ * θ) := by
  rw [rayPhase_mul, hρβ]
  congr 1
  ring

theorem sharpness_beta_balance {q : ℕ} (hq : 1 ≤ q) (k : ℕ) :
    ((k : ℝ) / q) * q = k := div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))

theorem sharpness_rho_pos (q k : ℕ) : 0 < 1 + (k : ℝ) / q := by positivity

/-- The actual phases exp(i theta) and exp(i beta theta), with no branch
or algebraic phase compatibility left as an unproved premise. -/
theorem sharpness_ray_fourier_hasDerivAt {q k : ℕ} (hq : 1 ≤ q) (θ : ℝ)
    {t : ℝ} (ht : 0 < t) {y : ℂ → ℂ} (hy : Differentiable ℂ y)
    (heq : ∀ z, iteratedDeriv q y z = z ^ k * y z) :
    HasDerivAt
      (rayFourierJet q (1 + (k : ℝ) / q) ((k : ℝ) / q)
        (rayPhase (((k : ℝ) / q) * θ)) (rayPhase θ) y)
      ((Matrix.diagonal (fun j => rayPhase ((1 + (k : ℝ) / q) * θ) * sharpnessRoot q j) +
        ((t⁻¹ : ℝ) : ℂ) • rayDiagonalPerturbation q (1 + (k : ℝ) / q) ((k : ℝ) / q)).mulVec
        (rayFourierJet q (1 + (k : ℝ) / q) ((k : ℝ) / q)
          (rayPhase (((k : ℝ) / q) * θ)) (rayPhase θ) y t)) t := by
  have hd := rayFourierJet_hasDerivAt hq (sharpness_rho_pos q k) ht rfl
    (sharpness_beta_balance hq k) (rayPhase_ne_zero (((k : ℝ) / q) * θ))
    (rayPhases_power_balance (sharpness_beta_balance hq k) θ) hy heq
  have hs : raySpectralValues q (rayPhase (((k : ℝ) / q) * θ)) (rayPhase θ) =
      fun j => rayPhase ((1 + (k : ℝ) / q) * θ) * sharpnessRoot q j := by
    funext j
    unfold raySpectralValues
    rw [rayPhases_product rfl θ]
  rw [hs] at hd
  exact hd

end ModifiedCartan
#print axioms ModifiedCartan.rayPhases_power_balance
#print axioms ModifiedCartan.sharpness_ray_fourier_hasDerivAt

