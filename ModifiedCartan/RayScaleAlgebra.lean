import ModifiedCartan.RayScaledDerivatives

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem rayScale_velocity_mul {ρ β t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hρβ : ρ = 1 + β) (δ η : ℂ) :
    (((rayRadius ρ t ^ (1 - ρ) : ℝ) : ℂ) * η) * rayScale ρ β δ t = η * δ := by
  have hr := rayRadius_pos hρ ht
  have he : rayRadius ρ t ^ (1 - ρ) * rayRadius ρ t ^ β = 1 := by
    rw [← Real.rpow_add hr, show 1 - ρ + β = 0 by linarith, Real.rpow_zero]
  calc
    _ = ((rayRadius ρ t ^ (1 - ρ) * rayRadius ρ t ^ β : ℝ) : ℂ) * (η * δ) := by
      unfold rayScale
      rw [Complex.ofReal_mul]
      ring
    _ = _ := by rw [he, Complex.ofReal_one, one_mul]

theorem rayScale_pow {q k : ℕ} {ρ β t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hβ : β * (q : ℝ) = k) {δ η : ℂ} (hphase : δ ^ q = η ^ k) :
    rayScale ρ β δ t ^ q = rayPoint ρ η t ^ k := by
  have hr := rayRadius_pos hρ ht
  have hp : (rayRadius ρ t ^ β) ^ q = rayRadius ρ t ^ k := by
    rw [← Real.rpow_mul_natCast hr.le, hβ, Real.rpow_natCast]
  rw [rayScale, rayPoint, mul_pow, mul_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_pow, hp, hphase]

theorem rayDerivativeCoordinate_next_term {ρ β t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hρβ : ρ = 1 + β) {δ : ℂ} (hδ : δ ≠ 0) (η : ℂ) (y : ℂ → ℂ) (i : ℕ) :
    iteratedDeriv (i + 1) y (rayPoint ρ η t) *
        (((rayRadius ρ t ^ (1 - ρ) : ℝ) : ℂ) * η) / rayScale ρ β δ t ^ i =
      (η * δ) * rayDerivativeCoordinate ρ β δ η y (i + 1) t := by
  have ha := rayScale_ne_zero hρ ht β hδ
  calc
    _ = (((rayRadius ρ t ^ (1 - ρ) : ℝ) : ℂ) * η) *
        (iteratedDeriv (i + 1) y (rayPoint ρ η t) / rayScale ρ β δ t ^ i) := by ring
    _ = (((rayRadius ρ t ^ (1 - ρ) : ℝ) : ℂ) * η) *
        (rayScale ρ β δ t * rayDerivativeCoordinate ρ β δ η y (i + 1) t) := by
      rw [rayDerivativeCoordinate, divided_next_identity _ _ ha i]
    _ = _ := by rw [← mul_assoc, rayScale_velocity_mul hρ ht hρβ]

theorem rayDerivativeCoordinate_top {q k : ℕ} {ρ β t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hβ : β * (q : ℝ) = k) {δ η : ℂ} (hδ : δ ≠ 0) (hphase : δ ^ q = η ^ k)
    {y : ℂ → ℂ} (heq : ∀ z, iteratedDeriv q y z = z ^ k * y z) :
    rayDerivativeCoordinate ρ β δ η y q t = rayDerivativeCoordinate ρ β δ η y 0 t := by
  have ha := pow_ne_zero q (rayScale_ne_zero hρ ht β hδ)
  rw [rayDerivativeCoordinate, rayDerivativeCoordinate, heq, ← rayScale_pow hρ ht hβ hphase,
    mul_div_cancel_left₀ _ ha, iteratedDeriv_zero, pow_zero, div_one]

end ModifiedCartan
#print axioms ModifiedCartan.rayScale_pow
#print axioms ModifiedCartan.rayDerivativeCoordinate_top
