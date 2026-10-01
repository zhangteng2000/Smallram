import ModifiedCartan.PowerExpPrimitive
import ModifiedCartan.RayScaledDerivatives
import ModifiedCartan.EntirePrimitives

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def rayPrimitivePower (ρ : ℝ) : ℝ := (1 - ρ) / ρ

theorem rayRadius_velocity_power {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    rayRadius ρ t ^ (1 - ρ) = ρ ^ rayPrimitivePower ρ * t ^ rayPrimitivePower ρ := by
  rw [rayRadius, ← Real.rpow_mul (mul_pos hρ ht).le]
  rw [show ρ⁻¹ * (1 - ρ) = rayPrimitivePower ρ by unfold rayPrimitivePower; ring]
  exact Real.mul_rpow hρ.le ht.le

theorem powerExpProfile_add_power {t : ℝ} (ht : 0 < t) (lam : ℂ) (a b : ℝ) :
    powerExpProfile lam (b + a) t = ((t ^ a : ℝ) : ℂ) * powerExpProfile lam b t := by
  rw [powerExpProfile, Real.rpow_add ht, Complex.ofReal_mul, powerExpProfile]
  ring

/-- Exact one-step primitive asymptotics in the manuscript's ray clock. -/
theorem ray_primitive_ratio_limit {ρ : ℝ} (hρ : 0 < ρ) (η : ℂ)
    {w : ℂ → ℂ} (hw : Differentiable ℂ w) {lam c : ℂ} {b : ℝ}
    (hlam : 0 < lam.re)
    (hy : Tendsto (fun t => deriv w (rayPoint ρ η t) / powerExpProfile lam b t)
      atTop (𝓝 c)) :
    Tendsto (fun t => w (rayPoint ρ η t) /
      powerExpProfile lam (b + rayPrimitivePower ρ) t)
      atTop (𝓝 ((((ρ ^ rayPrimitivePower ρ : ℝ) : ℂ) * η * c) / lam)) := by
  let a := rayPrimitivePower ρ
  let v : ℝ → ℂ := fun t => ((rayRadius ρ t ^ (1 - ρ) : ℝ) : ℂ) * η
  have hd : ∀ᶠ t in atTop, HasDerivAt (fun s => w (rayPoint ρ η s))
      (deriv w (rayPoint ρ η t) * v t) t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (hw (rayPoint ρ η t)).hasDerivAt.comp t (rayPoint_hasDerivAt hρ ht η)
  have hl : Tendsto (fun t => (deriv w (rayPoint ρ η t) * v t) /
      powerExpProfile lam (b + a) t) atTop (𝓝 (((ρ ^ a : ℝ) : ℂ) * η * c)) := by
    apply (hy.const_mul (((ρ ^ a : ℝ) : ℂ) * η)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hp := powerExpProfile_ne_zero ht lam b
    have hpw : ((t ^ a : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht a).ne'
    dsimp [v]
    rw [rayRadius_velocity_power hρ ht, Complex.ofReal_mul, powerExpProfile_add_power ht]
    change ((ρ ^ a : ℝ) : ℂ) * η * (deriv w (rayPoint ρ η t) / powerExpProfile lam b t) =
      (deriv w (rayPoint ρ η t) * ((((ρ ^ a : ℝ) : ℂ) * ((t ^ a : ℝ) : ℂ)) * η)) /
        (((t ^ a : ℝ) : ℂ) * powerExpProfile lam b t)
    field_simp
  exact powerExp_primitive_ratio_limit hlam hd hl

/-- Repeated actual entire primitives preserve every positive exponential rate,
with a proved nonzero leading coefficient at every step. -/
theorem ray_iteratedPrimitive_ratio_limit {ρ : ℝ} (hρ : 0 < ρ) {η : ℂ} (hη : η ≠ 0)
    (m : ℕ) {w : ℂ → ℂ} (hw : Differentiable ℂ w) {lam c : ℂ} {b : ℝ}
    (hlam : 0 < lam.re) (hc : c ≠ 0)
    (hy : Tendsto (fun t => iteratedDeriv m w (rayPoint ρ η t) / powerExpProfile lam b t)
      atTop (𝓝 c)) :
    ∃ d : ℂ, d ≠ 0 ∧ Tendsto (fun t => w (rayPoint ρ η t) /
      powerExpProfile lam (b + (m : ℝ) * rayPrimitivePower ρ) t) atTop (𝓝 d) := by
  induction m generalizing w b c with
  | zero => exact ⟨c, hc, by simpa only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, add_zero] using hy⟩
  | succ m ih =>
    have hyr : Tendsto (fun t => iteratedDeriv m (deriv w) (rayPoint ρ η t) /
        powerExpProfile lam b t) atTop (𝓝 c) := by
      simpa only [iteratedDeriv_succ'] using hy
    obtain ⟨d, hd, hdl⟩ := ih hw.deriv hc hyr
    have hl := ray_primitive_ratio_limit hρ η hw hlam hdl
    refine ⟨(((ρ ^ rayPrimitivePower ρ : ℝ) : ℂ) * η * d) / lam, ?_, ?_⟩
    · exact div_ne_zero (mul_ne_zero (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hρ _).ne') hη) hd)
        (by intro he; simp [he] at hlam)
    · have he : b + (m : ℝ) * rayPrimitivePower ρ + rayPrimitivePower ρ =
          b + ((m + 1 : ℕ) : ℝ) * rayPrimitivePower ρ := by push_cast; ring
      simpa only [he] using hl

end ModifiedCartan
#print axioms ModifiedCartan.ray_primitive_ratio_limit
#print axioms ModifiedCartan.ray_iteratedPrimitive_ratio_limit

