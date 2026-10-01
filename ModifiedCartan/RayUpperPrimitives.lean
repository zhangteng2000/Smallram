import ModifiedCartan.ExponentialUpperRate
import ModifiedCartan.RayPrimitives

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem ray_primitive_upper_rate {ρ H : ℝ} (hρ : 0 < ρ) (hH : 0 ≤ H) (η : ℂ)
    {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hy : HasExponentialUpperRate H (fun t => deriv w (rayPoint ρ η t))) :
    HasExponentialUpperRate H (fun t => w (rayPoint ρ η t)) := by
  let a := rayPrimitivePower ρ
  let f' : ℝ → ℂ := fun t => deriv w (rayPoint ρ η t) *
    (((rayRadius ρ t ^ (1 - ρ) : ℝ) : ℂ) * η)
  have hd : ∀ᶠ t in atTop, HasDerivAt (fun s => w (rayPoint ρ η s)) (f' t) t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (hw (rayPoint ρ η t)).hasDerivAt.comp t (rayPoint_hasDerivAt hρ ht η)
  have hf : HasExponentialUpperRate H f' := by
    apply ((hy.real_power_mul a).const_mul (((ρ ^ a : ℝ) : ℂ) * η)).congr
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp [f']
    rw [rayRadius_velocity_power hρ ht, Complex.ofReal_mul]
    change ((ρ ^ a : ℝ) : ℂ) * η * (((t ^ a : ℝ) : ℂ) * deriv w (rayPoint ρ η t)) = _
    ring
  exact HasExponentialUpperRate.primitive hH hd hf

theorem ray_iteratedPrimitive_upper_rate {ρ H : ℝ} (hρ : 0 < ρ) (hH : 0 ≤ H) (η : ℂ)
    (m : ℕ) {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hy : HasExponentialUpperRate H (fun t => iteratedDeriv m w (rayPoint ρ η t))) :
    HasExponentialUpperRate H (fun t => w (rayPoint ρ η t)) := by
  induction m generalizing w with
  | zero => simpa only [iteratedDeriv_zero] using hy
  | succ m ih =>
    have hyr : HasExponentialUpperRate H (fun t => iteratedDeriv m (deriv w) (rayPoint ρ η t)) := by
      simpa only [iteratedDeriv_succ'] using hy
    exact ray_primitive_upper_rate hρ hH η hw (ih hw.deriv hyr)

end ModifiedCartan
#print axioms ModifiedCartan.ray_iteratedPrimitive_upper_rate
