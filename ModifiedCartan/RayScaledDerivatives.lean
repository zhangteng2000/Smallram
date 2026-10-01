import ModifiedCartan.RayPowerClock
import ModifiedCartan.ScaledJets
import Mathlib.Analysis.Calculus.Deriv.Pow

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def rayPoint (ρ : ℝ) (η : ℂ) (t : ℝ) : ℂ := (rayRadius ρ t : ℂ) * η
noncomputable def rayScale (ρ β : ℝ) (δ : ℂ) (t : ℝ) : ℂ :=
  ((rayRadius ρ t ^ β : ℝ) : ℂ) * δ

noncomputable def rayDerivativeCoordinate (ρ β : ℝ) (δ η : ℂ) (y : ℂ → ℂ)
    (i : ℕ) (t : ℝ) : ℂ := iteratedDeriv i y (rayPoint ρ η t) / rayScale ρ β δ t ^ i

noncomputable def rayDerivativeJet (q : ℕ) (ρ β : ℝ) (δ η : ℂ) (y : ℂ → ℂ)
    (t : ℝ) (i : Fin q) : ℂ := rayDerivativeCoordinate ρ β δ η y i.val t

theorem rayScale_ne_zero {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (β : ℝ)
    {δ : ℂ} (hδ : δ ≠ 0) : rayScale ρ β δ t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (rayRadius_pos hρ ht) β).ne') hδ

theorem rayScale_hasDerivAt {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (β : ℝ) (δ : ℂ) :
    HasDerivAt (rayScale ρ β δ) (((β / (ρ * t) : ℝ) : ℂ) * rayScale ρ β δ t) t := by
  have hd := ((rayRadius_power_hasDerivAt hρ ht β).ofReal_comp).mul_const δ
  simpa only [rayScale, Complex.ofReal_mul, mul_assoc] using! hd

theorem rayPoint_hasDerivAt {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (η : ℂ) :
    HasDerivAt (rayPoint ρ η) (((rayRadius ρ t ^ (1 - ρ) : ℝ) : ℂ) * η) t := by
  simpa only [rayPoint] using! ((rayRadius_hasDerivAt hρ ht).ofReal_comp).mul_const η

theorem iteratedDeriv_rayPoint_hasDerivAt {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    {y : ℂ → ℂ} (hy : Differentiable ℂ y) (η : ℂ) (i : ℕ) :
    HasDerivAt (fun u => iteratedDeriv i y (rayPoint ρ η u))
      (iteratedDeriv (i + 1) y (rayPoint ρ η t) *
        (((rayRadius ρ t ^ (1 - ρ) : ℝ) : ℂ) * η)) t := by
  have ha := (Complex.analyticOnNhd_univ_iff_differentiable.mpr hy)
    (rayPoint ρ η t) (mem_univ _)
  have hd := (FewInflection.analyticAt_iteratedDeriv ha i).differentiableAt.hasDerivAt
  rw [← iteratedDeriv_succ] at hd
  simpa only [Function.comp_apply] using! hd.comp t (rayPoint_hasDerivAt hρ ht η)

theorem quotient_pow_hasDerivAt {F a : ℝ → ℂ} {F' c : ℂ} {t : ℝ}
    (hF : HasDerivAt F F' t) (ha : HasDerivAt a (c * a t) t) (ha0 : a t ≠ 0) (i : ℕ) :
    HasDerivAt (fun u => F u / a u ^ i)
      (F' / a t ^ i - (i : ℂ) * c * (F t / a t ^ i)) t := by
  cases i with
  | zero => simpa only [pow_zero, div_one, Nat.cast_zero, zero_mul, sub_zero] using! hF
  | succ i =>
    apply (hF.div (ha.pow (i + 1)) (pow_ne_zero _ ha0)).congr_deriv
    simp only [Pi.pow_apply, Nat.add_sub_cancel, pow_succ]
    field_simp

theorem rayDerivativeCoordinate_hasDerivAt {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (β : ℝ) {δ : ℂ} (hδ : δ ≠ 0) (η : ℂ) {y : ℂ → ℂ}
    (hy : Differentiable ℂ y) (i : ℕ) :
    HasDerivAt (rayDerivativeCoordinate ρ β δ η y i)
      (iteratedDeriv (i + 1) y (rayPoint ρ η t) *
          (((rayRadius ρ t ^ (1 - ρ) : ℝ) : ℂ) * η) / rayScale ρ β δ t ^ i -
        (i : ℂ) * ((β / (ρ * t) : ℝ) : ℂ) * rayDerivativeCoordinate ρ β δ η y i t) t := by
  exact quotient_pow_hasDerivAt (iteratedDeriv_rayPoint_hasDerivAt hρ ht hy η i)
    (rayScale_hasDerivAt hρ ht β δ) (rayScale_ne_zero hρ ht β hδ) i

end ModifiedCartan
#print axioms ModifiedCartan.rayDerivativeCoordinate_hasDerivAt


