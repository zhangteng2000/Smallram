import ModifiedCartan.FirstOrderElimination
import ModifiedCartan.FirstOrderError
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem firstOrderGauge_dynamics_identity {A : Type*}
    [NormedRing A] [NormedSpace ℝ A] [CompleteSpace A]
    [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (L B C : A) (b t : ℝ) (hc : L * C - C * L + B = b • (1 : A))
    (hu : IsUnit (linearGauge C t)) :
    (L + t⁻¹ • B) * linearGauge C t =
      (t⁻¹ * b) • linearGauge C t - t⁻¹ ^ 2 • C +
        linearGauge C t * (L + firstOrderError C ((B - b • (1 : A)) * C + C) t) := by
  let D : A := (B - b • (1 : A)) * C + C
  have he : linearGauge C t * firstOrderError C D t = t⁻¹ ^ 2 • D := by
    rw [firstOrderError, mul_smul_comm, inverseLinearGauge, ← mul_assoc,
      Ring.mul_inverse_cancel _ hu, one_mul]
  have hi := firstOrderGauge_identity L B C b t⁻¹ hc
  change (L + t⁻¹ • B) * linearGauge C t - (t⁻¹ * b) • linearGauge C t + t⁻¹ ^ 2 • C =
    linearGauge C t * L + t⁻¹ ^ 2 • D at hi
  change _ = _ + linearGauge C t * (L + firstOrderError C D t)
  rw [mul_add, he]
  calc
    _ = ((L + t⁻¹ • B) * linearGauge C t - (t⁻¹ * b) • linearGauge C t + t⁻¹ ^ 2 • C) +
        (t⁻¹ * b) • linearGauge C t - t⁻¹ ^ 2 • C := by abel
    _ = _ := by rw [hi]; abel

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V] [CompleteSpace V]

noncomputable def powerLinearGauge (C : V →L[ℂ] V) (b : ℝ) (X : ℝ → V) (t : ℝ) : V :=
  t ^ b • (linearGauge C t) (X t)

theorem linearGauge_apply_hasDerivWithinAt (C : V →L[ℂ] V)
    {X : ℝ → V} {X' : V} {s : Set ℝ} {t : ℝ} (ht : t ≠ 0)
    (hX : HasDerivWithinAt X X' s t) :
    HasDerivWithinAt (fun u => linearGauge C u (X u))
      (linearGauge C t X' - t⁻¹ ^ 2 • C (X t)) s t := by
  have hi : HasDerivWithinAt (fun u : ℝ => u⁻¹) (-(t⁻¹ ^ 2)) s t := by
    simpa only [id_eq, neg_div, one_div, inv_pow] using!
      ((hasDerivAt_id t).inv ht).hasDerivWithinAt
  have hC := (C.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hX
  have hd := hX.add (hi.smul hC)
  have hd' : HasDerivWithinAt (fun u => linearGauge C u (X u))
      (X' + (t⁻¹ • C X' + (-(t⁻¹ ^ 2)) • C (X t))) s t := by
    simpa only [linearGauge, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, Function.comp_apply] using! hd
  apply hd'.congr_deriv
  simp only [linearGauge, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, neg_smul, sub_eq_add_neg]
  abel

/-- The near-identity and power gauge transforms actual solutions of the
integrable-error system into actual solutions of Z'=(L+B/t)Z. -/
theorem powerLinearGauge_hasDerivWithinAt (L B C : V →L[ℂ] V) (b : ℝ)
    (hc : L * C - C * L + B = b • (1 : V →L[ℂ] V))
    {X : ℝ → V} {s : Set ℝ} {t : ℝ} (ht : 0 < t)
    (hu : IsUnit (linearGauge C t))
    (hX : HasDerivWithinAt X
      ((L + firstOrderError C ((B - b • (1 : V →L[ℂ] V)) * C + C) t) (X t)) s t) :
    HasDerivWithinAt (powerLinearGauge C b X)
      ((L + t⁻¹ • B) (powerLinearGauge C b X t)) s t := by
  have hp := (Real.hasDerivAt_rpow_const (p := b) (Or.inl ht.ne')).hasDerivWithinAt (s := s)
  have hd := hp.smul (linearGauge_apply_hasDerivWithinAt C ht.ne' hX)
  have hp' : b * t ^ (b - 1) = t ^ b * (t⁻¹ * b) := by
    rw [Real.rpow_sub_one ht.ne']
    ring
  have he := congrArg (fun F : V →L[ℂ] V => F (X t))
    (firstOrderGauge_dynamics_identity L B C b t hc hu)
  change (L + t⁻¹ • B) (linearGauge C t (X t)) =
    (t⁻¹ * b) • linearGauge C t (X t) - t⁻¹ ^ 2 • C (X t) +
      linearGauge C t ((L + firstOrderError C ((B - b • (1 : V →L[ℂ] V)) * C + C) t) (X t)) at he
  apply hd.congr_deriv
  change t ^ b • (linearGauge C t ((L + firstOrderError C
    ((B - b • (1 : V →L[ℂ] V)) * C + C) t) (X t)) - t⁻¹ ^ 2 • C (X t)) +
    (b * t ^ (b - 1)) • linearGauge C t (X t) =
      (L + t⁻¹ • B) (t ^ b • linearGauge C t (X t))
  rw [ContinuousLinearMap.map_smul_of_tower, he, hp']
  simp only [smul_add, smul_sub, mul_smul, ContinuousLinearMap.add_apply]
  abel

end ModifiedCartan
#print axioms ModifiedCartan.firstOrderGauge_dynamics_identity
#print axioms ModifiedCartan.powerLinearGauge_hasDerivWithinAt


