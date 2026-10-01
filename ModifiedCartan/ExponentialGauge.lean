import ModifiedCartan.SmallOrderGauge
import ModifiedCartan.RescaledGauge
import FewInflection.ScalarGaugeRamification

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The Euclidean characteristic is exactly preserved by an entire
nowhere-zero scalar gauge. Context: `lem:small-order-coordinates`. -/
theorem characteristic_scalarGauge {n : ℕ} (f : Curve n) (a : ℂ → ℂ)
    (ha : ∀ z, a z ≠ 0) (had : Differentiable ℂ a) {r : ℝ} (hr : 0 < r) :
    characteristic (f.scalarGauge a ha had) r = characteristic f r := by
  have hlog (z : ℂ) : Real.log (euclideanNorm ((f.scalarGauge a ha had).vector z)) =
      Real.log ‖a z‖ + Real.log (euclideanNorm (f.vector z)) := by
    change Real.log (euclideanNorm (fun j => a z * f.coord j z)) = _
    rw [euclideanNorm_mul_scalar]
    change Real.log (‖a z‖ * euclideanNorm (f.vector z)) = _
    exact Real.log_mul (norm_ne_zero_iff.mpr (ha z)) (euclideanNorm_pos (f.vector_ne_zero z)).ne'
  have hi : CircleIntegrable (fun z => Real.log ‖a z‖) 0 r :=
    (had.continuous.norm.log (fun z => norm_ne_zero_iff.mpr (ha z))).continuousOn.circleIntegrable'
  unfold characteristic
  simp only [hlog]
  rw [Real.circleAverage_fun_add hi (curve_log_euclideanNorm_continuous f).continuousOn.circleIntegrable',
    FewInflection.scalar_circleAverage_log_norm_eq_center_of_nonvanishing had ha hr]
  ring

/-- The reduced curve associated with the fixed entire gauge. -/
noncomputable def exponentialGauge {n : ℕ} (f : Curve n) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) : Curve n :=
  f.scalarGauge (fun z => Complex.exp (-G z)) (fun z => Complex.exp_ne_zero _)
    (Complex.differentiable_exp.comp hG.neg)

theorem exponentialGauge_coord {n : ℕ} (f : Curve n) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) :
    (exponentialGauge f G hG).coord = gaugedCoordinates f G := rfl

theorem exponentialGauge_linearlyNonDegenerate {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (G : ℂ → ℂ) (hG : Differentiable ℂ G) :
    (exponentialGauge f G hG).linearlyNonDegenerate :=
  (FewInflection.Curve.scalarGauge_linearlyNonDegenerate_iff f _ _ _).mp hlin

theorem exponentialGauge_characteristic {n : ℕ} (f : Curve n) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) {r : ℝ} (hr : 0 < r) :
    characteristic (exponentialGauge f G hG) r = characteristic f r :=
  characteristic_scalarGauge f _ _ _ hr

theorem exponentialGauge_ramification {n : ℕ} (f : Curve n) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) :
    ramification (exponentialGauge f G hG) = ramification f :=
  FewInflection.Curve.scalarGauge_ramification_eq f _ _ _

theorem exponentialGauge_exists_regular_point {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (G : ℂ → ℂ) (hG : Differentiable ℂ G) :
    ∃ b, FewInflection.wronskian n (gaugedCoordinates f G) b ≠ 0 :=
  curve_wronskian_nontrivial (exponentialGauge f G hG)
    (exponentialGauge_linearlyNonDegenerate f hlin G hG)

end ModifiedCartan
#print axioms ModifiedCartan.characteristic_scalarGauge
#print axioms ModifiedCartan.exponentialGauge_ramification
#print axioms ModifiedCartan.exponentialGauge_exists_regular_point
