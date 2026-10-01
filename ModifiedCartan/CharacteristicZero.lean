import ModifiedCartan.HerglotzNormalization
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem coordinates_proportional_on_ball_of_characteristic_zero {n : ℕ}
    (f : Curve n) {R : ℝ} (hR : 0 < R) (hzero : characteristic f R = 0) :
    ∀ z ∈ ball (0 : ℂ) R, ∀ j k,
      f.coord j 0 * f.coord k z = f.coord k 0 * f.coord j z := by
  let L := curveHerglotz f R
  let g := rescaledRepresentation f 1 L
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Index n => ℂ)).symm
  let G := fun z => e (fun j => g j z)
  have he (v : Index n → ℂ) : ‖e v‖ = euclideanNorm v := by
    rw [PiLp.norm_eq_of_L2]
    rfl
  have hnorm (z : ℂ) : ‖G z‖ = euclideanNorm (fun j => g j z) := he _
  have hpos (z : ℂ) : 0 < ‖G z‖ := by
    rw [hnorm]
    apply euclideanNorm_pos
    obtain ⟨j, hj⟩ := rescaledRepresentation_reduced f 1 L z
    intro hv
    exact hj (congrFun hv j)
  have hlog (z : ℂ) : Real.log ‖G z‖ =
      Real.log (euclideanNorm (f.vector z)) - (L z).re := by
    rw [hnorm, rescaledRepresentation_log_norm]
    simp only [Complex.ofReal_one, one_mul]
  have hbound : ∀ z ∈ ball (0 : ℂ) R, ‖G z‖ ≤ 1 := by
    intro z hz
    apply (Real.log_nonpos_iff (norm_nonneg _)).mp
    rw [hlog]
    exact sub_nonpos.mpr (curve_log_norm_le_herglotz f hz)
  have hcenterlog : Real.log ‖G 0‖ = 0 := by
    rw [hlog, show (L 0).re = Real.circleAverage
      (fun z => Real.log (euclideanNorm (f.vector z))) 0 R from curveHerglotz_re_zero f hR]
    unfold characteristic at hzero
    linarith
  have hcenter : ‖G 0‖ = 1 := by
    have ht := congrArg Real.exp hcenterlog
    simpa only [Real.exp_log (hpos 0), Real.exp_zero] using ht
  have hdiff : DifferentiableOn ℂ G (ball 0 R) := by
    apply e.differentiable.comp_differentiableOn
    apply differentiableOn_pi.mpr
    intro j z hz
    exact (rescaledRepresentation_analyticAt f 1 (curveHerglotz_analytic f R z hz) j).differentiableWithinAt
  have hmax : IsMaxOn (norm ∘ G) (ball 0 R) 0 := by
    intro z hz
    change ‖G z‖ ≤ ‖G 0‖
    rw [hcenter]
    exact hbound z hz
  have hconst := Complex.eq_const_of_exists_max hdiff (mem_ball_self hR) hmax
  intro z hz j k
  have hG : e (fun i => g i z) = e (fun i => g i 0) := hconst hz
  have hcoords := e.injective hG
  have hj := congrFun hcoords j
  have hk := congrFun hcoords k
  simp only [g, rescaledRepresentation, Complex.ofReal_one, one_mul] at hj hk
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-L z))
  linear_combination (f.coord j 0) * hk - (f.coord k 0) * hj

theorem coordinates_proportional_of_characteristic_zero {n : ℕ}
    (f : Curve n) {R : ℝ} (hR : 0 < R) (hzero : characteristic f R = 0) :
    ∀ z j k, f.coord j 0 * f.coord k z = f.coord k 0 * f.coord j z := by
  have hlocal := coordinates_proportional_on_ball_of_characteristic_zero f hR hzero
  intro z j k
  let h : ℂ → ℂ := fun w => f.coord j 0 * f.coord k w - f.coord k 0 * f.coord j w
  have hdiff : Differentiable ℂ h :=
    ((f.holomorphic k).const_mul (f.coord j 0)).sub
      ((f.holomorphic j).const_mul (f.coord k 0))
  have hne : h =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with w hw
    exact sub_eq_zero.mpr (hlocal w hw j k)
  have hall := (Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ 0) hne
  exact sub_eq_zero.mp (hall (mem_univ z))

theorem hasPolynomialRepresentation_of_characteristic_zero {n : ℕ}
    (f : Curve n) {R : ℝ} (hR : 0 < R) (hzero : characteristic f R = 0) :
    f.HasPolynomialRepresentation := by
  have hprop := coordinates_proportional_of_characteristic_zero f hR hzero
  obtain ⟨j, hj⟩ := f.reduced 0
  have hjnz : ∀ z, f.coord j z ≠ 0 := by
    intro z hz
    obtain ⟨k, hk⟩ := f.reduced z
    have he := hprop z j k
    rw [hz, mul_zero] at he
    exact hk ((mul_eq_zero.mp he).resolve_left hj)
  refine ⟨fun k => Polynomial.C (f.coord k 0), fun z => f.coord j z / f.coord j 0,
    fun z => div_ne_zero (hjnz z) hj, (f.holomorphic j).div_const _, ?_⟩
  intro k z
  simp only [Polynomial.eval_C]
  field_simp
  simpa only [mul_comm] using hprop z j k

theorem characteristic_pos_of_transcendental {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) {r : ℝ} (hr : 0 < r) :
    0 < characteristic f r := by
  have hnonneg := characteristic_nonneg f hr
  rcases eq_or_lt_of_le hnonneg with hz | hp
  · exact False.elim (htrans (hasPolynomialRepresentation_of_characteristic_zero f hr hz.symm))
  · exact hp

end
end ModifiedCartan
#print axioms ModifiedCartan.hasPolynomialRepresentation_of_characteristic_zero
#print axioms ModifiedCartan.characteristic_pos_of_transcendental
