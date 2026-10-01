import ModifiedCartan.ScaledPolynomialJets
import ModifiedCartan.JetLengthBounds

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem closed_unit_disk_subset_D4 {a : ℂ} (ha : a ∈ ball (0 : ℂ) 2) :
    closedBall a 1 ⊆ ball (0 : ℂ) 4 := by
  intro z hz
  have hz' : ‖z - a‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have ha' : ‖a‖ < 2 := by simpa only [mem_ball, dist_zero_right] using ha
  have ht : ‖z‖ ≤ ‖z - a‖ + ‖a‖ := by simpa only [sub_add_cancel] using norm_add_le (z - a) a
  rw [mem_ball, dist_zero_right]
  linarith

/-- A uniform polynomial bound controls all singular column lengths
after any actual unitary basis change, at every center in D2. -/
theorem unitary_polynomial_jet_eventual_bound {n : ℕ} {s : ℕ → ℝ}
    {p : ℕ → Index n → Polynomial ℂ} {C : ℝ}
    (hs : Tendsto s atTop atTop)
    (hb : ∀ᶠ ν in atTop, ∀ j z, z ∈ ball (0 : ℂ) 4 → ‖(p ν j).eval z‖ ≤ Real.exp (C * s ν))
    (V : ℕ → Matrix.unitaryGroup (Index n) ℂ) {a : ℂ} (ha : a ∈ ball (0 : ℂ) 2) :
    ∀ᶠ ν in atTop, ∀ j,
      scaledJetLength n (s ν)
        (fun z => (polynomialMatrixGauge (p ν) (V ν : Matrix (Index n) (Index n) ℂ) j).eval z) a ≤
          Real.exp ((C + 2) * s ν) := by
  have hK := jetCauchyConstant_pos n (by norm_num : (0 : ℝ) < 1)
  have hcard : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  filter_upwards [hb, hs.eventually_ge_atTop 1,
    hs.eventually_ge_atTop (Real.log (Real.sqrt (n + 1))),
    hs.eventually_ge_atTop (Real.log (jetCauchyConstant n 1))]
    with ν hbν hsν hss hsk j
  have hfn (z : ℂ) (hz : z ∈ ball (0 : ℂ) 4) :
      ‖(polynomialMatrixGauge (p ν) (V ν : Matrix (Index n) (Index n) ℂ) j).eval z‖ ≤
        Real.exp ((C + 1) * s ν) := by
    have hh := (norm_le_pi_norm
      (fun k => (polynomialMatrixGauge (p ν) (V ν : Matrix (Index n) (Index n) ℂ) k).eval z) j).trans
        (norm_le_euclideanNorm _)
    rw [polynomialMatrixGauge_unitary_norm] at hh
    have hn : ‖(fun k => (p ν k).eval z)‖ ≤ Real.exp (C * s ν) :=
      (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr (fun k => hbν k z hz)
    exact hh.trans ((euclideanNorm_le _).trans ((mul_le_mul_of_nonneg_left hn hcard.le).trans
      (constant_mul_exp_le_exp hcard hss)))
  have hc := scaledJetLength_le_of_sphere_bound (n := n) hsν (by norm_num : (0 : ℝ) < 1)
    (Real.exp_pos ((C + 1) * s ν)).le
    (polynomialMatrixGauge (p ν) (V ν : Matrix (Index n) (Index n) ℂ) j).differentiable.diffContOnCl
    (fun z hz => hfn z (closed_unit_disk_subset_D4 ha (sphere_subset_closedBall hz)))
  exact hc.trans (by simpa only [show C + 1 + 1 = C + 2 by ring] using
    constant_mul_exp_le_exp (a := C + 1) hK hsk)

end ModifiedCartan
#print axioms ModifiedCartan.unitary_polynomial_jet_eventual_bound
