import ModifiedCartan.PointSingularExponents
import ModifiedCartan.ScalarSphericalSpeed

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem scalar_wronskian_le_jet_product {s : ℝ} (hs : 0 < s)
    (g : Index 1 → ℂ → ℂ) (a : ℂ) :
    ‖FewInflection.wronskian 1 g a‖ ≤
      2 * s * scaledJetLength 1 s (g 0) a * scaledJetLength 1 s (g 1) a := by
  have hJ (j : Index 1) : 0 ≤ scaledJetLength 1 s (g j) a := euclideanNorm_nonneg _
  have hval (j : Index 1) : ‖g j a‖ ≤ scaledJetLength 1 s (g j) a := by
    simpa only [Fin.val_zero, iteratedDeriv_zero, pow_zero, one_mul] using
      derivative_norm_le_scaledJetLength hs (g j) a (0 : Index 1)
  have hder (j : Index 1) : ‖deriv (g j) a‖ ≤ s * scaledJetLength 1 s (g j) a := by
    simpa only [Fin.val_one, iteratedDeriv_one, pow_one] using
      derivative_norm_le_scaledJetLength hs (g j) a (1 : Index 1)
  rw [scalar_wronskian_formula_function]
  calc
    _ ≤ ‖g 0 a‖ * ‖deriv (g 1) a‖ + ‖g 1 a‖ * ‖deriv (g 0) a‖ := by
      simpa only [norm_mul] using norm_sub_le (g 0 a * deriv (g 1) a) (g 1 a * deriv (g 0) a)
    _ ≤ scaledJetLength 1 s (g 0) a * (s * scaledJetLength 1 s (g 1) a) +
        scaledJetLength 1 s (g 1) a * (s * scaledJetLength 1 s (g 0) a) :=
      add_le_add (mul_le_mul (hval 0) (hder 1) (norm_nonneg _) (hJ 0))
        (mul_le_mul (hval 1) (hder 0) (norm_nonneg _) (hJ 1))
    _ = _ := by ring

theorem exp_lower_of_two_factor_bound {s B x y : ℝ} (hs : 1 ≤ s)
    (hx : 0 ≤ x) (hy : y ≤ Real.exp (B * s))
    (hprod : Real.exp (-s) ≤ 2 * s * x * y) :
    Real.exp (-(B + 3) * s) ≤ x := by
  have he := Real.add_one_le_exp s
  have hs0 : 0 ≤ s := by linarith
  have h2s : 2 * s ≤ Real.exp (2 * s) := by
    calc
      _ ≤ Real.exp s * Real.exp s := mul_le_mul (by linarith) (by linarith) hs0 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : Real.exp (-s) ≤ Real.exp ((B + 2) * s) * x := by
    calc
      _ ≤ 2 * s * x * y := hprod
      _ ≤ 2 * s * x * Real.exp (B * s) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      _ ≤ Real.exp (2 * s) * x * Real.exp (B * s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2s hx) (Real.exp_pos _).le
      _ = _ := by
        rw [show (B + 2) * s = 2 * s + B * s by ring, Real.exp_add]
        ring
  have hh := (div_le_iff₀ (Real.exp_pos ((B + 2) * s))).2 (by simpa only [mul_comm] using hp)
  rw [← Real.exp_sub] at hh
  convert hh using 1 <;> congr 1 <;> ring

theorem scalar_jet_exp_lower {s B : ℝ} (hs : 1 ≤ s)
    (g : Index 1 → ℂ → ℂ) (a : ℂ)
    (hupper : ∀ j, scaledJetLength 1 s (g j) a ≤ Real.exp (B * s))
    (hW : Real.exp (-s) ≤ ‖FewInflection.wronskian 1 g a‖) :
    ∀ j, Real.exp (-(B + 3) * s) ≤ scaledJetLength 1 s (g j) a := by
  have hp := hW.trans (scalar_wronskian_le_jet_product (zero_lt_one.trans_le hs) g a)
  intro j
  fin_cases j
  · exact exp_lower_of_two_factor_bound hs (euclideanNorm_nonneg _) (hupper 1) hp
  · apply exp_lower_of_two_factor_bound hs (euclideanNorm_nonneg _) (hupper 0)
    change Real.exp (-s) ≤ 2 * s * scaledJetLength 1 s (g 1) a * scaledJetLength 1 s (g 0) a
    calc
      _ ≤ 2 * s * scaledJetLength 1 s (g 0) a * scaledJetLength 1 s (g 1) a := hp
      _ = _ := by ring

/-- Every actual unitary column has a finite exponential lower bound for its
initial jet. No singular basis is chosen or assumed here. -/
theorem ArbitraryRadiusLimitData.scalar_unitary_jet_exp_lower
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {a : ℂ} (ha : a ∈ d.good_centers.centers)
    (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ) :
    ∃ B > 0, ∀ᶠ ν in atTop, ∀ j,
      Real.exp (-B * characteristic f (r (d.subseq ν))) ≤
        scaledJetLength 1 (characteristic f (r (d.subseq ν)))
          (fun z => (polynomialMatrixGauge (d.polynomial ν)
            (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z) a := by
  let B := (5 * d.C + 2) + 2
  have hupper := unitary_polynomial_jet_eventual_bound d.scale_tendsto
    (d.replacement.polynomial_coordinate_bound d.C_pos d.A_pos d.scale_tendsto) V
    (d.good_centers.subset ha).1
  have hlog := (d.good_centers.log_wronskian a ha).eventually_const_lt (by norm_num : (-1 : ℝ) < 0)
  refine ⟨B + 3, by dsimp only [B]; linarith [d.C_pos], ?_⟩
  filter_upwards [hupper, hlog, d.scale_tendsto.eventually_ge_atTop 1] with ν huν hlν hsν
  apply scalar_jet_exp_lower hsν _ a huν
  rw [← polynomialWronskian_eval_eq_wronskian, polynomialMatrixGauge_unitary_wronskian_norm]
  have hh := Real.exp_le_exp.mpr ((lt_div_iff₀ (d.scale_pos ν)).mp hlν).le
  simpa only [neg_one_mul, Real.exp_log (norm_pos_iff.mpr (d.good_centers.wronskian_ne_zero a ha ν))] using hh

end ModifiedCartan
#print axioms ModifiedCartan.scalar_wronskian_le_jet_product
#print axioms ModifiedCartan.scalar_jet_exp_lower
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_unitary_jet_exp_lower
