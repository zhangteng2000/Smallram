import FewInflection.GaugeTranscendental
import FewInflection.ScalarGauge
import FewInflection.ScalarWronskian
import FewInflection.Growth.SharpnessBounds
import FewInflection.Growth.Transfer
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped BigOperators Topology
open Filter

namespace FewInflection

noncomputable section

/- A polynomial cannot agree with the complex exponential.  This elementary
   fact is useful when constructing genuinely transcendental test curves. -/
theorem complexExp_not_polynomial (p : Polynomial ℂ) :
    ¬ (∀ z : ℂ, p.eval z = Complex.exp z) := by
  intro h
  have hfun : (fun z : ℂ => p.eval z) = Complex.exp := by
    funext z
    exact h z
  have hpoly : p.derivative = p := by
    apply Polynomial.funext
    intro z
    have hz := congrArg (fun F : ℂ → ℂ => deriv F z) hfun
    have hz' : p.derivative.eval z = Complex.exp z := by
      simpa [Polynomial.deriv, Complex.deriv_exp] using hz
    exact hz'.trans (h z).symm
  have hdeg : p.derivative.degree < p.degree :=
    Polynomial.degree_derivative_lt (by
      intro hp
      have hzero := congrArg (fun F : ℂ → ℂ => F 0) hfun
      simp [hp] at hzero)
  rw [hpoly] at hdeg
  exact (lt_irrefl _ hdeg)

/- The two-dimensional exponential test curve. -/
def exponentialCurve : Curve 1 where
  coord := ![fun _ : ℂ => 1, Complex.exp]
  holomorphic := by
    intro j
    fin_cases j
    · change Differentiable ℂ (fun _ : ℂ => 1)
      fun_prop
    · change Differentiable ℂ Complex.exp
      exact Complex.differentiable_exp
  reduced := by
    intro z
    exact ⟨0, by simp⟩

theorem exponentialCurve_transcendental :
    exponentialCurve.Transcendental := by
  intro hrep
  rcases hrep with ⟨p, g, hg, hgd, hrep⟩
  let p₀ : Polynomial ℂ := p 0
  have hp₀_ne : ∀ z : ℂ, p₀.eval z ≠ 0 := by
    intro z hz
    have h0 := hrep 0 z
    simp [exponentialCurve, p₀, hz] at h0
  have hp₀_deg : p₀.degree = 0 := by
    by_contra hdeg
    have hp₀_ne_zero : p₀ ≠ 0 := by
      intro hp
      exact (hp₀_ne 0) (by simp [hp])
    have hnonneg : (0 : WithBot ℕ) ≤ p₀.degree := by
      rw [Polynomial.degree_eq_natDegree hp₀_ne_zero]
      exact_mod_cast (Nat.zero_le p₀.natDegree)
    have hpos : 0 < p₀.degree := lt_of_le_of_ne hnonneg (Ne.symm hdeg)
    obtain ⟨z, hz⟩ := Complex.exists_root hpos
    exact hp₀_ne z hz
  have hp₀_const : p₀ = Polynomial.C (p₀.coeff 0) :=
    Polynomial.eq_C_of_degree_eq_zero hp₀_deg
  have ha : p₀.coeff 0 ≠ 0 := by
    intro ha
    apply hp₀_ne 0
    rw [hp₀_const, ha]
    simp
  have hrel : ∀ z : ℂ, (p 1).eval z = p₀.coeff 0 * Complex.exp z := by
    intro z
    have h0 := hrep 0 z
    have h1 := hrep 1 z
    simp only [exponentialCurve, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h0 h1
    have h0' : (1 : ℂ) = g z * p₀.coeff 0 := by
      calc
        (1 : ℂ) = g z * p₀.eval z := h0
        _ = g z * p₀.coeff 0 := by rw [hp₀_const]; simp
    have hga : g z * p₀.coeff 0 = 1 := h0'.symm
    calc
      (p 1).eval z = 1 * (p 1).eval z := by ring
      _ = (g z * p₀.coeff 0) * (p 1).eval z := by rw [hga]
      _ = (p₀.coeff 0) * (g z * (p 1).eval z) := by ring
      _ = (p₀.coeff 0) * Complex.exp z := by rw [← h1]
  apply complexExp_not_polynomial (Polynomial.C (p₀.coeff 0)⁻¹ * p 1)
  intro z
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [hrel z]
  field_simp

theorem exponentialCurve_linearlyNonDegenerate :
    exponentialCurve.linearlyNonDegenerate := by
  unfold Curve.linearlyNonDegenerate
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hfun : c 0 • (exponentialCurve.coord 0) +
      c 1 • (exponentialCurve.coord 1) = 0 := by
    rw [Fin.sum_univ_two] at hc
    simpa [exponentialCurve] using hc
  have hzero := congrArg (fun F : ℂ → ℂ => F 0) hfun
  have hder := congrArg (fun F : ℂ → ℂ => deriv F 0) hfun
  have hc1 : c 1 = 0 := by
    have hder' := hder
    have hdc0 : DifferentiableAt ℂ (c 0 • exponentialCurve.coord 0) 0 := by
      change DifferentiableAt ℂ (c 0 • (fun _ : ℂ => (1 : ℂ))) 0
      fun_prop
    have hdc1 : DifferentiableAt ℂ (c 1 • exponentialCurve.coord 1) 0 := by
      change DifferentiableAt ℂ (c 1 • Complex.exp) 0
      fun_prop
    rw [deriv_add hdc0 hdc1, deriv_const_smul_field, deriv_const_smul_field] at hder'
    simpa [exponentialCurve, Complex.deriv_exp] using hder'
  have hc0 : c 0 = 0 := by
    simpa [exponentialCurve, hc1] using hzero
  fin_cases j <;> simp [hc0, hc1]

theorem wronskian_exponentialCurve (z : ℂ) :
    wronskian 1 exponentialCurve.coord z = Complex.exp z := by
  unfold wronskian
  let M : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
    iteratedDeriv (i : ℕ) (exponentialCurve.coord j) z
  change M.det = Complex.exp z
  rw [Matrix.det_fin_two M]
  simp [M, exponentialCurve]

def normalizedExponentialCurve : Curve 1 :=
  exponentialCurve.scalarGauge
    (fun z : ℂ => Complex.exp (-z / 2))
    (by intro z; exact Complex.exp_ne_zero _)
    (by fun_prop)

theorem normalizedExponentialCurve_transcendental :
    normalizedExponentialCurve.Transcendental := by
  apply (Curve.scalarGauge_transcendental_iff exponentialCurve
    (fun z : ℂ => Complex.exp (-z / 2))
    (by intro z; exact Complex.exp_ne_zero _)
    (by fun_prop)).mp
  exact exponentialCurve_transcendental

theorem normalizedExponentialCurve_linearlyNonDegenerate :
    normalizedExponentialCurve.linearlyNonDegenerate := by
  apply (Curve.scalarGauge_linearlyNonDegenerate_iff exponentialCurve
    (fun z : ℂ => Complex.exp (-z / 2))
    (by intro z; exact Complex.exp_ne_zero _)
    (by fun_prop)).mp
  exact exponentialCurve_linearlyNonDegenerate

theorem normalizedExponentialCurve_wronskian_one (z : ℂ) :
    wronskian 1 normalizedExponentialCurve.coord z = 1 := by
  rw [normalizedExponentialCurve, Curve.scalarGauge_wronskian,
    wronskian_exponentialCurve]
  calc
    Complex.exp (-z / 2) ^ (1 + 1) * Complex.exp z =
        Complex.exp (2 * (-z / 2)) * Complex.exp z := by
          norm_num
          rw [← Complex.exp_nat_mul]
          norm_num
    _ = Complex.exp (2 * (-z / 2) + z) := by rw [Complex.exp_add]
    _ = 1 := by
      rw [show 2 * (-z / 2) + z = 0 by ring]
      simp

theorem exponentialCurve_vector_norm (z : ℂ) :
    ‖exponentialCurve.vector z‖ = max 1 ‖Complex.exp z‖ := by
  rw [Pi.norm_def]
  let v : Fin 2 → NNReal := fun b => ‖(exponentialCurve.vector z) b‖₊
  have hs : Finset.univ.sup v = max (v 0) (v 1) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i hi
      fin_cases i <;> simp [v, exponentialCurve]
    · apply max_le
      · exact Finset.le_sup (Finset.mem_univ 0)
      · exact Finset.le_sup (Finset.mem_univ 1)
  rw [show (fun b => ‖(exponentialCurve.vector z) b‖₊) = v by rfl, hs]
  simp [v, Curve.vector, exponentialCurve]

theorem exponentialCurve_log_vector_norm (z : ℂ) :
    Real.log ‖exponentialCurve.vector z‖ = max 0 z.re := by
  rw [exponentialCurve_vector_norm, Complex.norm_exp]
  by_cases hz : 0 ≤ z.re
  · have hmax : max (1 : ℝ) (Real.exp z.re) = Real.exp z.re := by
      rw [← Real.exp_zero]
      exact max_eq_right (Real.exp_le_exp.mpr hz)
    rw [hmax, Real.log_exp, max_eq_right hz]
  · have hmax : max (1 : ℝ) (Real.exp z.re) = 1 := by
      rw [← Real.exp_zero]
      exact max_eq_left (Real.exp_le_exp.mpr (le_of_not_ge hz))
    rw [hmax, Real.log_one, max_eq_left (le_of_not_ge hz)]

theorem normalizedExponentialCurve_characteristic_eventuallyEq :
    characteristic normalizedExponentialCurve =ᶠ[atTop]
      characteristic exponentialCurve := by
  exact characteristic_scalarGauge_eventuallyEq exponentialCurve
    (fun z : ℂ => Complex.exp (-z / 2))
    (by intro z; exact Complex.exp_ne_zero _)
    (by fun_prop)

theorem circleAverage_re_sq (r : ℝ) :
    Real.circleAverage (fun z : ℂ => z.re ^ 2) 0 r = r ^ 2 / 2 := by
  rw [Real.circleAverage_def]
  simp only [smul_eq_mul, circleMap_zero_re, mul_pow]
  rw [intervalIntegral.integral_const_mul, integral_cos_sq]
  simp
  field_simp [Real.pi_ne_zero]

theorem exponentialCurve_circleAverage_log_norm_le {r : ℝ} (hr : 0 ≤ r) :
    Real.circleAverage (fun z : ℂ =>
      Real.log ‖exponentialCurve.vector z‖) 0 r ≤ r := by
  have hcont : Continuous (fun z : ℂ =>
      Real.log ‖exponentialCurve.vector z‖) := by
    apply (continuous_pi (fun j => (exponentialCurve.holomorphic j).continuous)).norm |>.log
    intro z
    exact norm_ne_zero_iff.mpr (exponentialCurve.vector_ne_zero z)
  apply Real.circleAverage_mono_on_of_le_circle
    hcont.continuousOn.circleIntegrable'
  intro z hz
  have hnorm : ‖z‖ = r := by
    simpa [abs_of_nonneg hr] using (mem_sphere_zero_iff_norm.mp hz)
  have hre : z.re ≤ r := by
    exact le_trans (le_abs_self z.re)
      (le_trans (Complex.abs_re_le_norm z) (le_of_eq hnorm))
  rw [exponentialCurve_log_vector_norm]
  exact max_le hr hre

theorem circleAverage_max_re_eq_neg (r : ℝ) :
    Real.circleAverage (fun z : ℂ => max 0 (-z.re)) 0 r =
      Real.circleAverage (fun z : ℂ => max 0 z.re) 0 r := by
  symm
  have hshift (θ : ℝ) :
      circleMap 0 r (θ + Real.pi) = -circleMap 0 r θ := by
    calc
      circleMap 0 r (θ + Real.pi) = circleMap 0 (-r) θ := by
        symm
        exact circleMap_neg_radius
      _ = -circleMap 0 r θ := by
        simp [circleMap]
  calc
    Real.circleAverage (fun z : ℂ => max 0 z.re) 0 r =
        (2 * Real.pi)⁻¹ • ∫ θ in 0..2 * Real.pi,
          max 0 (circleMap 0 r (θ + Real.pi)).re :=
      Real.circleAverage_eq_integral_add Real.pi
    _ = (2 * Real.pi)⁻¹ • ∫ θ in 0..2 * Real.pi,
          max 0 (-(circleMap 0 r θ).re) := by
      congr 2
      funext θ
      rw [hshift θ]
      simp
    _ = Real.circleAverage (fun z : ℂ => max 0 (-z.re)) 0 r := by
      rw [Real.circleAverage_def]

theorem exponentialCurve_circleAverage_log_norm_ge {r : ℝ} (hr : 0 < r) :
    r / 4 ≤ Real.circleAverage (fun z : ℂ =>
      Real.log ‖exponentialCurve.vector z‖) 0 r := by
  let hplus : ℂ → ℝ := fun z => max 0 z.re
  let hminus : ℂ → ℝ := fun z => max 0 (-z.re)
  have hcont_plus : Continuous hplus := by
    dsimp [hplus]
    fun_prop
  have hcont_minus : Continuous hminus := by
    dsimp [hminus]
    fun_prop
  have hint_plus : CircleIntegrable hplus 0 r :=
    hcont_plus.continuousOn.circleIntegrable'
  have hint_minus : CircleIntegrable hminus 0 r :=
    hcont_minus.continuousOn.circleIntegrable'
  have hintAbs : CircleIntegrable (fun z : ℂ => |z.re|) 0 r := by
    exact (Complex.continuous_re.abs).continuousOn.circleIntegrable'
  have hnorm_on_circle (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) |r|) :
      ‖z‖ = r := by
    simpa [abs_of_pos hr] using (mem_sphere_zero_iff_norm.mp hz)
  have hsq_le_abs (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) |r|) :
      (z.re) ^ 2 / r ≤ |z.re| := by
    have habs : |z.re| ≤ r := by
      exact le_trans (Complex.abs_re_le_norm z)
        (le_of_eq (hnorm_on_circle z hz))
    rw [div_le_iff₀ hr]
    simpa [← sq, sq_abs] using mul_le_mul_of_nonneg_left habs (abs_nonneg z.re)
  have havg_sq_le_abs :
      Real.circleAverage (fun z : ℂ => (z.re) ^ 2 / r) 0 r ≤
        Real.circleAverage (fun z : ℂ => |z.re|) 0 r := by
    apply Real.circleAverage_mono
      ((Complex.continuous_re.pow 2).div_const r).continuousOn.circleIntegrable' hintAbs
    exact hsq_le_abs
  have havg_sq :
      Real.circleAverage (fun z : ℂ => (z.re) ^ 2 / r) 0 r = r / 2 := by
    have hfun : (fun z : ℂ => (z.re) ^ 2 / r) =
        (1 / r) • (fun z : ℂ => (z.re) ^ 2) := by
      funext z
      simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [hfun, Real.circleAverage_smul, circleAverage_re_sq, smul_eq_mul]
    field_simp
  have hsum :
      Real.circleAverage (fun z : ℂ => |z.re|) 0 r =
        Real.circleAverage hplus 0 r + Real.circleAverage hminus 0 r := by
    rw [← Real.circleAverage_fun_add hint_plus hint_minus]
    congr 2
    funext z
    dsimp [hplus, hminus]
    by_cases hz : 0 ≤ z.re
    · simp [max_eq_right hz, max_eq_left (neg_nonpos.mpr hz), abs_of_nonneg hz]
    · have hz' : z.re ≤ 0 := le_of_not_ge hz
      simp [max_eq_left hz', max_eq_right (neg_nonneg.mpr hz'), abs_of_nonpos hz']
  have hsymm : Real.circleAverage hminus 0 r =
      Real.circleAverage hplus 0 r := by
    exact circleAverage_max_re_eq_neg r
  have havg_plus : r / 4 ≤ Real.circleAverage hplus 0 r := by
    nlinarith [havg_sq_le_abs, havg_sq, hsum, hsymm]
  rw [show (fun z : ℂ => Real.log ‖exponentialCurve.vector z‖) = hplus by
    funext z
    exact exponentialCurve_log_vector_norm z]
  exact havg_plus

/-- Genuine two-sided growth bounds for the exponential projective curve. -/
theorem exponentialCurve_characteristic_bounds {r : ℝ} (hr : 0 < r) :
    r / 4 ≤ characteristic exponentialCurve r ∧
      characteristic exponentialCurve r ≤ r := by
  have hcenter : Real.log ‖exponentialCurve.vector 0‖ = 0 := by
    simpa using exponentialCurve_log_vector_norm 0
  simpa only [characteristic, hcenter, sub_zero] using
    And.intro (exponentialCurve_circleAverage_log_norm_ge hr)
      (exponentialCurve_circleAverage_log_norm_le hr.le)

/-- The order-one realization is constructed from explicit entire functions;
all the witness fields are proved above, including the growth field. -/
def exponentialRealization : RealizationWitness 1 1 where
  curve := normalizedExponentialCurve
  transcendental := normalizedExponentialCurve_transcendental
  linearlyNonDegenerate := normalizedExponentialCurve_linearlyNonDegenerate
  wronskian_one := normalizedExponentialCurve_wronskian_one
  two_sided_growth := by
    obtain ⟨R, hR⟩ := eventually_atTop.mp
      normalizedExponentialCurve_characteristic_eventuallyEq
    refine ⟨1 / 4, 1, max R 1, by norm_num, by norm_num,
      lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro r hr
    rw [hR r (le_trans (le_max_left _ _) hr)]
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right _ _) hr)
    have hrpow : Real.rpow r (1 : ℝ) = r := by
      change r ^ (1 : ℝ) = r
      exact Real.rpow_one r
    rw [hrpow]
    simpa only [one_mul, one_div_mul_eq_div] using
      exponentialCurve_characteristic_bounds hrpos

theorem exponentialRealization_sharpness_instance :
    ∃ w : RealizationWitness 1 1,
      w.curve.Transcendental ∧
      w.curve.linearlyNonDegenerate ∧
      (∀ z, wronskian 1 w.curve.coord z = 1) := by
  exact ⟨exponentialRealization,
    realizationWitness_to_sharpness exponentialRealization⟩

theorem normalizedExponentialCurve_order_lowerOrder :
    order normalizedExponentialCurve = (1 : EReal) ∧
      lowerOrder normalizedExponentialCurve = (1 : EReal) := by
  exact exponentialRealization.order_lowerOrder_eq zero_lt_one

theorem normalizedExponentialCurve_smallRamification :
    SmallRamification normalizedExponentialCurve :=
  smallRamification_of_wronskian_const normalizedExponentialCurve 1
    normalizedExponentialCurve_wronskian_one

/- The exponential example has an exact radial scaling law.  This is stronger
   than the coarse bounds above and supplies a concrete regular-variation
   certificate without importing any asymptotic assertion. -/
theorem circleAverage_max_re_homogeneous {r : ℝ} (hr : 0 ≤ r) :
    Real.circleAverage (fun z : ℂ => max 0 z.re) 0 r =
      r * Real.circleAverage (fun z : ℂ => max 0 z.re) 0 1 := by
  simp only [Real.circleAverage_def, smul_eq_mul, circleMap_zero_re]
  have hfun : (fun θ : ℝ => max 0 (r * Real.cos θ)) =
      (fun θ : ℝ => r * max 0 (Real.cos θ)) := by
    funext θ
    by_cases hθ : 0 ≤ Real.cos θ
    · rw [max_eq_right (mul_nonneg hr hθ), max_eq_right hθ]
    · have hθ' : Real.cos θ ≤ 0 := le_of_not_ge hθ
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hr hθ'),
        max_eq_left hθ']
      simp
  rw [hfun, intervalIntegral.integral_const_mul]
  ring

theorem exponentialCurve_characteristic_homogeneous {r : ℝ} (hr : 0 ≤ r) :
    characteristic exponentialCurve r =
      r * characteristic exponentialCurve 1 := by
  have hlogavg (s : ℝ) :
      Real.circleAverage (fun z : ℂ => Real.log ‖exponentialCurve.vector z‖) 0 s =
        Real.circleAverage (fun z : ℂ => max 0 z.re) 0 s := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    exact exponentialCurve_log_vector_norm z
  unfold characteristic
  rw [hlogavg r, hlogavg 1, circleAverage_max_re_homogeneous hr]
  have hzero := exponentialCurve_log_vector_norm 0
  norm_num [hzero]

theorem exponentialCurve_characteristic_pos :
    0 < characteristic exponentialCurve 1 := by
  have h := exponentialCurve_characteristic_bounds (r := 1) (by norm_num)
  linarith [h.1]

theorem exponentialCurve_characteristic_regularlyVarying :
    RegularlyVarying (characteristic exponentialCurve) 1 := by
  apply regularlyVarying_of_pos_homogeneous
  · intro r hr
    rw [exponentialCurve_characteristic_homogeneous hr.le]
    exact mul_pos hr exponentialCurve_characteristic_pos
  · intro r hr c hc
    rw [exponentialCurve_characteristic_homogeneous
      (mul_nonneg hc.le hr.le),
      exponentialCurve_characteristic_homogeneous hr.le]
    have hpow : Real.rpow c (1 : ℝ) = c := by
      change c ^ (1 : ℝ) = c
      exact Real.rpow_one c
    rw [hpow]
    ring

theorem normalizedExponentialCurve_characteristic_eq_of_nonneg {r : ℝ}
    (hr : 0 ≤ r) :
    characteristic normalizedExponentialCurve r = characteristic exponentialCurve r := by
  by_cases hr0 : r = 0
  · subst r
    rw [characteristic_zero, characteristic_zero]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let g : ℂ → ℂ := fun z => Complex.exp (-z / 2)
    have hg : ∀ z, g z ≠ 0 := by
      intro z
      exact Complex.exp_ne_zero _
    have hgd : Differentiable ℂ g := by
      intro z
      fun_prop
    have hlog_cont : Continuous
        (fun z : ℂ => Real.log ‖exponentialCurve.vector z‖) := by
      apply (continuous_pi (fun j => (exponentialCurve.holomorphic j).continuous)).norm.log
      intro z
      exact norm_ne_zero_iff.mpr (exponentialCurve.vector_ne_zero z)
    have hscalar_cont : Continuous (fun z : ℂ => Real.log ‖g z‖) := by
      apply (hgd.continuous.norm).log
      intro z
      exact norm_ne_zero_iff.mpr (hg z)
    have hlogmul (z : ℂ) :
        Real.log ‖(exponentialCurve.scalarGauge g hg hgd).vector z‖ =
          Real.log ‖g z‖ + Real.log ‖exponentialCurve.vector z‖ := by
      rw [Curve.scalarGauge_vector, norm_smul,
        Real.log_mul (norm_ne_zero_iff.mpr (hg z))
          (norm_ne_zero_iff.mpr (exponentialCurve.vector_ne_zero z))]
    have havg : Real.circleAverage
        (fun z : ℂ => Real.log ‖g z‖ + Real.log ‖exponentialCurve.vector z‖) 0 r =
        Real.log ‖g 0‖ +
          Real.circleAverage (fun z : ℂ => Real.log ‖exponentialCurve.vector z‖) 0 r := by
      rw [Real.circleAverage_fun_add hscalar_cont.continuousOn.circleIntegrable'
        hlog_cont.continuousOn.circleIntegrable']
      rw [scalar_circleAverage_log_norm_eq_center_of_nonvanishing hgd hg hrpos]
    have hzero := hlogmul 0
    change characteristic (exponentialCurve.scalarGauge g hg hgd) r =
      characteristic exponentialCurve r
    unfold characteristic
    rw [show (fun z : ℂ => Real.log
        ‖(exponentialCurve.scalarGauge g hg hgd).vector z‖) =
        (fun z : ℂ => Real.log ‖g z‖ + Real.log ‖exponentialCurve.vector z‖) by
          funext z
          exact hlogmul z]
    rw [havg, hzero]
    ring

theorem normalizedExponentialCurve_characteristic_regularlyVarying :
    RegularlyVarying (characteristic normalizedExponentialCurve) 1 := by
  apply regularlyVarying_congr_eventuallyEq
    exponentialCurve_characteristic_regularlyVarying
  exact normalizedExponentialCurve_characteristic_eventuallyEq.symm

theorem normalizedExponentialCurve_slowlyVarying_factor :
    ∃ ℓ : ℝ → ℝ, SlowlyVarying ℓ ∧
      ∀ᶠ r in atTop,
        characteristic normalizedExponentialCurve r = Real.rpow r 1 * ℓ r := by
  rcases regularlyVarying_factor_of_pos_continuous
      (T := characteristic exponentialCurve) (ρ := (1 : ℝ))
      (by norm_num)
      (by
        intro r hr
        rw [exponentialCurve_characteristic_homogeneous hr.le]
        exact mul_pos hr exponentialCurve_characteristic_pos)
      (Curve.characteristic_continuous exponentialCurve).continuousOn
      exponentialCurve_characteristic_regularlyVarying with
    ⟨ℓ, hℓ, hEq⟩
  refine ⟨ℓ, hℓ, ?_⟩
  filter_upwards [normalizedExponentialCurve_characteristic_eventuallyEq, hEq]
    with r hnorm hbase
  exact hnorm.trans hbase

def normalizedExponentialCurve_mainConclusion :
    MainConclusion normalizedExponentialCurve := by
  have horders := normalizedExponentialCurve_order_lowerOrder
  refine ⟨1, horders.1.trans horders.2.symm, horders.1, horders.2, ?_,
    normalizedExponentialCurve_characteristic_regularlyVarying,
    normalizedExponentialCurve_slowlyVarying_factor⟩
  refine ⟨0, 2, by decide, by norm_num, by norm_num⟩

theorem normalizedExponentialCurve_mainTheoremStatement :
    MainTheoremStatement normalizedExponentialCurve := by
  intro hn htrans hlin hfinite hsmall
  exact mainConclusion_to_statement normalizedExponentialCurve_mainConclusion
    hn htrans hlin hfinite hsmall


end

end FewInflection
