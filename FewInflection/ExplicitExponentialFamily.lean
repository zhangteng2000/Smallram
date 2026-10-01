import FewInflection.ExplicitHigherDim
import Mathlib.LinearAlgebra.Vandermonde

open scoped BigOperators Topology
open Filter

namespace FewInflection

noncomputable section

/-! A second explicit family, with distinct exponential rates.  Unlike the
polynomial--exponential family, its norm is an exact maximum of exponentials;
the Vandermonde theorem computes its Wronskian. -/

def exponentialRate (n : ℕ) (j : Index n) : ℂ := (j : ℕ)

def exponentialFamily (n : ℕ) (j : Index n) (z : ℂ) : ℂ :=
  Complex.exp (exponentialRate n j * z)

def exponentialFamilyCurve (n : ℕ) : Curve n where
  coord := exponentialFamily n
  holomorphic := by
    intro j
    change Differentiable ℂ
      (fun z : ℂ => Complex.exp (exponentialRate n j * z))
    fun_prop
  reduced := by
    intro z
    refine ⟨0, ?_⟩
    simp [exponentialFamily, exponentialRate]

private theorem exponentialRate_injective (n : ℕ) :
    Function.Injective (exponentialRate n) := by
  intro i j hij
  apply Fin.ext
  change ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) at hij
  exact_mod_cast congrArg Complex.re hij

theorem exponentialFamily_wronskian (n : ℕ) (z : ℂ) :
    wronskian n (exponentialFamily n) z =
      (Matrix.vandermonde (exponentialRate n)).det *
        Complex.exp ((∑ j : Index n, exponentialRate n j) * z) := by
  let V : Matrix (Index n) (Index n) ℂ :=
    Matrix.transpose (Matrix.vandermonde (exponentialRate n))
  let D : Matrix (Index n) (Index n) ℂ :=
    Matrix.diagonal (fun j : Index n =>
      Complex.exp (exponentialRate n j * z))
  have hentry : (fun (i j : Index n) =>
      iteratedDeriv (i : ℕ) (exponentialFamily n j) z) = V * D := by
    funext i j
    simp only [V, D, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.diagonal_apply]
    change iteratedDeriv (i : ℕ)
        (fun s : ℂ => Complex.exp (exponentialRate n j * s)) z = _
    rw [Finset.sum_eq_single j]
    · rw [iteratedDeriv_cexp_const_mul]
      simp [exponentialRate, mul_comm, mul_left_comm, mul_assoc]
    · intro k hk hkj
      simp [hkj]
    · intro hnot
      exact (hnot (Finset.mem_univ j)).elim
  rw [show wronskian n (exponentialFamily n) z = (V * D).det by
    simp only [wronskian, hentry]]
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.sum_mul]

theorem exponentialFamily_wronskian_ne_zero (n : ℕ) (z : ℂ) :
    wronskian n (exponentialFamily n) z ≠ 0 := by
  rw [exponentialFamily_wronskian]
  apply mul_ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr (exponentialRate_injective n)
  · exact Complex.exp_ne_zero _

theorem exponentialFamilyCurve_linearlyNonDegenerate (n : ℕ) :
    (exponentialFamilyCurve n).linearlyNonDegenerate := by
  unfold Curve.linearlyNonDegenerate
  apply linearlyIndependent_of_wronskian_ne_zero
    (exponentialFamilyCurve n).coord 0
  · intro i j
    exact ((exponentialFamilyCurve n).holomorphic j).contDiff.contDiffAt
  · exact exponentialFamily_wronskian_ne_zero n 0

theorem exponentialFamilyCurve_transcendental {n : ℕ} (hn : 1 ≤ n) :
    (exponentialFamilyCurve n).Transcendental := by
  intro hrep
  rcases hrep with ⟨p, g, hg, hgd, hrep⟩
  let p₀ : Polynomial ℂ := p 0
  have hzero : (0 : Index n) ≠ (lastIndex n) := by
    intro h
    have hv := congrArg (fun j : Index n => (j : ℕ)) h
    simp [lastIndex] at hv
    omega
  let j1 : Index n := ⟨1, by omega⟩
  have hzero1 : (0 : Index n) ≠ j1 := by
    intro h
    have hv := congrArg (fun j : Index n => (j : ℕ)) h
    simp [j1] at hv
  have h0 := hrep 0
  have h1 := hrep j1
  have h0rel : ∀ z : ℂ,
      Complex.exp 0 = g z * (p₀.eval z) := by
    intro z
    simpa [exponentialFamilyCurve, exponentialFamily, exponentialRate,
      hzero, p₀] using h0 z
  have h1rel : ∀ z : ℂ,
      Complex.exp z = g z * ((p j1).eval z) := by
    intro z
    simpa [exponentialFamilyCurve, exponentialFamily, exponentialRate, j1] using h1 z
  have hp₀_ne : ∀ z : ℂ, p₀.eval z ≠ 0 := by
    intro z hz
    have := h0rel z
    simp [hz] at this
  have hp₀_const : p₀ = Polynomial.C (p₀.coeff 0) := by
    apply Polynomial.eq_C_of_degree_eq_zero
    by_contra hdeg
    have hp0 : p₀ ≠ 0 := by
      intro hp
      exact hp₀_ne 0 (by simp [hp])
    have hnonneg : (0 : WithBot ℕ) ≤ p₀.degree := by
      rw [Polynomial.degree_eq_natDegree hp0]
      exact_mod_cast Nat.zero_le p₀.natDegree
    have hpos : 0 < p₀.degree := lt_of_le_of_ne hnonneg (Ne.symm hdeg)
    obtain ⟨z, hz⟩ := Complex.exists_root hpos
    exact hp₀_ne z hz
  have ha : p₀.coeff 0 ≠ 0 := by
    intro ha
    apply hp₀_ne 0
    rw [hp₀_const, ha]
    simp
  have hrel : ∀ z : ℂ,
      (p j1).eval z = p₀.coeff 0 * Complex.exp z := by
    intro z
    have h0' : (1 : ℂ) = g z * p₀.coeff 0 := by
      calc
        (1 : ℂ) = g z * p₀.eval z := by simpa using h0rel z
        _ = g z * p₀.coeff 0 := by rw [hp₀_const]; simp
    have hga : g z * p₀.coeff 0 = 1 := h0'.symm
    calc
      (p j1).eval z = 1 * (p j1).eval z := by ring
      _ = (g z * p₀.coeff 0) * (p j1).eval z := by rw [hga]
      _ = p₀.coeff 0 * (g z * (p j1).eval z) := by ring
      _ = p₀.coeff 0 * Complex.exp z := by rw [← h1rel z]
  apply complexExp_not_polynomial
    ((Polynomial.C (p₀.coeff 0)⁻¹) * p j1)
  intro z
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [hrel z]
  field_simp

theorem exponentialFamilyCurve_vector_norm (n : ℕ) (z : ℂ) :
    ‖(exponentialFamilyCurve n).vector z‖ =
      Real.exp (max 0 ((n : ℝ) * z.re)) := by
  have hcoord : ∀ j : Index n,
      ‖(exponentialFamilyCurve n).coord j z‖ ≤
        Real.exp (max 0 ((n : ℝ) * z.re)) := by
    intro j
    simp only [exponentialFamilyCurve, Curve.vector, exponentialFamily,
      Complex.norm_exp]
    rw [show (exponentialRate n j * z).re = (j : ℝ) * z.re by
      simp [exponentialRate, Complex.mul_re]]
    apply Real.exp_le_exp.mpr
    have hj : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
    have hre : (j : ℝ) * z.re ≤ max 0 ((n : ℝ) * z.re) := by
      by_cases hz : 0 ≤ z.re
      · exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hz)
          (le_max_right _ _)
      · have hneg : (j : ℝ) * z.re ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hz)
        exact hneg.trans (le_max_left _ _)
    exact hre
  have hlast : ‖(exponentialFamilyCurve n).vector z‖ ≥
      Real.exp (max 0 ((n : ℝ) * z.re)) := by
    have hidx : (lastIndex n : ℕ) = n := rfl
    have hcoordlast : ‖(exponentialFamilyCurve n).coord (lastIndex n) z‖ =
        Real.exp ((n : ℝ) * z.re) := by
      simp [exponentialFamilyCurve, exponentialFamily, exponentialRate, hidx,
        Complex.norm_exp]
    have hlastnorm := norm_le_pi_norm ((exponentialFamilyCurve n).vector z)
      (lastIndex n)
    by_cases hz : 0 ≤ z.re
    · rw [max_eq_right (by positivity : 0 ≤ (n : ℝ) * z.re)]
      calc
        Real.exp ((n : ℝ) * z.re) =
            ‖(exponentialFamilyCurve n).coord (lastIndex n) z‖ :=
          hcoordlast.symm
        _ = ‖(exponentialFamilyCurve n).vector z (lastIndex n)‖ := rfl
        _ ≤ ‖(exponentialFamilyCurve n).vector z‖ := hlastnorm
    · have hzero : Real.exp 0 ≤ ‖(exponentialFamilyCurve n).vector z‖ := by
        have h0 := norm_le_pi_norm ((exponentialFamilyCurve n).vector z)
          (0 : Index n)
        change ‖(exponentialFamilyCurve n).coord (0 : Index n) z‖ ≤
          ‖(exponentialFamilyCurve n).vector z‖ at h0
        simpa [exponentialFamilyCurve, exponentialFamily, exponentialRate,
          Complex.norm_exp] using h0
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (le_of_not_ge hz))]
      simpa using hzero
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonempty _).2 hcoord
  · exact hlast

theorem exponentialFamilyCurve_log_norm (n : ℕ) (z : ℂ) :
    Real.log ‖(exponentialFamilyCurve n).vector z‖ =
      max 0 ((n : ℝ) * z.re) := by
  rw [exponentialFamilyCurve_vector_norm, Real.log_exp]

theorem exponentialFamilyCurve_characteristic_homogeneous
    (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    characteristic (exponentialFamilyCurve n) r =
      r * characteristic (exponentialFamilyCurve n) 1 := by
  have hlogavg (s : ℝ) :
      Real.circleAverage
        (fun z : ℂ => Real.log ‖(exponentialFamilyCurve n).vector z‖) 0 s =
      Real.circleAverage (fun z : ℂ => max 0 ((n : ℝ) * z.re)) 0 s := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    exact exponentialFamilyCurve_log_norm n z
  unfold characteristic
  rw [hlogavg r, hlogavg 1]
  have hscale :
      Real.circleAverage (fun z : ℂ => max 0 ((n : ℝ) * z.re)) 0 r =
        r * Real.circleAverage (fun z : ℂ => max 0 ((n : ℝ) * z.re)) 0 1 := by
    simp only [Real.circleAverage_def, smul_eq_mul, circleMap_zero_re]
    have hfun : (fun θ : ℝ => max 0 ((n : ℝ) * (r * Real.cos θ))) =
        (fun θ : ℝ => r * max 0 ((n : ℝ) * Real.cos θ)) := by
      funext θ
      by_cases hθ : 0 ≤ (n : ℝ) * Real.cos θ
      · rw [show (n : ℝ) * (r * Real.cos θ) =
          r * ((n : ℝ) * Real.cos θ) by ring,
          max_eq_right (mul_nonneg hr hθ), max_eq_right hθ]
      · have hθ' : (n : ℝ) * Real.cos θ ≤ 0 := le_of_not_ge hθ
        rw [show (n : ℝ) * (r * Real.cos θ) =
          r * ((n : ℝ) * Real.cos θ) by ring,
          max_eq_left (mul_nonpos_of_nonneg_of_nonpos hr hθ'),
          max_eq_left hθ']
        simp
    rw [hfun, intervalIntegral.integral_const_mul]
    ring
  rw [hscale]
  simp [exponentialFamilyCurve_log_norm]

/-! The nonzero Vandermonde factor can be removed by a constant scalar
gauge.  We keep the root construction explicit, using that every nonconstant
complex polynomial has a root. -/

def exponentialFamilyVandermonde (n : ℕ) : ℂ :=
  (Matrix.vandermonde (exponentialRate n)).det

theorem exponentialFamilyVandermonde_ne_zero (n : ℕ) :
    exponentialFamilyVandermonde n ≠ 0 := by
  exact Matrix.det_vandermonde_ne_zero_iff.mpr (exponentialRate_injective n)

theorem exists_complex_pow_eq (n : ℕ) (a : ℂ) :
    ∃ c : ℂ, c ^ (n + 1) = a := by
  let p : Polynomial ℂ := Polynomial.X ^ (n + 1) - Polynomial.C a
  have hpdeg : 0 < p.degree := by
    rw [show p = Polynomial.X ^ (n + 1) - Polynomial.C a by rfl,
      Polynomial.degree_X_pow_sub_C (by omega) a]
    positivity
  obtain ⟨c, hc⟩ := Complex.exists_root hpdeg
  refine ⟨c, ?_⟩
  have heval : p.eval c = 0 := hc
  have hsub : c ^ (n + 1) - a = 0 := by simpa [p] using heval
  exact sub_eq_zero.mp hsub

def normalizedExponentialFamilyCurve (n : ℕ) (c : ℂ)
    (hc : c ≠ 0) : Curve n :=
  (exponentialFamilyCurve n).scalarGauge
    (fun z : ℂ => c * Complex.exp
      (-z * (∑ j : Index n, exponentialRate n j) / ((n + 1 : ℕ) : ℂ)))
    (by
      intro z
      exact mul_ne_zero hc (Complex.exp_ne_zero _))
    (by fun_prop)

theorem normalizedExponentialFamilyCurve_wronskian_one
    (n : ℕ) (c : ℂ) (hc : c ≠ 0)
  (hcpow : c ^ (n + 1) = (exponentialFamilyVandermonde n)⁻¹)
    (z : ℂ) :
    wronskian n (normalizedExponentialFamilyCurve n c hc).coord z = 1 := by
  rw [normalizedExponentialFamilyCurve, Curve.scalarGauge_wronskian]
  change (c * Complex.exp
      (-z * (∑ j : Index n, exponentialRate n j) / ((n + 1 : ℕ) : ℂ))) ^
      (n + 1) * wronskian n (exponentialFamily n) z = 1
  rw [exponentialFamily_wronskian]
  let S : ℂ := ∑ j : Index n, exponentialRate n j
  have hcast : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hdet : exponentialFamilyVandermonde n ≠ 0 :=
    exponentialFamilyVandermonde_ne_zero n
  have hexp :
      Complex.exp (-z * S / ((n + 1 : ℕ) : ℂ)) ^ (n + 1) =
        Complex.exp ((n + 1 : ℕ) *
          (-z * S / ((n + 1 : ℕ) : ℂ))) := by
    rw [Complex.exp_nat_mul]
  have hcancel :
      ((n + 1 : ℕ) : ℂ) * (-z * S / ((n + 1 : ℕ) : ℂ)) + S * z = 0 := by
    field_simp [hcast]
    ring
  change (c * Complex.exp (-z * S / ((n + 1 : ℕ) : ℂ))) ^ (n + 1) *
      ((exponentialFamilyVandermonde n) * Complex.exp (S * z)) = 1
  calc
    (c * Complex.exp (-z * S / ((n + 1 : ℕ) : ℂ))) ^ (n + 1) *
        ((exponentialFamilyVandermonde n) * Complex.exp (S * z)) =
      c ^ (n + 1) *
        Complex.exp (-z * S / ((n + 1 : ℕ) : ℂ)) ^ (n + 1) *
        ((exponentialFamilyVandermonde n) * Complex.exp (S * z)) := by
          rw [mul_pow]
    _ = (exponentialFamilyVandermonde n)⁻¹ *
        Complex.exp ((n + 1 : ℕ) *
          (-z * S / ((n + 1 : ℕ) : ℂ))) *
        (exponentialFamilyVandermonde n) * Complex.exp (S * z) := by
          rw [hcpow, hexp]
          ring
    _ = Complex.exp (((n + 1 : ℕ) : ℂ) *
          (-z * S / ((n + 1 : ℕ) : ℂ)) + S * z) := by
          calc
            (exponentialFamilyVandermonde n)⁻¹ *
                Complex.exp ((n + 1 : ℕ) *
                  (-z * S / ((n + 1 : ℕ) : ℂ))) *
                (exponentialFamilyVandermonde n) * Complex.exp (S * z) =
              ((exponentialFamilyVandermonde n)⁻¹ *
                exponentialFamilyVandermonde n) *
                (Complex.exp ((n + 1 : ℕ) *
                  (-z * S / ((n + 1 : ℕ) : ℂ))) *
                Complex.exp (S * z)) := by ring
            _ = Complex.exp ((n + 1 : ℕ) *
                  (-z * S / ((n + 1 : ℕ) : ℂ))) *
                Complex.exp (S * z) := by
              rw [inv_mul_cancel₀ hdet]
              ring
            _ = Complex.exp (((n + 1 : ℕ) : ℂ) *
                  (-z * S / ((n + 1 : ℕ) : ℂ)) + S * z) := by
              rw [← Complex.exp_add]
    _ = 1 := by rw [hcancel]; simp

theorem normalizedExponentialFamilyCurve_transcendental
    {n : ℕ} (hn : 1 ≤ n) (c : ℂ) (hc : c ≠ 0) :
    (normalizedExponentialFamilyCurve n c hc).Transcendental := by
  apply (Curve.scalarGauge_transcendental_iff (exponentialFamilyCurve n)
    (fun z : ℂ => c * Complex.exp
      (-z * (∑ j : Index n, exponentialRate n j) / ((n + 1 : ℕ) : ℂ)))
    (by intro z; exact mul_ne_zero hc (Complex.exp_ne_zero _))
    (by fun_prop)).mp
  exact exponentialFamilyCurve_transcendental hn

theorem normalizedExponentialFamilyCurve_linearlyNonDegenerate
    (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    (normalizedExponentialFamilyCurve n c hc).linearlyNonDegenerate := by
  apply (Curve.scalarGauge_linearlyNonDegenerate_iff (exponentialFamilyCurve n)
    (fun z : ℂ => c * Complex.exp
      (-z * (∑ j : Index n, exponentialRate n j) / ((n + 1 : ℕ) : ℂ)))
    (by intro z; exact mul_ne_zero hc (Complex.exp_ne_zero _))
    (by fun_prop)).mp
  exact exponentialFamilyCurve_linearlyNonDegenerate n

theorem normalizedExponentialFamilyCurve_characteristic_eventuallyEq
    (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    characteristic (normalizedExponentialFamilyCurve n c hc) =ᶠ[atTop]
      characteristic (exponentialFamilyCurve n) := by
  simpa [normalizedExponentialFamilyCurve] using
    (characteristic_scalarGauge_eventuallyEq
      (exponentialFamilyCurve n)
      (fun z : ℂ => c * Complex.exp
        (-z * (∑ j : Index n, exponentialRate n j) / ((n + 1 : ℕ) : ℂ)))
      (by intro z; exact mul_ne_zero hc (Complex.exp_ne_zero _))
      (by fun_prop))

theorem exponentialFamilyCurve_characteristic_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < characteristic (exponentialFamilyCurve n) 1 := by
  have hcont : Continuous (fun z : ℂ =>
      max 0 ((n : ℝ) * z.re)) := by fun_prop
  have hint : CircleIntegrable
      (fun z : ℂ => max 0 ((n : ℝ) * z.re)) 0 1 :=
    hcont.continuousOn.circleIntegrable'
  have hcont' : Continuous (fun z : ℂ => max 0 z.re) := by fun_prop
  have hint' : CircleIntegrable (fun z : ℂ => max 0 z.re) 0 1 :=
    hcont'.continuousOn.circleIntegrable'
  have hmono : Real.circleAverage (fun z : ℂ => max 0 z.re) 0 1 ≤
      Real.circleAverage (fun z : ℂ => max 0 ((n : ℝ) * z.re)) 0 1 := by
    apply Real.circleAverage_mono hint' hint
    intro z hz
    by_cases hzre : 0 ≤ z.re
    · rw [max_eq_right hzre,
        max_eq_right (mul_nonneg (by positivity) hzre)]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      simpa using (mul_le_mul_of_nonneg_right hnR hzre)
    · simp [max_eq_left (le_of_not_ge hzre)]
  have hbase : (1 : ℝ) / 4 ≤
      Real.circleAverage (fun z : ℂ => max 0 z.re) 0 1 := by
    simpa [exponentialCurve_log_vector_norm] using
      (exponentialCurve_circleAverage_log_norm_ge (r := 1) (by norm_num))
  have hcenter : Real.log ‖(exponentialFamilyCurve n).vector 0‖ = 0 := by
    rw [exponentialFamilyCurve_log_norm]
    norm_num
  have hlogavg :
      Real.circleAverage
          (fun z : ℂ => Real.log ‖(exponentialFamilyCurve n).vector z‖) 0 1 =
        Real.circleAverage (fun z : ℂ => max 0 ((n : ℝ) * z.re)) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    exact exponentialFamilyCurve_log_norm n z
  unfold characteristic
  rw [hcenter, hlogavg]
  have hle : (1 : ℝ) / 4 ≤
      Real.circleAverage (fun z : ℂ => max 0 ((n : ℝ) * z.re)) 0 1 :=
    hbase.trans hmono
  simpa using (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hle)

theorem normalizedExponentialFamilyCurve_characteristic_regularlyVarying
    {n : ℕ} (hn : 1 ≤ n) (c : ℂ) (hc : c ≠ 0) :
    RegularlyVarying
      (characteristic (normalizedExponentialFamilyCurve n c hc)) 1 := by
  apply regularlyVarying_congr_eventuallyEq
    (regularlyVarying_of_pos_homogeneous
      (fun r hr => by
        rw [exponentialFamilyCurve_characteristic_homogeneous n hr.le]
        exact mul_pos hr (exponentialFamilyCurve_characteristic_pos hn))
      (by
        intro r hr c' hc'
        rw [exponentialFamilyCurve_characteristic_homogeneous n
          (mul_nonneg hc'.le hr.le),
          exponentialFamilyCurve_characteristic_homogeneous n hr.le]
        have hpow : Real.rpow c' (1 : ℝ) = c' := by
          change c' ^ (1 : ℝ) = c'
          exact Real.rpow_one c'
        rw [hpow]
        ring))
    (normalizedExponentialFamilyCurve_characteristic_eventuallyEq n c hc).symm

def normalizedExponentialFamilyRealization
    {n : ℕ} (hn : 1 ≤ n) (c : ℂ) (hc : c ≠ 0)
    (hcpow : c ^ (n + 1) = (exponentialFamilyVandermonde n)⁻¹) :
    RealizationWitness n 1 where
  curve := normalizedExponentialFamilyCurve n c hc
  transcendental := normalizedExponentialFamilyCurve_transcendental hn c hc
  linearlyNonDegenerate := normalizedExponentialFamilyCurve_linearlyNonDegenerate n c hc
  wronskian_one := normalizedExponentialFamilyCurve_wronskian_one n c hc hcpow
  two_sided_growth := by
    rcases eventually_atTop.mp
      (normalizedExponentialFamilyCurve_characteristic_eventuallyEq n c hc) with
      ⟨R₀, hR₀⟩
    let a : ℝ := characteristic (exponentialFamilyCurve n) 1
    have ha : 0 < a := exponentialFamilyCurve_characteristic_pos hn
    refine ⟨a, a, max R₀ 1, ha, ha,
      lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right _ _) hr)
    have hEq : characteristic (normalizedExponentialFamilyCurve n c hc) r =
        characteristic (exponentialFamilyCurve n) r :=
      hR₀ r (le_trans (le_max_left _ _) hr)
    have hhom := exponentialFamilyCurve_characteristic_homogeneous n hrpos.le
    have hpow : Real.rpow r (1 : ℝ) = r := by
      change r ^ (1 : ℝ) = r
      exact Real.rpow_one r
    rw [hpow, hEq, hhom]
    simp [a, mul_comm]

theorem exponentialFamily_realization_sharpness_instance
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ w : RealizationWitness n 1,
      w.curve.Transcendental ∧ w.curve.linearlyNonDegenerate ∧
      (∀ z, wronskian n w.curve.coord z = 1) := by
  obtain ⟨c, hcpow⟩ := exists_complex_pow_eq n
    (exponentialFamilyVandermonde n)⁻¹
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_pow (by omega)] at hcpow
    exact (inv_ne_zero (exponentialFamilyVandermonde_ne_zero n)) hcpow.symm
  let w := normalizedExponentialFamilyRealization hn c hc hcpow
  refine ⟨w, w.transcendental, w.linearlyNonDegenerate, w.wronskian_one⟩

def normalizedExponentialFamily_mainConclusion
    {n : ℕ} (hn : 1 ≤ n) (c : ℂ) (hc : c ≠ 0)
    (hcpow : c ^ (n + 1) = (exponentialFamilyVandermonde n)⁻¹) :
    MainConclusion (normalizedExponentialFamilyCurve n c hc) := by
  let f := normalizedExponentialFamilyCurve n c hc
  let w := normalizedExponentialFamilyRealization hn c hc hcpow
  have hreg : RegularlyVarying (characteristic f) 1 := by
    simpa [f] using normalizedExponentialFamilyCurve_characteristic_regularlyVarying
      hn c hc
  have hslow : ∃ ℓ : ℝ → ℝ, SlowlyVarying ℓ ∧
      ∀ᶠ r in atTop, characteristic f r = Real.rpow r 1 * ℓ r := by
    let a : ℝ → ℝ := characteristic (exponentialFamilyCurve n)
    have hapos : ∀ r, 0 < r → 0 < a r := by
      intro r hr
      dsimp [a]
      rw [exponentialFamilyCurve_characteristic_homogeneous n hr.le]
      exact mul_pos hr (exponentialFamilyCurve_characteristic_pos hn)
    have hbaseReg : RegularlyVarying a 1 := by
      apply regularlyVarying_of_pos_homogeneous hapos
      intro r hr c' hc'
      dsimp [a]
      rw [exponentialFamilyCurve_characteristic_homogeneous n
        (mul_nonneg hc'.le hr.le),
        exponentialFamilyCurve_characteristic_homogeneous n hr.le]
      norm_num [Real.rpow_one]
      ring
    rcases regularlyVarying_factor_of_pos_continuous
      (T := a) (ρ := (1 : ℝ)) (by norm_num) hapos
      (Curve.characteristic_continuous (exponentialFamilyCurve n)).continuousOn
      hbaseReg with
      ⟨ℓ, hℓ, hℓeq⟩
    refine ⟨ℓ, hℓ, ?_⟩
    filter_upwards [normalizedExponentialFamilyCurve_characteristic_eventuallyEq n c hc,
      hℓeq] with r hnorm hbase
    exact hnorm.trans hbase
  have hAdm : AdmissibleOrder n 1 :=
    ⟨0, 2, by decide, by omega, by norm_num⟩
  change MainConclusion w.curve
  exact w.mainConclusion (by norm_num) hAdm hreg hslow

theorem normalizedExponentialFamily_mainTheoremStatement
    {n : ℕ} (hn : 1 ≤ n) (c : ℂ) (hc : c ≠ 0)
    (hcpow : c ^ (n + 1) = (exponentialFamilyVandermonde n)⁻¹) :
    MainTheoremStatement (normalizedExponentialFamilyCurve n c hc) := by
  intro hn' htrans hlin hfinite hsmall
  exact mainConclusion_to_statement
    (normalizedExponentialFamily_mainConclusion hn c hc hcpow)
    hn' htrans hlin hfinite hsmall

end

end FewInflection
