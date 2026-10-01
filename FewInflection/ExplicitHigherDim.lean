import FewInflection.ExplicitExamples

open scoped BigOperators Topology
open Filter

namespace FewInflection

noncomputable section

def lastIndex (n : ℕ) : Index n :=
  ⟨n, Nat.lt_succ_self n⟩

/- A polynomial jet together with one exponential coordinate.  The factorial
  normalization makes the Wronskian exactly `exp`, without introducing a
  separate constant root. -/
def exponentialMonomialFamily (n : ℕ) (j : Index n) : ℂ → ℂ :=
  if j = lastIndex n then Complex.exp
  else fun z => (Nat.factorial (j : ℕ) : ℂ)⁻¹ * z ^ (j : ℕ)

def exponentialMonomialCurve (n : ℕ) : Curve n where
  coord := exponentialMonomialFamily n
  holomorphic := by
    intro j
    by_cases h : j = lastIndex n
    · simp only [exponentialMonomialFamily, h, ite_true]
      exact Complex.differentiable_exp
    · simp only [exponentialMonomialFamily, h, ite_false]
      fun_prop
  reduced := by
    intro z
    refine ⟨lastIndex n, ?_⟩
    simp [exponentialMonomialFamily]

theorem exponentialMonomialCurve_wronskian (n : ℕ) (z : ℂ) :
    wronskian n (exponentialMonomialCurve n).coord z = Complex.exp z := by
  unfold wronskian
  let M : Matrix (Index n) (Index n) ℂ := fun i j =>
    iteratedDeriv (i : ℕ) (exponentialMonomialFamily n j) z
  change M.det = Complex.exp z
  have hupper : M.IsUpperTriangular := by
    intro i j hij
    by_cases hlast : j = lastIndex n
    · subst j
      have hnot : ¬ n < (i : ℕ) := Nat.not_lt_of_ge (Nat.le_of_lt_succ i.isLt)
      exact False.elim (hnot hij)
    · dsimp [M]
      simp only [exponentialMonomialFamily, hlast, ite_false]
      change iteratedDeriv (i : ℕ)
        (fun x : ℂ => (Nat.factorial (j : ℕ) : ℂ)⁻¹ *
          x ^ (j : ℕ)) z = 0
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
      have hji : (j : ℕ) < (i : ℕ) := hij
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hji]
      simp
  have hdiag : ∀ i : Index n,
      M i i = if i = lastIndex n then Complex.exp z else 1 := by
    intro i
    by_cases hlast : i = lastIndex n
    · subst i
      simp [M, exponentialMonomialFamily, iteratedDeriv_eq_iterate,
        Complex.iter_deriv_exp]
    · have hfac : (Nat.factorial (i : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (i : ℕ)
      simp only [M, exponentialMonomialFamily, hlast, ite_false]
      change iteratedDeriv (i : ℕ)
        (fun x : ℂ => (Nat.factorial (i : ℕ) : ℂ)⁻¹ *
          x ^ (i : ℕ)) z = 1
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow,
        Nat.descFactorial_self]
      simp [hfac]
  rw [Matrix.det_of_isUpperTriangular hupper]
  simp_rw [hdiag]
  simp

theorem exponentialMonomialCurve_linearlyNonDegenerate (n : ℕ) :
    (exponentialMonomialCurve n).linearlyNonDegenerate := by
  unfold Curve.linearlyNonDegenerate
  apply linearlyIndependent_of_wronskian_ne_zero
    (exponentialMonomialCurve n).coord 0
  · intro i j
    exact ((exponentialMonomialCurve n).holomorphic j).contDiff.contDiffAt
  · rw [exponentialMonomialCurve_wronskian]
    exact Complex.exp_ne_zero _

theorem exponentialMonomialCurve_transcendental {n : ℕ} (hn : 1 ≤ n) :
    (exponentialMonomialCurve n).Transcendental := by
  intro hrep
  rcases hrep with ⟨p, g, hg, hgd, hrep⟩
  let p₀ : Polynomial ℂ := p 0
  have hzero : (0 : Index n) ≠ lastIndex n := by
    intro h
    have hv := congrArg (fun j : Index n => (j : ℕ)) h
    simp [lastIndex] at hv
    omega
  have hp₀_ne : ∀ z : ℂ, p₀.eval z ≠ 0 := by
    intro z hz
    have h0 := hrep 0 z
    change exponentialMonomialFamily n 0 z = g z * p₀.eval z at h0
    simp [exponentialMonomialFamily, hzero, hz] at h0
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
  have hrel : ∀ z : ℂ,
      (p (lastIndex n)).eval z = p₀.coeff 0 * Complex.exp z := by
    intro z
    have h0 := hrep 0 z
    have hlast := hrep (lastIndex n) z
    change exponentialMonomialFamily n 0 z = g z * p₀.eval z at h0
    change exponentialMonomialFamily n (lastIndex n) z =
      g z * (p (lastIndex n)).eval z at hlast
    simp only [exponentialMonomialFamily, ite_true] at hlast
    have h0' : (1 : ℂ) = g z * p₀.coeff 0 := by
      calc
        (1 : ℂ) = g z * p₀.eval z := by
          simpa [exponentialMonomialFamily, hzero] using h0
        _ = g z * p₀.coeff 0 := by rw [hp₀_const]; simp
    have hga : g z * p₀.coeff 0 = 1 := h0'.symm
    calc
      (p (lastIndex n)).eval z = 1 * (p (lastIndex n)).eval z := by ring
      _ = (g z * p₀.coeff 0) * (p (lastIndex n)).eval z := by rw [hga]
      _ = p₀.coeff 0 * (g z * (p (lastIndex n)).eval z) := by ring
      _ = p₀.coeff 0 * Complex.exp z := by rw [← hlast]
  apply complexExp_not_polynomial
    (Polynomial.C (p₀.coeff 0)⁻¹ * p (lastIndex n))
  intro z
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [hrel z]
  field_simp

private theorem exponentialMonomialCurve_zero_ne_last {n : ℕ} (hn : 1 ≤ n) :
    (0 : Index n) ≠ lastIndex n := by
  intro h
  have hv := congrArg (fun j : Index n => (j : ℕ)) h
  simp [lastIndex] at hv
  omega

theorem exponentialMonomialCurve_log_norm_lower {n : ℕ} (hn : 1 ≤ n)
    (z : ℂ) :
    max 0 z.re ≤ Real.log ‖(exponentialMonomialCurve n).vector z‖ := by
  have hzero : (0 : Index n) ≠ lastIndex n :=
    exponentialMonomialCurve_zero_ne_last hn
  have hcoord0 : (exponentialMonomialCurve n).coord 0 z = 1 := by
    simp [exponentialMonomialCurve, exponentialMonomialFamily, hzero]
  have hcoordlast :
      (exponentialMonomialCurve n).coord (lastIndex n) z = Complex.exp z := by
    simp [exponentialMonomialCurve, exponentialMonomialFamily]
  have hvpos : 0 < ‖(exponentialMonomialCurve n).vector z‖ :=
    norm_pos_iff.mpr ((exponentialMonomialCurve n).vector_ne_zero z)
  have hone : (1 : ℝ) ≤ ‖(exponentialMonomialCurve n).vector z‖ := by
    calc
      (1 : ℝ) = ‖(exponentialMonomialCurve n).coord 0 z‖ := by
        rw [hcoord0]
        norm_num
      _ ≤ ‖(exponentialMonomialCurve n).vector z‖ :=
        norm_le_pi_norm ((exponentialMonomialCurve n).vector z) 0
  have hexp : ‖Complex.exp z‖ ≤ ‖(exponentialMonomialCurve n).vector z‖ := by
    rw [← hcoordlast]
    exact norm_le_pi_norm ((exponentialMonomialCurve n).vector z) (lastIndex n)
  have hlogone : 0 ≤ Real.log ‖(exponentialMonomialCurve n).vector z‖ := by
    simpa using Real.log_nonneg hone
  have hlogexp : z.re ≤ Real.log ‖(exponentialMonomialCurve n).vector z‖ := by
    rw [Complex.norm_exp] at hexp
    exact (Real.le_log_iff_exp_le hvpos).2 hexp
  exact max_le hlogone hlogexp

theorem exponentialMonomialCurve_log_norm_upper {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r) {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) |r|) :
    Real.log ‖(exponentialMonomialCurve n).vector z‖ ≤ r := by
  have hnorm : ‖z‖ = r := by
    simpa [abs_of_nonneg hr] using (mem_sphere_zero_iff_norm.mp hz)
  have hre : z.re ≤ r := by
    exact le_trans (le_abs_self z.re)
      (le_trans (Complex.abs_re_le_norm z) (le_of_eq hnorm))
  have hcoord : ∀ j : Index n,
      ‖(exponentialMonomialCurve n).coord j z‖ ≤ Real.exp r := by
    intro j
    by_cases hlast : j = lastIndex n
    · subst j
      rw [show (exponentialMonomialCurve n).coord (lastIndex n) z =
        Complex.exp z by simp [exponentialMonomialCurve, exponentialMonomialFamily],
        Complex.norm_exp]
      exact Real.exp_le_exp.mpr hre
    · have hfac : 0 < (Nat.factorial (j : ℕ) : ℝ) := by positivity
      have hpow := Real.pow_div_factorial_le_exp r hr (j : ℕ)
      simp only [exponentialMonomialCurve, exponentialMonomialFamily,
        hlast, ite_false]
      rw [norm_mul, norm_inv, Complex.norm_natCast, norm_pow, hnorm]
      simpa [div_eq_mul_inv, mul_comm] using hpow
  have hvec : ‖(exponentialMonomialCurve n).vector z‖ ≤ Real.exp r :=
    (pi_norm_le_iff_of_nonempty _).2 hcoord
  exact (Real.log_le_iff_le_exp
    (norm_pos_iff.mpr ((exponentialMonomialCurve n).vector_ne_zero z))).2 hvec

theorem exponentialMonomialCurve_characteristic_bounds
    {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    r / 4 ≤ characteristic (exponentialMonomialCurve n) r ∧
      characteristic (exponentialMonomialCurve n) r ≤ r := by
  let F : ℂ → ℝ := fun z =>
    Real.log ‖(exponentialMonomialCurve n).vector z‖
  let H : ℂ → ℝ := fun z => max 0 z.re
  have hFcont : Continuous F := by
    dsimp [F]
    apply (continuous_pi (fun j =>
      ((exponentialMonomialCurve n).holomorphic j).continuous)).norm.log
    intro z
    exact norm_ne_zero_iff.mpr ((exponentialMonomialCurve n).vector_ne_zero z)
  have hHint : CircleIntegrable H 0 r := by
    have hHcont : Continuous H := by
      dsimp [H]
      fun_prop
    exact hHcont.continuousOn.circleIntegrable'
  have hFint : CircleIntegrable F 0 r :=
    hFcont.continuousOn.circleIntegrable'
  have hmono : Real.circleAverage H 0 r ≤ Real.circleAverage F 0 r := by
    apply Real.circleAverage_mono hHint hFint
    intro z hz
    exact exponentialMonomialCurve_log_norm_lower hn z
  have hplus : r / 4 ≤ Real.circleAverage H 0 r := by
    simpa [H, exponentialCurve_log_vector_norm] using
      (exponentialCurve_circleAverage_log_norm_ge hr)
  have hupper : Real.circleAverage F 0 r ≤ r := by
    apply Real.circleAverage_mono_on_of_le_circle hFint
    intro z hz
    exact exponentialMonomialCurve_log_norm_upper hr.le hz
  have hzero : Real.log ‖(exponentialMonomialCurve n).vector 0‖ = 0 := by
    have hlow := exponentialMonomialCurve_log_norm_lower hn 0
    have hz0 : (0 : ℂ) ∈ Metric.sphere (0 : ℂ) |(0 : ℝ)| := by
      simp
    have hupp := exponentialMonomialCurve_log_norm_upper (n := n) (r := 0) (by norm_num)
      hz0
    have hlow' : 0 ≤ Real.log ‖(exponentialMonomialCurve n).vector 0‖ := by
      simpa [H] using hlow
    have hupp' : Real.log ‖(exponentialMonomialCurve n).vector 0‖ ≤ 0 := by
      simpa using hupp
    exact le_antisymm hupp' hlow'
  unfold characteristic
  change r / 4 ≤ Real.circleAverage F 0 r -
      Real.log ‖(exponentialMonomialCurve n).vector 0‖ ∧
    Real.circleAverage F 0 r -
      Real.log ‖(exponentialMonomialCurve n).vector 0‖ ≤ r
  rw [hzero, sub_zero]
  exact ⟨hplus.trans hmono, hupper⟩

def normalizedExponentialMonomialCurve (n : ℕ) : Curve n :=
  (exponentialMonomialCurve n).scalarGauge
    (fun z : ℂ => Complex.exp (-z / ((n + 1 : ℕ) : ℂ)))
    (by intro z; exact Complex.exp_ne_zero _)
    (by fun_prop)

private theorem normalizedExponentialMonomialCurve_gauge_ne_zero (n : ℕ) :
    ∀ z : ℂ, Complex.exp (-z / ((n + 1 : ℕ) : ℂ)) ≠ 0 := by
  intro z
  exact Complex.exp_ne_zero _

private theorem normalizedExponentialMonomialCurve_gauge_diff (n : ℕ) :
    Differentiable ℂ (fun z : ℂ => Complex.exp (-z / ((n + 1 : ℕ) : ℂ))) := by
  fun_prop

theorem normalizedExponentialMonomialCurve_transcendental {n : ℕ} (hn : 1 ≤ n) :
    (normalizedExponentialMonomialCurve n).Transcendental := by
  apply (Curve.scalarGauge_transcendental_iff (exponentialMonomialCurve n)
    (fun z : ℂ => Complex.exp (-z / ((n + 1 : ℕ) : ℂ)))
    (normalizedExponentialMonomialCurve_gauge_ne_zero n)
    (normalizedExponentialMonomialCurve_gauge_diff n)).mp
  exact exponentialMonomialCurve_transcendental hn

theorem normalizedExponentialMonomialCurve_linearlyNonDegenerate (n : ℕ) :
    (normalizedExponentialMonomialCurve n).linearlyNonDegenerate := by
  apply (Curve.scalarGauge_linearlyNonDegenerate_iff (exponentialMonomialCurve n)
    (fun z : ℂ => Complex.exp (-z / ((n + 1 : ℕ) : ℂ)))
    (normalizedExponentialMonomialCurve_gauge_ne_zero n)
    (normalizedExponentialMonomialCurve_gauge_diff n)).mp
  exact exponentialMonomialCurve_linearlyNonDegenerate n

theorem normalizedExponentialMonomialCurve_wronskian_one (n : ℕ) (z : ℂ) :
    wronskian n (normalizedExponentialMonomialCurve n).coord z = 1 := by
  rw [normalizedExponentialMonomialCurve, Curve.scalarGauge_wronskian,
    exponentialMonomialCurve_wronskian]
  have hcast : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  calc
    Complex.exp (-z / ((n + 1 : ℕ) : ℂ)) ^ (n + 1) * Complex.exp z =
        Complex.exp (((n + 1 : ℕ) : ℂ) *
          (-z / ((n + 1 : ℕ) : ℂ))) * Complex.exp z := by
            rw [Complex.exp_nat_mul]
    _ = Complex.exp (((n + 1 : ℕ) : ℂ) *
          (-z / ((n + 1 : ℕ) : ℂ)) + z) := by
            rw [Complex.exp_add]
    _ = 1 := by
      rw [show ((n + 1 : ℕ) : ℂ) *
          (-z / ((n + 1 : ℕ) : ℂ)) + z = 0 by
            field_simp [hcast]
            ring]
      simp

theorem normalizedExponentialMonomialCurve_characteristic_eventuallyEq (n : ℕ) :
    characteristic (normalizedExponentialMonomialCurve n) =ᶠ[atTop]
      characteristic (exponentialMonomialCurve n) := by
  simpa [normalizedExponentialMonomialCurve] using
    (characteristic_scalarGauge_eventuallyEq
      (exponentialMonomialCurve n)
      (fun z : ℂ => Complex.exp (-z / ((n + 1 : ℕ) : ℂ)))
      (normalizedExponentialMonomialCurve_gauge_ne_zero n)
      (normalizedExponentialMonomialCurve_gauge_diff n))

def exponentialMonomialRealization {n : ℕ} (hn : 1 ≤ n) :
    RealizationWitness n 1 where
  curve := normalizedExponentialMonomialCurve n
  transcendental := normalizedExponentialMonomialCurve_transcendental hn
  linearlyNonDegenerate := normalizedExponentialMonomialCurve_linearlyNonDegenerate n
  wronskian_one := normalizedExponentialMonomialCurve_wronskian_one n
  two_sided_growth := by
    rcases eventually_atTop.mp
      (normalizedExponentialMonomialCurve_characteristic_eventuallyEq n) with
      ⟨R₀, hR₀⟩
    refine ⟨1 / 4, 1, max R₀ 1, by norm_num, by norm_num,
      lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right _ _) hr)
    have hEq : characteristic (normalizedExponentialMonomialCurve n) r =
        characteristic (exponentialMonomialCurve n) r :=
      hR₀ r (le_trans (le_max_left _ _) hr)
    have hb := exponentialMonomialCurve_characteristic_bounds hn hrpos
    have hpow : Real.rpow r (1 : ℝ) = r := by
      change r ^ (1 : ℝ) = r
      exact Real.rpow_one r
    rw [hpow]
    rw [hEq]
    constructor <;> linarith [hb.1, hb.2]

theorem exponentialMonomialRealization_sharpness_instance {n : ℕ} (hn : 1 ≤ n) :
    ∃ w : RealizationWitness n 1,
      w.curve.Transcendental ∧ w.curve.linearlyNonDegenerate ∧
      (∀ z, wronskian n w.curve.coord z = 1) := by
  refine ⟨exponentialMonomialRealization hn, ?_, ?_, ?_⟩
  · exact (exponentialMonomialRealization hn).transcendental
  · exact (exponentialMonomialRealization hn).linearlyNonDegenerate
  · exact (exponentialMonomialRealization hn).wronskian_one

end

end FewInflection
