import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Tactic

/-!
# Kernel bounds for the fixed-radius logarithmic derivative estimate

These estimates are Step 3 of the paper's fixed-radius lemma. They concern
the actual complex kernels, with every denominator justified geometrically.
-/

open scoped BigOperators ComplexConjugate Topology
open Filter
open Complex

namespace FewInflection

/-- Distance from an interior point to a circle, in the form needed for
derivatives of the Poisson kernel. -/
theorem circle_kernel_denominator_lower_bound
    {R : ℝ} (hR : 0 ≤ R) (z : ℂ) (θ : ℝ) :
    R - ‖z‖ ≤ ‖(R : ℂ) * Complex.exp (θ * Complex.I) - z‖ := by
  have hmul : ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ = R := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  simpa only [hmul] using
    (norm_sub_norm_le ((R : ℂ) * Complex.exp (θ * Complex.I)) z)

/-- The rational expression for a Poisson-kernel derivative is uniformly
bounded on the unit circle when the integration radius lies in `(2,3)`. -/
theorem poisson_derivative_kernel_bound
    (m : ℕ) {R : ℝ} {z : ℂ} (hR2 : 2 < R) (hR3 : R < 3)
    (hz : ‖z‖ = 1) (θ : ℝ) :
    ‖(2 : ℂ) * (Nat.factorial m : ℂ) * (R : ℂ) *
        Complex.exp (θ * Complex.I) /
        ((R : ℂ) * Complex.exp (θ * Complex.I) - z) ^ (m + 1)‖ ≤
      6 * (Nat.factorial m : ℝ) := by
  have hR0 : 0 ≤ R := by linarith
  have hden : 1 < ‖(R : ℂ) * Complex.exp (θ * Complex.I) - z‖ := by
    have h := circle_kernel_denominator_lower_bound hR0 z θ
    rw [hz] at h
    linarith
  have hden0 : 0 < ‖(R : ℂ) * Complex.exp (θ * Complex.I) - z‖ :=
    lt_trans (by norm_num) hden
  have hdenpow : 1 ≤ ‖(R : ℂ) * Complex.exp (θ * Complex.I) - z‖ ^ (m + 1) :=
    one_le_pow₀ hden.le
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat,
    norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0,
    norm_exp_ofReal_mul_I, mul_one]
  have hfac : 0 ≤ (Nat.factorial m : ℝ) := by positivity
  apply (div_le_iff₀ (pow_pos hden0 _)).2
  nlinarith [mul_nonneg hfac (sub_nonneg.mpr hR3.le),
    mul_nonneg hfac (sub_nonneg.mpr hdenpow)]

/-- Iterated derivatives of the reciprocal of an affine coordinate. -/
theorem iteratedDeriv_sub_inv (m : ℕ) (a z : ℂ) :
    iteratedDeriv m (fun x : ℂ => (a - x)⁻¹) z =
      (Nat.factorial m : ℂ) / (a - z) ^ (m + 1) := by
  rw [iteratedDeriv_comp_const_sub]
  dsimp only
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
  simp only [smul_eq_mul]
  have hint : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by omega
  rw [hint, zpow_neg, zpow_natCast]
  have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℂ)^m * ((-1 : ℂ)^m * (Nat.factorial m : ℂ) * ((a-z)^(m+1))⁻¹) =
        ((-1 : ℂ)^m * (-1 : ℂ)^m) * ((Nat.factorial m : ℂ) * ((a-z)^(m+1))⁻¹) := by ring
    _ = _ := by rw [hsign]; simp [div_eq_mul_inv]

/-- Exact derivatives of the singular kernel appearing in the zero/pole
term of the Poisson--Jensen formula. -/
theorem iteratedDeriv_singular_fraction (m : ℕ) (a z : ℂ) :
    iteratedDeriv m (fun w : ℂ => (w - a)⁻¹) z =
      (-1 : ℂ)^m * (Nat.factorial m : ℂ) /
        (z - a) ^ (m + 1) := by
  rw [iteratedDeriv_eq_iterate]
  have h := congrFun (iter_deriv_inv_linear m 1 (-a)) z
  have hint : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by omega
  rw [hint, zpow_neg, zpow_natCast] at h
  simpa [sub_eq_add_neg, div_eq_mul_inv] using h

/-- Finite sums of the singular kernels may be differentiated term by term
away from their poles. -/
theorem iteratedDeriv_singular_sum
    {ι : Type*} (s : Finset ι) (a c : ι → ℂ) (m : ℕ) {z : ℂ}
    (hz : ∀ i ∈ s, a i ≠ z) :
    iteratedDeriv m (fun w : ℂ => ∑ i ∈ s, c i * (w - a i)⁻¹) z =
      ∑ i ∈ s, c i *
        ((-1 : ℂ)^m * (Nat.factorial m : ℂ) /
          (z - a i)^(m + 1)) := by
  rw [iteratedDeriv_fun_sum]
  · simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_singular_fraction]
  · intro i hi
    have hzi : z - a i ≠ 0 := sub_ne_zero.mpr (hz i hi).symm
    fun_prop

/-- The higher derivative of the scalar Poisson rational kernel. -/
theorem iteratedDeriv_poisson_fraction
    (m : ℕ) {a z : ℂ} (hm : 1 ≤ m) (haz : a ≠ z) :
    iteratedDeriv m (fun w : ℂ => (a + w) / (a - w)) z =
      2 * (Nat.factorial m : ℂ) * a / (a - z) ^ (m + 1) := by
  have heq : (fun w : ℂ => (a + w) / (a - w)) =ᶠ[𝓝 z]
      (fun w => -1 + (2*a) * (a-w)⁻¹) := by
    filter_upwards [continuousAt_id.eventually_ne haz.symm] with w hw
    have hw' : w ≠ a := by simpa only [id_eq] using hw
    field_simp [sub_ne_zero.mpr hw']
    ring
  rw [heq.iteratedDeriv_eq m, iteratedDeriv_const_add (Nat.zero_lt_of_lt hm),
    iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_sub_inv]
  field_simp

/-- The previous identity and the geometric denominator estimate give the
uniform bound used for the differentiated Poisson integral. -/
theorem norm_iteratedDeriv_poisson_fraction_bound
    (m : ℕ) {R : ℝ} {z : ℂ} (hm : 1 ≤ m) (hR2 : 2 < R) (hR3 : R < 3)
    (hz : ‖z‖ = 1) (θ : ℝ) :
    ‖iteratedDeriv m
      (fun w : ℂ => ((R : ℂ) * Complex.exp (θ * Complex.I) + w) /
        ((R : ℂ) * Complex.exp (θ * Complex.I) - w)) z‖ ≤
      6 * (Nat.factorial m : ℝ) := by
  have hR0 : 0 ≤ R := by linarith
  have hbound := circle_kernel_denominator_lower_bound hR0 z θ
  rw [hz] at hbound
  have hne : (R : ℂ) * Complex.exp (θ * Complex.I) ≠ z := by
    intro heq
    rw [heq] at hbound
    simp only [sub_self, norm_zero] at hbound
    linarith
  rw [iteratedDeriv_poisson_fraction m hm hne]
  simpa only [mul_assoc] using
    poisson_derivative_kernel_bound m hR2 hR3 hz θ

/-- The boundary integral of a higher Poisson kernel derivative is controlled
by the absolute boundary mean. No exceptional radius is used in this bound. -/
theorem norm_integral_poisson_derivative_le
    (m : ℕ) {R : ℝ} {z : ℂ} {g : ℝ → ℝ}
    (hm : 1 ≤ m) (hR2 : 2 < R) (hR3 : R < 3) (hz : ‖z‖ = 1)
    (hg : IntervalIntegrable g MeasureTheory.volume (-Real.pi) Real.pi) :
    ‖∫ θ in (-Real.pi)..Real.pi,
      (iteratedDeriv m
        (fun w : ℂ => ((R : ℂ) * Complex.exp (θ * Complex.I) + w) /
          ((R : ℂ) * Complex.exp (θ * Complex.I) - w)) z) * (g θ : ℂ)‖ ≤
      (6 * (Nat.factorial m : ℝ)) *
        ∫ θ in (-Real.pi)..Real.pi, |g θ| := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith [Real.pi_pos])
  · apply Filter.Eventually.of_forall
    intro θ _hθ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (norm_iteratedDeriv_poisson_fraction_bound m hm hR2 hR3 hz θ) (abs_nonneg _)
  · exact hg.abs.const_mul _

/-- The reflected kernel is bounded uniformly for points in the integration
disk. The estimate is valid on the whole closed unit disk. -/
theorem reflected_kernel_bound
    {R : ℝ} {a z : ℂ} (hR : 1 < R) (ha : ‖a‖ < R) (hz : ‖z‖ ≤ 1) :
    ‖conj a / ((R : ℂ) ^ 2 - conj a * z)‖ ≤ (R - 1)⁻¹ := by
  have hR0 : 0 < R := by linarith
  have hgeom := norm_sub_norm_le ((R : ℂ) ^ 2) (conj a * z)
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hR0, norm_mul, norm_conj] at hgeom
  have haz : ‖a‖ * ‖z‖ ≤ ‖a‖ := by nlinarith [norm_nonneg a]
  have hden0 : 0 < ‖(R : ℂ) ^ 2 - conj a * z‖ := by
    nlinarith [mul_pos hR0 (sub_pos.mpr hR)]
  rw [norm_div, norm_conj, inv_eq_one_div]
  apply (div_le_div_iff₀ hden0 (sub_pos.mpr hR)).2
  nlinarith [mul_pos hR0 (sub_pos.mpr ha)]

/-- Points in the unit disk cannot be poles of the reflected kernel when the
integration radius is larger than two. -/
theorem reflected_denominator_ne_zero
    {R : ℝ} {a z : ℂ} (hR : 1 < R)
    (ha : ‖a‖ < R) (hz : ‖z‖ ≤ 1) :
    (R : ℂ) ^ 2 - conj a * z ≠ 0 := by
  have hR0 : 0 < R := by linarith
  have hgeom := norm_sub_norm_le ((R : ℂ) ^ 2) (conj a * z)
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hR0, norm_mul, norm_conj] at hgeom
  have haz : ‖a‖ * ‖z‖ ≤ ‖a‖ := by nlinarith [norm_nonneg a]
  have hpos : 0 < R ^ 2 - ‖a‖ := by
    nlinarith [mul_pos hR0 (sub_pos.mpr hR), mul_pos hR0 (sub_pos.mpr ha)]
  intro hzero
  rw [hzero] at hgeom
  simp only [norm_zero] at hgeom
  linarith

/-- Every positive integral power of a reflected kernel is bounded by one
for integration radii above two. -/
theorem reflected_kernel_pow_le_one
    (k : ℕ) {R : ℝ} {a z : ℂ}
    (hR : 2 < R) (ha : ‖a‖ < R) (hz : ‖z‖ ≤ 1) :
    ‖conj a ^ k / ((R : ℂ) ^ 2 - conj a * z) ^ k‖ ≤ 1 := by
  rw [← div_pow, norm_pow]
  have hR1 : 1 < R := by linarith
  have hbase := reflected_kernel_bound hR1 ha hz
  have hinv : (R - 1)⁻¹ ≤ 1 :=
    (inv_le_one₀ (sub_pos.mpr hR1)).2 (by linarith)
  exact pow_le_one₀ (norm_nonneg _) (hbase.trans hinv)

/-- Exact derivatives of the reflected Poisson--Jensen kernel. -/
theorem iteratedDeriv_reflected_fraction
    (m : ℕ) {a R z : ℂ} :
    iteratedDeriv m (fun w : ℂ => conj a / (R ^ 2 - conj a * w)) z =
      (Nat.factorial m : ℂ) * (conj a) ^ (m + 1) /
        (R ^ 2 - conj a * z) ^ (m + 1) := by
  simp only [div_eq_mul_inv]
  rw [iteratedDeriv_const_mul_field]
  have hder : iteratedDeriv m (fun w : ℂ => (R ^ 2 - conj a * w)⁻¹) z =
      (-1 : ℂ)^m * (Nat.factorial m : ℂ) * (-conj a)^m *
        (R^2 - conj a*z)^(-1-(m:ℤ)) := by
    rw [iteratedDeriv_eq_iterate]
    simpa [sub_eq_add_neg, add_comm] using
      congrFun (iter_deriv_inv_linear m (-conj a) (R^2)) z
  rw [hder]
  have hint : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by omega
  rw [hint, zpow_neg, zpow_natCast]
  have hsign : (-1 : ℂ) ^ m * (-conj a) ^ m = (conj a) ^ m := by
    rw [← mul_pow]
    simp
  have hprod : (-1 : ℂ)^m * (Nat.factorial m : ℂ) * (-conj a)^m =
      (Nat.factorial m : ℂ) * (conj a)^m := by
    calc
      (-1 : ℂ)^m * (Nat.factorial m : ℂ) * (-conj a)^m =
          (Nat.factorial m : ℂ) * ((-1 : ℂ)^m * (-conj a)^m) := by ring
      _ = _ := by rw [hsign]
  rw [hprod]
  field_simp
  ring

/-- Finite reflected kernels may likewise be differentiated term by term away
from their denominators' zero set. -/
theorem iteratedDeriv_reflected_sum
    {ι : Type*} (s : Finset ι) (a c : ι → ℂ) (R : ℂ) (m : ℕ) {z : ℂ}
    (hz : ∀ i ∈ s, R ^ 2 - conj (a i) * z ≠ 0) :
    iteratedDeriv m
      (fun w : ℂ => ∑ i ∈ s,
        c i * (conj (a i) / (R ^ 2 - conj (a i) * w))) z =
      ∑ i ∈ s, c i *
        ((Nat.factorial m : ℂ) * (conj (a i)) ^ (m + 1) /
          (R ^ 2 - conj (a i) * z) ^ (m + 1)) := by
  rw [iteratedDeriv_fun_sum]
  · simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_reflected_fraction]
  · intro i hi
    have hzi := hz i hi
    fun_prop

/-- The reflected derivative is bounded by the factorial on the unit disk. -/
theorem norm_iteratedDeriv_reflected_fraction_le
    (m : ℕ) {R : ℝ} {a z : ℂ} (hR : 2 < R)
    (ha : ‖a‖ < R) (hz : ‖z‖ ≤ 1) :
    ‖iteratedDeriv m
      (fun w : ℂ => conj a / ((R : ℂ) ^ 2 - conj a * w)) z‖ ≤
      (Nat.factorial m : ℝ) := by
  rw [iteratedDeriv_reflected_fraction]
  have hk := reflected_kernel_pow_le_one (m + 1) hR ha hz
  calc
    ‖(Nat.factorial m : ℂ) *
        (conj a) ^ (m + 1) /
          ((R : ℂ) ^ 2 - conj a * z) ^ (m + 1)‖ =
        (Nat.factorial m : ℝ) *
          ‖(conj a) ^ (m + 1) /
            ((R : ℂ) ^ 2 - conj a * z) ^ (m + 1)‖ := by
      simp [norm_div, norm_mul, Complex.norm_natCast, div_eq_mul_inv,
        mul_assoc]
    _ ≤ (Nat.factorial m : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    _ = (Nat.factorial m : ℝ) := by ring

/-- Reflected terms, with their integer multiplicities, are bounded by the
total absolute multiplicity. -/
theorem reflected_kernel_sum_bound
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ν : ι → ℤ) (k : ℕ)
    {R : ℝ} {z : ℂ} (hR : 2 < R)
    (ha : ∀ i ∈ s, ‖a i‖ < R) (hz : ‖z‖ ≤ 1) :
    ‖∑ i ∈ s, (ν i : ℂ) *
      (conj (a i) ^ k / ((R : ℂ) ^ 2 - conj (a i) * z) ^ k)‖ ≤
      ∑ i ∈ s, |(ν i : ℝ)| := by
  apply norm_sum_le_of_le
  intro i hi
  rw [norm_mul, Complex.norm_intCast]
  exact mul_le_of_le_one_right (abs_nonneg _) (reflected_kernel_pow_le_one k hR (ha i hi) hz)

/-! The same estimate after taking an arbitrary iterated derivative.  This is
  the finite-singular-sum piece used in the fixed-radius logarithmic
  derivative argument. -/
theorem norm_iteratedDeriv_reflected_sum_le
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ν : ι → ℤ) (m : ℕ)
    {R : ℝ} {z : ℂ} (hR : 2 < R)
    (ha : ∀ i ∈ s, ‖a i‖ < R) (hz : ‖z‖ ≤ 1) :
    ‖iteratedDeriv m
      (fun w : ℂ => ∑ i ∈ s, (ν i : ℂ) *
        (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w))) z‖ ≤
      (Nat.factorial m : ℝ) * ∑ i ∈ s, |(ν i : ℝ)| := by
  have hden : ∀ i ∈ s,
      (R : ℂ) ^ 2 - conj (a i) * z ≠ 0 := by
    intro i hi
    exact reflected_denominator_ne_zero (by linarith) (ha i hi) hz
  rw [iteratedDeriv_reflected_sum s a (fun i => (ν i : ℂ))
    (R : ℂ) m hden]
  calc
    ‖∑ i ∈ s,
        (ν i : ℂ) *
          ((Nat.factorial m : ℂ) * (conj (a i)) ^ (m + 1) /
            ((R : ℂ) ^ 2 - conj (a i) * z) ^ (m + 1))‖ ≤
      ∑ i ∈ s, (Nat.factorial m : ℝ) * |(ν i : ℝ)| := by
        apply norm_sum_le_of_le
        intro i hi
        have hfrac := norm_iteratedDeriv_reflected_fraction_le m hR (ha i hi) hz
        rw [iteratedDeriv_reflected_fraction] at hfrac
        calc
          ‖(ν i : ℂ) *
              ((Nat.factorial m : ℂ) * (conj (a i)) ^ (m + 1) /
                ((R : ℂ) ^ 2 - conj (a i) * z) ^ (m + 1))‖ =
              |(ν i : ℝ)| *
                ‖(Nat.factorial m : ℂ) * (conj (a i)) ^ (m + 1) /
                  ((R : ℂ) ^ 2 - conj (a i) * z) ^ (m + 1)‖ := by
                simp [norm_mul, Complex.norm_intCast, Real.norm_eq_abs]
          _ ≤ |(ν i : ℝ)| * (Nat.factorial m : ℝ) := by
            exact mul_le_mul_of_nonneg_left hfrac (abs_nonneg _)
          _ = (Nat.factorial m : ℝ) * |(ν i : ℝ)| := by ring
    _ = (Nat.factorial m : ℝ) * ∑ i ∈ s, |(ν i : ℝ)| := by
      rw [Finset.mul_sum]

/-! A corresponding estimate for the ordinary singular kernels.  The
    separation parameter `δ` is kept explicit so that this bound can be
    instantiated on any compact set avoiding the finite pole set. -/
theorem norm_iteratedDeriv_singular_sum_le
    {ι : Type*} (s : Finset ι) (a c : ι → ℂ) (m : ℕ)
    {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, δ ≤ ‖z - a i‖) :
    ‖iteratedDeriv m
      (fun w : ℂ => ∑ i ∈ s, c i * (w - a i)⁻¹) z‖ ≤
      (Nat.factorial m : ℝ) * (δ⁻¹) ^ (m + 1) *
        ∑ i ∈ s, ‖c i‖ := by
  have hne : ∀ i ∈ s, a i ≠ z := by
    intro i hi hazi
    subst z
    have hnorm : ‖a i - a i‖ = 0 := by simp
    linarith [hsep i hi]
  rw [iteratedDeriv_singular_sum s a c m hne]
  calc
    ‖∑ i ∈ s, c i *
        ((-1 : ℂ)^m * (Nat.factorial m : ℂ) /
          (z - a i) ^ (m + 1))‖ ≤
      ∑ i ∈ s, (Nat.factorial m : ℝ) * (δ⁻¹) ^ (m + 1) * ‖c i‖ := by
        apply norm_sum_le_of_le
        intro i hi
        have hnorm := hsep i hi
        have hnormpos : 0 < ‖z - a i‖ := lt_of_lt_of_le hδ hnorm
        have hδinv : (‖z - a i‖)⁻¹ ≤ δ⁻¹ := by
          exact (inv_le_inv₀ hnormpos hδ).2 hnorm
        have hpow : (‖z - a i‖)⁻¹ ^ (m + 1) ≤ (δ⁻¹) ^ (m + 1) := by
          exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hδinv _
        calc
          ‖c i * ((-1 : ℂ)^m * (Nat.factorial m : ℂ) /
              (z - a i) ^ (m + 1))‖ =
              ‖c i‖ * (Nat.factorial m : ℝ) *
                (‖z - a i‖⁻¹) ^ (m + 1) := by
            simp [norm_mul, norm_div, norm_pow, Complex.norm_natCast,
              div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          _ ≤ ‖c i‖ * (Nat.factorial m : ℝ) *
                (δ⁻¹) ^ (m + 1) := by
            exact mul_le_mul_of_nonneg_left hpow
              (mul_nonneg (norm_nonneg _) (by positivity))
          _ = (Nat.factorial m : ℝ) * (δ⁻¹) ^ (m + 1) * ‖c i‖ := by ring
    _ = (Nat.factorial m : ℝ) * (δ⁻¹) ^ (m + 1) *
          ∑ i ∈ s, ‖c i‖ := by
      rw [Finset.mul_sum]

end FewInflection
