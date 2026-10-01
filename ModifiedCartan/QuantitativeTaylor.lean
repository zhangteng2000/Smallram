import FewInflection.EntireTaylor
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.SpecificLimits.Basic
import ModifiedCartan.NormComparison
import Mathlib.Algebra.Order.Floor.Semiring

open scoped Topology BigOperators
open Filter Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem norm_taylor_coefficient_le {f : ℂ → ℂ} {a : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (closedBall a R))
    (hM : ∀ z ∈ sphere a R, ‖f z‖ ≤ M) (k : ℕ) :
    ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k f a‖ ≤ M / R ^ k := by
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR
    (hf.diffContOnCl_ball subset_rfl) hM
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (k.factorial : ℝ)⁻¹ * ((k.factorial : ℝ) * M / R ^ k) := by gcongr
    _ = _ := by field_simp

theorem norm_taylor_term_le {f : ℂ → ℂ} {a : ℂ} {R r M : ℝ}
    (hR : 0 < R) (_hr : 0 ≤ r) (hM0 : 0 ≤ M)
    (hf : DifferentiableOn ℂ f (closedBall a R))
    (hM : ∀ z ∈ sphere a R, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall a r) (k : ℕ) :
    ‖(k.factorial : ℂ)⁻¹ * iteratedDeriv k f a * (z - a) ^ k‖ ≤ M * (r / R) ^ k := by
  have hz' : ‖z - a‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (M / R ^ k) * r ^ k := by
      gcongr
      exact norm_taylor_coefficient_le hR hf hM k
    _ = _ := by rw [div_pow]; ring

theorem norm_taylorPolynomial_sub_le {f : ℂ → ℂ} {a : ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) (hM0 : 0 ≤ M)
    (hf : DifferentiableOn ℂ f (closedBall a R))
    (hM : ∀ z ∈ sphere a R, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall a r) (N : ℕ) :
    ‖(FewInflection.taylorPolynomial f a N).eval z - f z‖ ≤
      M * (r / R) ^ N / (1 - r / R) := by
  let term : ℕ → ℂ := fun k => (k.factorial : ℂ)⁻¹ * iteratedDeriv k f a * (z - a) ^ k
  have hseries : HasSum term (f z) := by
    have h := Complex.hasSum_taylorSeries_on_ball
      (hf.mono ball_subset_closedBall) ((closedBall_subset_ball hrR) hz)
    convert! h using 1
    funext k
    simp only [term, smul_eq_mul]
    ring
  have htail : HasSum (fun k => term (k + N)) (f z - ∑ k ∈ Finset.range N, term k) := by
    apply (hasSum_nat_add_iff N).mpr
    simpa only [sub_add_cancel] using hseries
  have hgeom : HasSum (fun k : ℕ => M * (r / R) ^ (k + N))
      (M * (r / R) ^ N / (1 - r / R)) := by
    have h := (hasSum_geometric_of_lt_one (div_nonneg hr hR.le)
      ((div_lt_one hR).mpr hrR)).mul_left (M * (r / R) ^ N)
    convert! h using 1
    · funext k
      rw [pow_add]
      ring
  have hbound := htail.norm_le_of_bounded hgeom
    (fun k => norm_taylor_term_le hR hr hM0 hf hM hz (k + N))
  rw [norm_sub_rev, FewInflection.taylorPolynomial_eval_eq_sum]
  exact hbound

theorem taylorPolynomial_natDegree_le (f : ℂ → ℂ) (a : ℂ) (N : ℕ) :
    (FewInflection.taylorPolynomial f a N).natDegree ≤ N := by
  unfold FewInflection.taylorPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_pow_le.trans
  simpa only [Polynomial.natDegree_X_sub_C, mul_one] using
    (Finset.mem_range.mp hk).le

theorem norm_taylor_remainder_disk {f : ℂ → ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (ball 0 32))
    (hM : ∀ z ∈ ball (0 : ℂ) 32, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall 0 20) (N : ℕ) :
    ‖(FewInflection.taylorPolynomial f 0 N).eval z - f z‖ ≤
      6 * M * (5 / 6 : ℝ) ^ N := by
  have hfc : DifferentiableOn ℂ f (closedBall 0 24) :=
    hf.differentiableOn.mono (closedBall_subset_ball (by norm_num))
  have hsphere : ∀ z ∈ sphere (0 : ℂ) 24, ‖f z‖ ≤ M := by
    intro w hw
    exact hM w ((closedBall_subset_ball (by norm_num : (24 : ℝ) < 32))
      (sphere_subset_closedBall hw))
  calc
    _ ≤ M * ((20 : ℝ) / 24) ^ N / (1 - (20 : ℝ) / 24) :=
      norm_taylorPolynomial_sub_le (by norm_num) (by norm_num) (by norm_num)
        hM0 hfc hsphere hz N
    _ = _ := by norm_num; ring

theorem norm_taylor_derivative_remainder_disk {f : ℂ → ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (ball 0 32))
    (hM : ∀ z ∈ ball (0 : ℂ) 32, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall 0 16) (N k : ℕ) :
    ‖iteratedDeriv k (fun w => (FewInflection.taylorPolynomial f 0 N).eval w) z -
        iteratedDeriv k f z‖ ≤
      k.factorial * (6 * M * (5 / 6 : ℝ) ^ N) / 2 ^ k := by
  let p := FewInflection.taylorPolynomial f 0 N
  have hsub : closedBall z 2 ⊆ closedBall (0 : ℂ) 20 := by
    intro w hw
    have hw' : ‖w - z‖ ≤ 2 := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hz' : ‖z‖ ≤ 16 := by simpa only [mem_closedBall, dist_zero_right] using hz
    rw [mem_closedBall, dist_zero_right]
    have ht : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa only [sub_add_cancel] using norm_add_le (w - z) z
    linarith
  have hd : DifferentiableOn ℂ (fun w => p.eval w - f w) (ball 0 32) :=
    p.differentiable.differentiableOn.sub hf.differentiableOn
  have he := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by norm_num : (0 : ℝ) < 2)
    (hd.diffContOnCl_ball (hsub.trans (closedBall_subset_ball (by norm_num))))
    (fun w hw => norm_taylor_remainder_disk hM0 hf hM (hsub (sphere_subset_closedBall hw)) N)
  have hz32 : z ∈ ball (0 : ℂ) 32 := (closedBall_subset_ball (by norm_num)) hz
  rw [iteratedDeriv_fun_sub
    (AnalyticOnNhd.eval_polynomial p z (mem_univ z)).contDiffAt (hf z hz32).contDiffAt] at he
  exact he

theorem norm_taylor_derivative_remainder_le_factorial {f : ℂ → ℂ} {M : ℝ}
    (hM0 : 0 ≤ M) (hf : AnalyticOnNhd ℂ f (ball 0 32))
    (hM : ∀ z ∈ ball (0 : ℂ) 32, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall 0 16) (N : ℕ) {k m : ℕ} (hkm : k ≤ m) :
    ‖iteratedDeriv k (fun w => (FewInflection.taylorPolynomial f 0 N).eval w) z -
        iteratedDeriv k f z‖ ≤
      (6 * m.factorial : ℝ) * M * (5 / 6 : ℝ) ^ N := by
  have hfac : (k.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hkm
  have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  calc
    _ ≤ k.factorial * (6 * M * (5 / 6 : ℝ) ^ N) / 2 ^ k :=
      norm_taylor_derivative_remainder_disk hM0 hf hM hz N k
    _ ≤ k.factorial * (6 * M * (5 / 6 : ℝ) ^ N) :=
      div_le_self (by positivity) hpow
    _ ≤ m.factorial * (6 * M * (5 / 6 : ℝ) ^ N) := by gcongr
    _ = _ := by ring

end ModifiedCartan
