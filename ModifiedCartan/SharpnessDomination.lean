import ModifiedCartan.SharpnessDerivativeBounds
import ModifiedCartan.DeterminantRowBounds

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem IsSharpnessSystem.vector_norm_le {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 2 ≤ q) (hqn : q ≤ n + 1) {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖fun j => g j z‖ ≤ Real.exp (R ^ (1 + (k : ℝ) / q)) := by
  apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr
  intro j
  simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, Real.rpow_zero, one_mul,
    iteratedDeriv_zero] using h.derivative_norm_le hq hqn hR hz (0 : Index n) j

theorem IsSharpnessSystem.derivative_norm_le_uniform {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 2 ≤ q) (hqn : q ≤ n + 1) {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (i j : Index n) :
    ‖iteratedDeriv i.val (g j) z‖ ≤
      R ^ ((n : ℝ) * ((k : ℝ) / q)) * Real.exp (R ^ (1 + (k : ℝ) / q)) := by
  apply (h.derivative_norm_le hq hqn hR hz i j).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply Real.rpow_le_rpow_of_exponent_le hR
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast (show i.val ≤ n by have := i.isLt; omega)

theorem IsSharpnessSystem.log_vector_norm_bounds {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 2 ≤ q) (hqn : q ≤ n + 1) {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    -Real.log ((n + 1).factorial : ℝ) -
        n * ((n : ℝ) * ((k : ℝ) / q) * Real.log R + R ^ (1 + (k : ℝ) / q)) ≤
      Real.log (euclideanNorm (fun j => g j z)) ∧
    Real.log (euclideanNorm (fun j => g j z)) ≤
      Real.log (Real.sqrt (n + 1)) + R ^ (1 + (k : ℝ) / q) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hv : (fun j => g j z) ≠ 0 := (h.curve hq hqn).vector_ne_zero z
  have hnorm : 0 < ‖fun j => g j z‖ := norm_pos_iff.mpr hv
  let B : ℝ := R ^ ((n : ℝ) * ((k : ℝ) / q)) * Real.exp (R ^ (1 + (k : ℝ) / q))
  have hB : 0 < B := by dsimp [B]; positivity
  have hlogB : Real.log B =
      (n : ℝ) * ((k : ℝ) / q) * Real.log R + R ^ (1 + (k : ℝ) / q) := by
    dsimp [B]
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow hRp, Real.log_exp]
  have hdet := norm_matrix_det_le_zero_row
    (fun i j : Index n => iteratedDeriv i.val (g j) z) hB.le
    (fun i j _ => h.derivative_norm_le_uniform hq hqn hR hz i j)
  change ‖FewInflection.wronskian n g z‖ ≤
    ((n + 1).factorial : ℝ) * ‖fun j => iteratedDeriv (0 : Index n).val (g j) z‖ * B ^ n at hdet
  simp only [h.wronskian_one hq hqn z, norm_one, Fin.val_zero, iteratedDeriv_zero] at hdet
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hlower := Real.log_nonneg hdet
  rw [Real.log_mul (mul_pos hfac hnorm).ne' (pow_pos hB n).ne',
    Real.log_mul hfac.ne' hnorm.ne', Real.log_pow, hlogB] at hlower
  have hlu := log_norm_le_log_euclideanNorm hv
  have hupper := Real.log_le_log hnorm (h.vector_norm_le hq hqn hR hz)
  rw [Real.log_exp] at hupper
  have hue := log_euclideanNorm_le hv
  constructor <;> linarith

/-- LaTeX `eq:sharpness-domination`. Uniform absolute log-norm control on
whole disks, hence in particular on every circle and every direction. -/
theorem IsSharpnessSystem.abs_log_vector_norm_le {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 2 ≤ q) (hqn : q ≤ n + 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ ≤ R →
      |Real.log (euclideanNorm (fun j => g j z))| ≤ C * R ^ (1 + (k : ℝ) / q) := by
  let β : ℝ := (k : ℝ) / q
  let L : ℝ := |Real.log ((n + 1).factorial : ℝ)| + n * ((n : ℝ) * β + 1)
  let U : ℝ := |Real.log (Real.sqrt (n + 1))| + 1
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  refine ⟨L + U, by linarith, ?_⟩
  intro R hR z hz
  let S : ℝ := R ^ (1 + β)
  have hS : 1 ≤ S := Real.one_le_rpow hR (by positivity)
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hRS : R ≤ S := by
    calc
      R = R ^ (1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ S := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hlR : Real.log R ≤ S :=
    (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hR)).trans (by linarith)
  have hfc : Real.log ((n + 1).factorial : ℝ) ≤ |Real.log ((n + 1).factorial : ℝ)| * S :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hS)
  have hsc : Real.log (Real.sqrt (n + 1)) ≤ |Real.log (Real.sqrt (n + 1))| * S :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hS)
  have hb := h.log_vector_norm_bounds hq hqn hR hz
  change -Real.log ((n + 1).factorial : ℝ) - n * ((n : ℝ) * β * Real.log R + S) ≤
    Real.log (euclideanNorm (fun j => g j z)) ∧
    Real.log (euclideanNorm (fun j => g j z)) ≤ Real.log (Real.sqrt (n + 1)) + S at hb
  have hinner : (n : ℝ) * β * Real.log R + S ≤ ((n : ℝ) * β + 1) * S := by
    have hm := mul_le_mul_of_nonneg_left hlR (mul_nonneg (Nat.cast_nonneg n) hβ)
    nlinarith
  have htotal : Real.log ((n + 1).factorial : ℝ) +
      n * ((n : ℝ) * β * Real.log R + S) ≤ L * S := by
    calc
      _ ≤ |Real.log ((n + 1).factorial : ℝ)| * S + n * (((n : ℝ) * β + 1) * S) :=
        add_le_add hfc (mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg n))
      _ = L * S := by dsimp [L]; ring
  apply abs_le.mpr
  constructor
  · have hLU : L * S ≤ (L + U) * S := by nlinarith
    change -((L + U) * S) ≤ _
    linarith [hb.1]
  · have hUU : U * S ≤ (L + U) * S := by nlinarith
    calc
      _ ≤ Real.log (Real.sqrt (n + 1)) + S := hb.2
      _ ≤ U * S := by dsimp [U]; nlinarith
      _ ≤ _ := hUU

end ModifiedCartan
#print axioms ModifiedCartan.IsSharpnessSystem.log_vector_norm_bounds
#print axioms ModifiedCartan.IsSharpnessSystem.abs_log_vector_norm_le

