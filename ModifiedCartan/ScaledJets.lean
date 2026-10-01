import ModifiedCartan.SharpnessWronskian
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Derivatives normalized at a fixed circle scale, as in Step 1 of
`prop:sharpness-orders`. The finite-product norm is used internally. -/
noncomputable def scaledDerivativeJet (n : ℕ) (a : ℝ) (w : ℂ → ℂ) (z : ℂ) (i : Index n) : ℂ :=
  iteratedDeriv i.val w z / (a : ℂ) ^ i.val

noncomputable def scaledDerivativeJetLine (n : ℕ) (a : ℝ) (w : ℂ → ℂ) (z : ℂ)
    (t : ℝ) : Index n → ℂ := scaledDerivativeJet n a w ((t : ℂ) * z)

noncomputable def scaledDerivativeJetLineDeriv (n : ℕ) (a : ℝ) (w : ℂ → ℂ) (z : ℂ)
    (t : ℝ) (i : Index n) : ℂ :=
  (iteratedDeriv (i.val + 1) w ((t : ℂ) * z) * z) / (a : ℂ) ^ i.val

theorem scaledDerivativeAlongLine_hasDerivAt {w : ℂ → ℂ}
    (hw : Differentiable ℂ w) (a : ℝ) (z : ℂ) (i : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedDeriv i w ((s : ℂ) * z) / (a : ℂ) ^ i)
      (iteratedDeriv (i + 1) w ((t : ℂ) * z) * z / (a : ℂ) ^ i) t := by
  have ha : AnalyticAt ℂ w ((t : ℂ) * z) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hw) _ (mem_univ _)
  have hi := (FewInflection.analyticAt_iteratedDeriv ha i).differentiableAt.hasDerivAt
  rw [← iteratedDeriv_succ] at hi
  have hm : HasDerivAt (fun v : ℂ => v * z) z (t : ℂ) := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id (t : ℂ)).mul_const z
  simpa only [Function.comp_apply] using! ((hi.comp (t : ℂ) hm).div_const ((a : ℂ) ^ i)).comp_ofReal

theorem scaledDerivativeJetLine_hasDerivAt {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (n : ℕ) (a : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (scaledDerivativeJetLine n a w z) (scaledDerivativeJetLineDeriv n a w z t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  exact scaledDerivativeAlongLine_hasDerivAt hw a z i.val t

theorem divided_next_identity (a b : ℂ) (ha : a ≠ 0) (i : ℕ) :
    b / a ^ i = a * (b / a ^ (i + 1)) := by
  rw [pow_succ]
  field_simp

theorem divided_top_identity (a b c : ℂ) (ha : a ≠ 0) {n m q : ℕ}
    (hmq : m + q = n + 1) :
    b * c / a ^ n = a * (b / a ^ q) * (c / a ^ m) := by
  have hp : a ^ q * a ^ m = a ^ n * a := by
    rw [← pow_add, Nat.add_comm q m, hmq, pow_succ]
  calc
    _ = (a * b * c) / (a ^ n * a) := by field_simp
    _ = (a * b * c) / (a ^ q * a ^ m) := by rw [hp]
    _ = _ := by ring

theorem IsSharpnessSystem.scaledDerivativeJet_initial_norm_le {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g) {a : ℝ} (ha : 1 ≤ a)
    (j : Index n) : ‖scaledDerivativeJet n a (g j) 0‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  change ‖iteratedDeriv i.val (g j) 0 / (a : ℂ) ^ i.val‖ ≤ 1
  rw [h.2.1 i j]
  split_ifs
  · rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans ha)]
    exact (div_le_one (pow_pos (lt_of_lt_of_le zero_lt_one ha) _)).mpr (one_le_pow₀ ha)
  · simp only [zero_div, norm_zero, zero_le_one]

theorem norm_iteratedDeriv_le_scaledDerivativeJet {n : ℕ} (w : ℂ → ℂ)
    {a : ℝ} (ha : 0 < a) (z : ℂ) (i : Index n) :
    ‖iteratedDeriv i.val w z‖ ≤ a ^ i.val * ‖scaledDerivativeJet n a w z‖ := by
  have hi := norm_le_pi_norm (scaledDerivativeJet n a w z) i
  change ‖iteratedDeriv i.val w z / (a : ℂ) ^ i.val‖ ≤ ‖scaledDerivativeJet n a w z‖ at hi
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha.le] at hi
  simpa only [mul_comm] using (div_le_iff₀ (pow_pos ha i.val)).mp hi

theorem sharpnessScale_pow {q : ℕ} (hq : 1 ≤ q) (k : ℕ) {R : ℝ} (hR : 0 < R) :
    (R ^ ((k : ℝ) / q)) ^ q = R ^ k := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc
    _ = (R ^ ((k : ℝ) / q)) ^ (q : ℝ) := (Real.rpow_natCast _ _).symm
    _ = R ^ (((k : ℝ) / q) * q) := (Real.rpow_mul hR.le _ _).symm
    _ = R ^ (k : ℝ) := by rw [div_mul_cancel₀ _ hq0]
    _ = R ^ k := Real.rpow_natCast _ _

end ModifiedCartan
#print axioms ModifiedCartan.scaledDerivativeJetLine_hasDerivAt
#print axioms ModifiedCartan.IsSharpnessSystem.scaledDerivativeJet_initial_norm_le
#print axioms ModifiedCartan.sharpnessScale_pow
