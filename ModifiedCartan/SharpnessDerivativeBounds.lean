import ModifiedCartan.ScaledJets
import Mathlib.Analysis.ODE.Gronwall

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem IsSharpnessSystem.scaledDerivativeJetNext_norm_le {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 1 ≤ q) (hqn : q ≤ n + 1) {a : ℝ} (ha : 0 < a)
    (j i : Index n) (v : ℂ) (hv : ‖v‖ ^ k ≤ a ^ q) :
    ‖iteratedDeriv (i.val + 1) (g j) v / (a : ℂ) ^ i.val‖ ≤
      a * ‖scaledDerivativeJet n a (g j) v‖ := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have han : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  by_cases hi : i.val < n
  · let next : Index n := ⟨i.val + 1, by omega⟩
    rw [divided_next_identity _ _ haC, norm_mul, han]
    exact mul_le_mul_of_nonneg_left
      (norm_le_pi_norm (scaledDerivativeJet n a (g j) v) next) ha.le
  · have hilast : i.val = n := by have := i.isLt; omega
    let m : Index n := ⟨n + 1 - q, by omega⟩
    rw [hilast, h.2.2 j v, divided_top_identity _ _ _ haC (by dsimp [m]; omega : m.val + q = n + 1)]
    rw [norm_mul, norm_mul, han]
    have hc : ‖v ^ k / (a : ℂ) ^ q‖ ≤ 1 := by
      rw [norm_div, norm_pow, norm_pow, han]
      exact (div_le_one (pow_pos ha q)).mpr hv
    have hm := norm_le_pi_norm (scaledDerivativeJet n a (g j) v) m
    change ‖iteratedDeriv m.val (g j) v / (a : ℂ) ^ m.val‖ ≤ _ at hm
    calc
      _ ≤ a * 1 * ‖scaledDerivativeJet n a (g j) v‖ := by gcongr
      _ = _ := by rw [mul_one]

theorem IsSharpnessSystem.scaledDerivativeJetLineDeriv_norm_le {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 1 ≤ q) (hqn : q ≤ n + 1) {a : ℝ} (ha : 0 < a)
    (j : Index n) (z : ℂ) (t : ℝ) (hv : ‖(t : ℂ) * z‖ ^ k ≤ a ^ q) :
    ‖scaledDerivativeJetLineDeriv n a (g j) z t‖ ≤
      (‖z‖ * a) * ‖scaledDerivativeJetLine n a (g j) z t‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have he : scaledDerivativeJetLineDeriv n a (g j) z t i =
      (iteratedDeriv (i.val + 1) (g j) ((t : ℂ) * z) / (a : ℂ) ^ i.val) * z := by
    unfold scaledDerivativeJetLineDeriv
    ring
  rw [he, norm_mul]
  calc
    _ ≤ (a * ‖scaledDerivativeJet n a (g j) ((t : ℂ) * z)‖) * ‖z‖ :=
      mul_le_mul_of_nonneg_right (h.scaledDerivativeJetNext_norm_le hq hqn ha j i _ hv) (norm_nonneg z)
    _ = _ := by unfold scaledDerivativeJetLine; ring

theorem IsSharpnessSystem.scaledDerivativeJet_norm_le {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 1 ≤ q) (hqn : q ≤ n + 1) {a R : ℝ} (ha : 1 ≤ a)
    (hscale : R ^ k ≤ a ^ q) {z : ℂ} (hz : ‖z‖ ≤ R) (j : Index n) :
    ‖scaledDerivativeJet n a (g j) z‖ ≤ Real.exp (‖z‖ * a) := by
  have hap : 0 < a := zero_lt_one.trans_le ha
  have hd := scaledDerivativeJetLine_hasDerivAt (h.1 j) n a z
  have hc : Continuous (scaledDerivativeJetLine n a (g j) z) :=
    continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖scaledDerivativeJetLineDeriv n a (g j) z t‖ ≤
        (‖z‖ * a) * ‖scaledDerivativeJetLine n a (g j) z t‖ + 0 := by
    rw [add_zero]
    apply h.scaledDerivativeJetLineDeriv_norm_le hq hqn hap
    apply le_trans _ hscale
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ = t * ‖z‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg z)
      _ ≤ R := by simpa only [one_mul] using hz
  have hinit : ‖scaledDerivativeJetLine n a (g j) z 0‖ ≤ 1 := by
    simpa only [scaledDerivativeJetLine, Complex.ofReal_zero, zero_mul] using
      h.scaledDerivativeJet_initial_norm_le ha j
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le hc.continuousOn
    (fun t (_ : t ∈ Ico (0 : ℝ) 1) => (hd t).hasDerivWithinAt) hinit hbound 1
    (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  simpa only [scaledDerivativeJetLine, Complex.ofReal_one, one_mul, sub_zero,
    gronwallBound_ε0, mul_one] using hb

/-- LaTeX `prop:sharpness-orders`, Step 1: a uniform disk bound for every
actual prescribed solution and every derivative in its jet. -/
theorem IsSharpnessSystem.derivative_norm_le {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 2 ≤ q) (hqn : q ≤ n + 1) {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (i j : Index n) :
    ‖iteratedDeriv i.val (g j) z‖ ≤
      R ^ ((i.val : ℝ) * ((k : ℝ) / q)) * Real.exp (R ^ (1 + (k : ℝ) / q)) := by
  let a : ℝ := R ^ ((k : ℝ) / q)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have ha : 1 ≤ a := Real.one_le_rpow hR (by positivity)
  have hap : 0 < a := zero_lt_one.trans_le ha
  have hscale : R ^ k = a ^ q := (sharpnessScale_pow (by omega) k hRp).symm
  have hi := norm_iteratedDeriv_le_scaledDerivativeJet (g j) hap z i
  have hb := h.scaledDerivativeJet_norm_le (by omega) hqn ha hscale.le hz j
  have he : ‖z‖ * a ≤ R ^ (1 + (k : ℝ) / q) := by
    rw [Real.rpow_add hRp, Real.rpow_one]
    exact mul_le_mul_of_nonneg_right hz hap.le
  have hp : a ^ i.val = R ^ ((i.val : ℝ) * ((k : ℝ) / q)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hRp.le]
    congr 1
    ring
  calc
    _ ≤ a ^ i.val * ‖scaledDerivativeJet n a (g j) z‖ := hi
    _ ≤ a ^ i.val * Real.exp (‖z‖ * a) := mul_le_mul_of_nonneg_left hb (pow_nonneg hap.le _)
    _ ≤ a ^ i.val * Real.exp (R ^ (1 + (k : ℝ) / q)) := by gcongr
    _ = _ := by rw [hp]

end ModifiedCartan
#print axioms ModifiedCartan.IsSharpnessSystem.derivative_norm_le
