import ModifiedCartan.LinearPicardTerms

open scoped Topology Interval
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem linearPicardTerm_norm_le_on {B : ℝ → V →L[ℝ] V} {M : ℝ}
    (hM : 0 ≤ M) (hB : ∀ t, ‖B t‖ ≤ M) (v : V) (n : ℕ) {t R : ℝ} (ht : |t| ≤ R) :
    ‖linearPicardTerm B v n t‖ ≤ ‖v‖ * ((M * R) ^ n / (n.factorial : ℝ)) := by
  calc
    _ ≤ (‖v‖ * M ^ n / (n.factorial : ℝ)) * |t| ^ n := linearPicardTerm_norm_le hM hB v n t
    _ ≤ (‖v‖ * M ^ n / (n.factorial : ℝ)) * R ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) ht n) (by positivity)
    _ = _ := by rw [mul_pow]; ring

noncomputable def linearPicardSolution (B : ℝ → V →L[ℝ] V) (v : V) (t : ℝ) : V :=
  ∑' n, linearPicardTerm B v n t

theorem linearPicardSolution_zero {B : ℝ → V →L[ℝ] V} {M : ℝ}
    (hM : 0 ≤ M) (hB : ∀ t, ‖B t‖ ≤ M) (v : V) : linearPicardSolution B v 0 = v := by
  unfold linearPicardSolution
  rw [(linearPicardTerm_summable hM hB v 0).tsum_eq_zero_add]
  simp only [linearPicardTerm, intervalIntegral.integral_same, tsum_zero, add_zero]

/-- The actual convergent successive-integral series solves the equation. -/
theorem linearPicardSolution_hasDerivAt {B : ℝ → V →L[ℝ] V}
    (hBc : Continuous B) {M : ℝ} (hM : 0 ≤ M) (hB : ∀ t, ‖B t‖ ≤ M)
    (v : V) (t : ℝ) :
    HasDerivAt (linearPicardSolution B v) (B t (linearPicardSolution B v t)) t := by
  let R : ℝ := |t| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have ht : t ∈ Ioo (-R) R := abs_lt.mp (by dsimp [R]; linarith)
  have hzero : (0 : ℝ) ∈ Ioo (-R) R := ⟨neg_neg_of_pos hR, hR⟩
  have hs : Summable (fun n : ℕ => (M * ‖v‖) * ((M * R) ^ n / (n.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial (M * R)).mul_left (M * ‖v‖)
  have hb (n : ℕ) (s : ℝ) (hs : s ∈ Ioo (-R) R) :
      ‖B s (linearPicardTerm B v n s)‖ ≤ (M * ‖v‖) * ((M * R) ^ n / (n.factorial : ℝ)) := by
    calc
      _ ≤ ‖B s‖ * ‖linearPicardTerm B v n s‖ := (B s).le_opNorm _
      _ ≤ M * (‖v‖ * ((M * R) ^ n / (n.factorial : ℝ))) :=
        mul_le_mul (hB s) (linearPicardTerm_norm_le_on hM hB v n (abs_lt.mpr hs).le)
          (norm_nonneg _) hM
      _ = _ := by ring
  have hs0 : Summable (fun n => linearPicardTerm B v (n + 1) 0) := by
    simp only [linearPicardTerm_succ_zero]
    exact summable_zero
  have hd := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioo isPreconnected_Ioo
    (fun n s _ => linearPicardTerm_succ_hasDerivAt hBc v n s) hb hzero hs0 ht
  have he : (fun s => v + ∑' n, linearPicardTerm B v (n + 1) s) = linearPicardSolution B v := by
    funext s
    exact (linearPicardTerm_summable hM hB v s).tsum_eq_zero_add.symm
  have hsum : (∑' n, B t (linearPicardTerm B v n t)) = B t (linearPicardSolution B v t) :=
    ((B t).map_tsum (linearPicardTerm_summable hM hB v t)).symm
  have hd' := hd.const_add v
  rw [he, hsum] at hd'
  exact hd'

/-- Global solutions for genuinely bounded continuous linear coefficients,
with arbitrary initial time and value. Used to extend the manuscript's system
across a compact interval after a continuous clipping of its coefficients. -/
theorem bounded_linearODE_solution_exists {B : ℝ → V →L[ℝ] V}
    (hBc : Continuous B) {M : ℝ} (hM : 0 ≤ M) (hB : ∀ t, ‖B t‖ ≤ M)
    (t0 : ℝ) (v : V) :
    ∃ X : ℝ → V, X t0 = v ∧ ∀ t, HasDerivAt X (B t (X t)) t := by
  let C : ℝ → V →L[ℝ] V := fun s => B (s + t0)
  have hCc : Continuous C := hBc.comp (continuous_id.add continuous_const)
  have hCb (s : ℝ) : ‖C s‖ ≤ M := hB (s + t0)
  refine ⟨fun t => linearPicardSolution C v (t - t0), ?_, ?_⟩
  · change linearPicardSolution C v (t0 - t0) = v
    rw [sub_self, linearPicardSolution_zero hM hCb]
  · intro t
    have hd := (linearPicardSolution_hasDerivAt hCc hM hCb v (t - t0)).scomp t
      ((hasDerivAt_id t).sub_const t0)
    simpa only [Function.comp_apply, id_eq, C, sub_add_cancel, one_smul] using! hd

end ModifiedCartan
#print axioms ModifiedCartan.linearPicardSolution_hasDerivAt
#print axioms ModifiedCartan.bounded_linearODE_solution_exists

