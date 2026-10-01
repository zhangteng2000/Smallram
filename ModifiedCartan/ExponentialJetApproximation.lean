import ModifiedCartan.ExponentialTaylorApproximation
import ModifiedCartan.LocalJetDeterminantBounds

open scoped Topology BigOperators
open Filter Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem norm_iteratedDeriv_disk_le_factorial {f : ℂ → ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (ball 0 32))
    (hM : ∀ z ∈ ball (0 : ℂ) 32, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall 0 16) {k m : ℕ} (hkm : k ≤ m) :
    ‖iteratedDeriv k f z‖ ≤ m.factorial * M := by
  have hsub : closedBall z 1 ⊆ ball (0 : ℂ) 32 := by
    intro w hw
    have hw' : ‖w - z‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hz' : ‖z‖ ≤ 16 := by simpa only [mem_closedBall, dist_zero_right] using hz
    rw [mem_ball, dist_zero_right]
    have ht : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w - z) z
    linarith
  have he := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by norm_num : (0 : ℝ) < 1) (hf.differentiableOn.diffContOnCl_ball hsub)
    (fun w hw => hM w (hsub (sphere_subset_closedBall hw)))
  simp only [one_pow, div_one] at he
  apply he.trans
  gcongr

theorem constant_mul_exp_le_exp {K a t : ℝ} (hK : 0 < K)
    (ht : Real.log K ≤ t) :
    K * Real.exp (a * t) ≤ Real.exp ((a + 1) * t) := by
  have hKexp : K ≤ Real.exp t := by
    rw [← Real.exp_log hK]
    exact Real.exp_le_exp.mpr ht
  calc
    _ ≤ Real.exp t * Real.exp (a * t) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem local_jet_exponential_margin {f : ℂ → ℂ} {C t : ℝ} {m : ℕ}
    (hf : AnalyticOnNhd ℂ f (ball 0 32))
    (hbound : ∀ z ∈ ball (0 : ℂ) 32, ‖f z‖ ≤ Real.exp (C * t))
    (ht0 : 0 ≤ t) (ht : Real.log ((m.factorial : ℝ) + 1) ≤ t)
    {z : ℂ} (hz : z ∈ closedBall 0 16) {k : ℕ} (hkm : k ≤ m) :
    ‖iteratedDeriv k f z‖ + 1 ≤ Real.exp ((|C| + 1) * t) := by
  have hj := norm_iteratedDeriv_disk_le_factorial (Real.exp_nonneg _) hf hbound hz hkm
  have hC : Real.exp (C * t) ≤ Real.exp (|C| * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self C) ht0)
  have hone : 1 ≤ Real.exp (|C| * t) := Real.one_le_exp_iff.mpr (mul_nonneg (abs_nonneg _) ht0)
  calc
    _ ≤ (m.factorial : ℝ) * Real.exp (C * t) + 1 := add_le_add hj le_rfl
    _ ≤ (m.factorial : ℝ) * Real.exp (|C| * t) + Real.exp (|C| * t) := by gcongr
    _ = ((m.factorial : ℝ) + 1) * Real.exp (|C| * t) := by ring
    _ ≤ _ := constant_mul_exp_le_exp (by positivity) ht

theorem norm_le_of_unit_error {u v : ℂ} {T : ℝ}
    (hv : ‖v‖ + 1 ≤ T) (herror : ‖u - v‖ ≤ 1) : ‖u‖ ≤ T := by
  have ht : ‖u‖ ≤ ‖u - v‖ + ‖v‖ := by simpa only [sub_add_cancel] using norm_add_le (u - v) v
  linarith

/-- The original-numerator bound in `eq:cramer-numerator-approx`.
The constant is independent of every later approximation precision. -/
theorem exists_fundamentalNumerator_exponential_bound (n : ℕ) (C : ℝ) :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ),
        Tendsto s atTop atTop →
        (∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        ∀ᶠ ν in atTop, ∀ i z, z ∈ closedBall (0 : ℂ) 16 →
          ‖FewInflection.fundamentalNumerator n (g ν) i z‖ ≤ Real.exp (C2 * s ν) := by
  let C1 : ℝ := |C| + 1
  let C2 : ℝ := (n + 1) * C1 + 1
  have hC1 : 0 < C1 := by dsimp [C1]; positivity
  have hC2 : 0 < C2 := by dsimp [C2]; positivity
  refine ⟨C2, hC2, ?_⟩
  intro g s hs hg hnorm
  filter_upwards [hs.eventually_ge_atTop 0,
    hs.eventually_ge_atTop (Real.log (((n + 1).factorial : ℝ) + 1)),
    hs.eventually_ge_atTop (Real.log ((n + 1).factorial : ℝ))] with ν hs0 hsjet hsfac
  intro i z hz
  have hcoordinate (j : Index n) (w : ℂ) (hw : w ∈ ball (0 : ℂ) 32) :
      ‖g ν j w‖ ≤ Real.exp (C * s ν) :=
    (norm_le_pi_norm (fun l => g ν l w) j).trans
      ((norm_le_euclideanNorm (fun l => g ν l w)).trans (hnorm ν w hw))
  have hjet (j : Index n) (k : ℕ) (hk : k ≤ n + 1) :
      ‖iteratedDeriv k (g ν j) z‖ ≤ Real.exp (C1 * s ν) := by
    have he := local_jet_exponential_margin (hg ν j) (hcoordinate j) hs0 hsjet hz hk
    dsimp only [C1]
    linarith
  have hbound := norm_fundamentalNumerator_le_of_jet_bound (g ν) z i (Real.exp_nonneg _) hjet
  calc
    _ ≤ ((n + 1).factorial : ℝ) * Real.exp (C1 * s ν) ^ (n + 1) := hbound
    _ = ((n + 1).factorial : ℝ) * Real.exp (((n + 1 : ℕ) : ℝ) * C1 * s ν) := by
      rw [← Real.exp_nat_mul, mul_assoc]
    _ ≤ Real.exp (((((n + 1 : ℕ) : ℝ) * C1) + 1) * s ν) :=
      constant_mul_exp_le_exp (by positivity) hsfac
    _ = Real.exp (C2 * s ν) := by simp only [C2, Nat.cast_add, Nat.cast_one]

theorem factorial_exponential_error_le (n : ℕ) (B C1 t : ℝ)
    (ht : Real.log (((n + 1).factorial : ℝ) * (n + 1)) ≤ t) :
    ((n + 1).factorial : ℝ) * Real.exp (-(B + (n + 1) * C1 + 1) * t) *
      (n + 1) * Real.exp (C1 * t) ^ (n + 1) ≤ Real.exp (-B * t) := by
  calc
    _ = (((n + 1).factorial : ℝ) * (n + 1)) *
        (Real.exp (-(B + (n + 1) * C1 + 1) * t) * Real.exp (((n + 1 : ℕ) : ℝ) * C1 * t)) := by
      rw [← Real.exp_nat_mul]
      push_cast
      simp only [mul_assoc]
      ring
    _ = (((n + 1).factorial : ℝ) * (n + 1)) *
        Real.exp ((-(B + (n + 1) * C1 + 1) + (n + 1) * C1) * t) := by
      rw [← Real.exp_add]
      congr 1
      congr 1
      push_cast
      ring
    _ ≤ Real.exp (((-(B + (n + 1) * C1 + 1) + (n + 1) * C1) + 1) * t) :=
      constant_mul_exp_le_exp (by positivity) ht
    _ = _ := by congr 1; ring

/-- Actual polynomial approximants with arbitrarily prescribed exponential
errors for both the Wronskian and every signed Cramer numerator.
LaTeX context: `eq:wronskiapprox`, `eq:cramer-numerator-approx`. -/
theorem exists_polynomial_determinant_approximation (n : ℕ) (C B : ℝ) (hB : 0 < B) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ),
        Tendsto s atTop atTop →
        (∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        ∃ p : ℕ → Index n → Polynomial ℂ,
          ∀ᶠ ν in atTop,
            (∀ j, ((p ν j).natDegree : ℝ) ≤ L * s ν) ∧
            (∀ z ∈ closedBall (0 : ℂ) 16,
              ‖FewInflection.wronskian n (fun j w => (p ν j).eval w) z -
                  FewInflection.wronskian n (g ν) z‖ ≤ Real.exp (-B * s ν) ∧
              ∀ i, ‖FewInflection.fundamentalNumerator n (fun j w => (p ν j).eval w) i z -
                  FewInflection.fundamentalNumerator n (g ν) i z‖ ≤ Real.exp (-B * s ν)) := by
  let C1 : ℝ := |C| + 1
  let A : ℝ := B + (n + 1) * C1 + 1
  have hC1 : 0 < C1 := by dsimp [C1]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨L, hL, htaylor⟩ := Paper.eq_taylorerror n A C
  refine ⟨L + 1, by linarith, ?_⟩
  intro g s hs hg hnorm
  obtain ⟨p, _, _, hp⟩ := htaylor g s hs hg hnorm
  refine ⟨p, ?_⟩
  filter_upwards [hp, hs.eventually_ge_atTop 0,
    hs.eventually_ge_atTop (Real.log (((n + 1).factorial : ℝ) + 1)),
    hs.eventually_ge_atTop (Real.log (((n + 1).factorial : ℝ) * (n + 1)))]
    with ν hpν hs0 hsjet hsfac
  refine ⟨hpν.1, ?_⟩
  intro z hz
  have hcoordinate (j : Index n) (w : ℂ) (hw : w ∈ ball (0 : ℂ) 32) :
      ‖g ν j w‖ ≤ Real.exp (C * s ν) :=
    (norm_le_pi_norm (fun l => g ν l w) j).trans
      ((norm_le_euclideanNorm (fun l => g ν l w)).trans (hnorm ν w hw))
  have hmargin (j : Index n) (k : ℕ) (hk : k ≤ n + 1) :
      ‖iteratedDeriv k (g ν j) z‖ + 1 ≤ Real.exp (C1 * s ν) :=
    local_jet_exponential_margin (hg ν j) (hcoordinate j) hs0 hsjet hz hk
  have hjg (j : Index n) (k : ℕ) (hk : k ≤ n + 1) :
      ‖iteratedDeriv k (g ν j) z‖ ≤ Real.exp (C1 * s ν) := by
    linarith [hmargin j k hk]
  have herr1 : Real.exp (-A * s ν) ≤ 1 := by
    have he : -A * s ν ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA.le) hs0
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr he
  have hjp (j : Index n) (k : ℕ) (hk : k ≤ n + 1) :
      ‖iteratedDeriv k (fun w => (p ν j).eval w) z‖ ≤ Real.exp (C1 * s ν) :=
    norm_le_of_unit_error (hmargin j k hk) ((hpν.2 j k hk z hz).trans herr1)
  have hd (j : Index n) (k : ℕ) (hk : k ≤ n + 1) :
      ‖iteratedDeriv k (fun w => (p ν j).eval w) z - iteratedDeriv k (g ν j) z‖ ≤
        Real.exp (-A * s ν) := hpν.2 j k hk z hz
  have hM1 : 1 ≤ Real.exp (C1 * s ν) := Real.one_le_exp_iff.mpr (mul_nonneg hC1.le hs0)
  constructor
  · exact (norm_wronskian_sub_le_of_jet_error (fun j w => (p ν j).eval w) (g ν) z
      hM1 (Real.exp_nonneg _) hjp hjg hd).trans (factorial_exponential_error_le n B C1 (s ν) hsfac)
  · intro i
    exact (norm_fundamentalNumerator_sub_le_of_jet_error (fun j w => (p ν j).eval w) (g ν) z i
      hM1 (Real.exp_nonneg _) hjp hjg hd).trans (factorial_exponential_error_le n B C1 (s ν) hsfac)

end ModifiedCartan
