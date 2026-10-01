import ModifiedCartan.QuantitativeTaylor
import ModifiedCartan.NormComparison
import Mathlib.Algebra.Order.Floor.Semiring

open scoped Topology BigOperators
open Filter Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem exists_geometric_linear_cutoff (A C K : ℝ) (hK : 0 < K) :
    ∃ L : ℝ, 0 < L ∧ ∀ t : ℝ, max 1 (Real.log K) ≤ t →
      (Nat.ceil (L * t) : ℝ) ≤ (L + 1) * t ∧
      K * Real.exp (C * t) * (5 / 6 : ℝ) ^ Nat.ceil (L * t) ≤ Real.exp (-A * t) := by
  let D : ℝ := |A| + |C| + 1
  let q : ℝ := 5 / 6
  have hq0 : 0 < q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have hD : 0 < D := by dsimp [D]; positivity
  let L : ℝ := D / (-Real.log q)
  have hL : 0 < L := div_pos hD (neg_pos.mpr hlog)
  have hLlog : L * Real.log q = -D := by
    dsimp [L]
    field_simp [hlog.ne]
  refine ⟨L, hL, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := by linarith
  have htlog : Real.log K ≤ t := (le_max_right _ _).trans ht
  have hceil := Nat.le_ceil (L * t)
  have hupper := Nat.ceil_lt_add_one (mul_nonneg hL.le ht0)
  constructor
  · nlinarith
  · have hpow : q ^ Nat.ceil (L * t) ≤ Real.exp (-D * t) := by
      have heq : q ^ Nat.ceil (L * t) =
          Real.exp ((Nat.ceil (L * t) : ℝ) * Real.log q) := by
        rw [Real.exp_nat_mul, Real.exp_log hq0]
      rw [heq]
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (L * t) * Real.log q := mul_le_mul_of_nonpos_right hceil hlog.le
        _ = -D * t := by rw [mul_right_comm, hLlog]
    have hKexp : K ≤ Real.exp t := by
      rw [← Real.exp_log hK]
      exact Real.exp_le_exp.mpr htlog
    have hcoeff : 1 + C - D ≤ -A := by
      dsimp [D]
      linarith [le_abs_self A, le_abs_self C]
    change K * Real.exp (C * t) * q ^ Nat.ceil (L * t) ≤ _
    calc
      _ ≤ Real.exp t * Real.exp (C * t) * Real.exp (-D * t) := by gcongr
      _ = Real.exp ((1 + C - D) * t) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-A * t) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hcoeff ht0)

namespace Paper

/-- LaTeX `eq:taylorerror`, with the actual Taylor approximants and their
linear degree control. Constants are chosen before the sequence data.
The proof uses radii 24 and 20, then Cauchy estimates on radius-2 circles;
this alternative is recorded in `FORMALIZATION_MAP.md`. -/
theorem eq_taylorerror (n : ℕ) (A C : ℝ) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (g : ℕ → Index n → ℂ → ℂ) (s : ℕ → ℝ),
        Tendsto s atTop atTop →
        (∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) →
        (∀ ν z, z ∈ ball (0 : ℂ) 32 →
          euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)) →
        ∃ p : ℕ → Index n → Polynomial ℂ,
          (∀ ν j, p ν j = FewInflection.taylorPolynomial (g ν j) 0 (Nat.ceil (L * s ν))) ∧
          (∀ ν j, (p ν j).natDegree ≤ Nat.ceil (L * s ν)) ∧
          ∀ᶠ ν in atTop,
            (∀ j, ((p ν j).natDegree : ℝ) ≤ (L + 1) * s ν) ∧
            (∀ j k, k ≤ n + 1 → ∀ z ∈ closedBall (0 : ℂ) 16,
              ‖iteratedDeriv k (fun w => (p ν j).eval w) z - iteratedDeriv k (g ν j) z‖ ≤
                Real.exp (-A * s ν)) := by
  let K : ℝ := 6 * (n + 1).factorial
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨L, hL, hcutoff⟩ := exists_geometric_linear_cutoff A C K hK
  refine ⟨L, hL, ?_⟩
  intro g s hs hg hnorm
  let p : ℕ → Index n → Polynomial ℂ := fun ν j =>
    FewInflection.taylorPolynomial (g ν j) 0 (Nat.ceil (L * s ν))
  have hdegree (ν : ℕ) (j : Index n) : (p ν j).natDegree ≤ Nat.ceil (L * s ν) :=
    taylorPolynomial_natDegree_le _ _ _
  refine ⟨p, fun _ _ => rfl, hdegree, ?_⟩
  filter_upwards [hs.eventually_ge_atTop (max 1 (Real.log K))] with ν hν
  have hcoordinate (j : Index n) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 32) :
      ‖g ν j z‖ ≤ Real.exp (C * s ν) :=
    (norm_le_pi_norm (fun i => g ν i z) j).trans
      ((norm_le_euclideanNorm (fun i => g ν i z)).trans (hnorm ν z hz))
  constructor
  · intro j
    exact (show ((p ν j).natDegree : ℝ) ≤ Nat.ceil (L * s ν) by
      exact_mod_cast hdegree ν j).trans (hcutoff (s ν) hν).1
  · intro j k hk z hz
    exact (norm_taylor_derivative_remainder_le_factorial (Real.exp_nonneg _)
      (hg ν j) (hcoordinate j) hz (Nat.ceil (L * s ν)) hk).trans (hcutoff (s ν) hν).2

end Paper

end ModifiedCartan
