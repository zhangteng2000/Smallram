import FewInflection.PolynomialJets
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Taylor polynomial approximants for entire functions

The compactness argument in the paper replaces entire coordinates by finite
Taylor polynomials.  Mathlib already proves convergence of the Taylor series
of an entire function; this file packages its finite partial sums as genuine
polynomials and records the resulting pointwise limit.
-/

open scoped BigOperators Topology
open Filter

namespace FewInflection

noncomputable section

def taylorPolynomial (f : ℂ → ℂ) (a : ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range N,
    Polynomial.C ((Nat.factorial k : ℂ)⁻¹ * iteratedDeriv k f a) *
      (Polynomial.X - Polynomial.C a) ^ k

theorem taylorPolynomial_eval_eq_sum
    (f : ℂ → ℂ) (a z : ℂ) (N : ℕ) :
    (taylorPolynomial f a N).eval z =
      ∑ k ∈ Finset.range N,
        (Nat.factorial k : ℂ)⁻¹ * iteratedDeriv k f a * (z - a) ^ k := by
  simp [taylorPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_pow, mul_assoc]

theorem tendsto_taylorPolynomial_eval_of_entire
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a z : ℂ) :
    Tendsto (fun N => (taylorPolynomial f a N).eval z) atTop (𝓝 (f z)) := by
  have hs := (Complex.hasSum_taylorSeries_of_entire hf a z).tendsto_sum_nat
  simpa [taylorPolynomial_eval_eq_sum, smul_eq_mul, mul_assoc,
    mul_comm, mul_left_comm] using hs

theorem taylorPolynomial_eval_center
    (f : ℂ → ℂ) (a : ℂ) (N : ℕ) :
    (taylorPolynomial f a (N + 1)).eval a = f a := by
  rw [taylorPolynomial_eval_eq_sum]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.zero_lt_succ N))]
  · simp
  · intro b hb hb0
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    simp [zero_pow hbpos.ne']

theorem entire_taylorPolynomial_eventually_ne_zero_at_center
    {f : ℂ → ℂ} {a : ℂ} (hfa : f a ≠ 0) :
    ∀ᶠ N in atTop, (taylorPolynomial f a (N + 1)).eval a ≠ 0 := by
  filter_upwards [] with N
  rw [taylorPolynomial_eval_center]
  exact hfa

/-- Identification of the multilinear partial sums with the actual Taylor
polynomials.  This uses the derivative formula for an already proved power
series expansion, including its factorial factor. -/
theorem powerSeries_partialSum_eq_taylorPolynomial_eval
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {a : ℂ} {r : ENNReal} (hp : HasFPowerSeriesOnBall f p a r)
    (N : ℕ) (z : ℂ) :
    p.partialSum N (z - a) = (taylorPolynomial f a N).eval z := by
  rw [taylorPolynomial_eval_eq_sum]
  unfold FormalMultilinearSeries.partialSum
  apply Finset.sum_congr rfl
  intro k hk
  have hfact := hp.factorial_smul (z - a) k
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hfact
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, nsmul_eq_mul] at hfact
  have hk0 : (Nat.factorial k : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  calc
    p k (fun _ => z - a) =
        (Nat.factorial k : ℂ)⁻¹ *
          ((Nat.factorial k : ℂ) * p k (fun _ => z - a)) := by
            field_simp
    _ = (Nat.factorial k : ℂ)⁻¹ * ((z - a) ^ k * iteratedDeriv k f a) := by
      rw [hfact]
    _ = (Nat.factorial k : ℂ)⁻¹ * iteratedDeriv k f a * (z - a) ^ k := by ring

/-- Entire Taylor polynomials converge locally uniformly on the whole plane. -/
theorem tendstoLocallyUniformlyOn_taylorPolynomial_eval_of_entire
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    TendstoLocallyUniformlyOn
      (fun N z => (taylorPolynomial f a N).eval z) f atTop Set.univ := by
  have hp := hf.hasFPowerSeriesOnBall a (R := 1) (by norm_num)
  have hlim := hp.tendstoLocallyUniformlyOn'
  simpa only [powerSeries_partialSum_eq_taylorPolynomial_eval hp,
    Metric.eball_top] using hlim

/-- In particular the same approximants converge uniformly on each fixed
closed disk; no exchange of a pointwise limit and a supremum is needed. -/
theorem tendstoUniformlyOn_taylorPolynomial_eval_closedBall
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) (R : ℝ) :
    TendstoUniformlyOn (fun N z => (taylorPolynomial f a N).eval z)
      f atTop (Metric.closedBall a R) := by
  have hp := hf.hasFPowerSeriesOnBall a (R := 1) (by norm_num)
  let S : NNReal := ⟨max R 0 + 1, by positivity⟩
  have hlim := hp.tendstoUniformlyOn' (r' := S) (by simp)
  have hRS : R < (S : ℝ) := by
    dsimp [S]
    exact lt_add_of_le_of_pos (le_max_left R 0) (by norm_num)
  have hsub : Metric.closedBall a R ⊆ Metric.ball a (S : ℝ) :=
    Metric.closedBall_subset_ball hRS
  simpa only [powerSeries_partialSum_eq_taylorPolynomial_eval hp] using hlim.mono hsub

/-- The local version only asks for holomorphicity on the outer closed disk. -/
theorem tendstoLocallyUniformlyOn_taylorPolynomial_eval_on_ball
    {f : ℂ → ℂ} {a : ℂ} {R : NNReal} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall a (R : ℝ))) :
    TendstoLocallyUniformlyOn (fun N z => (taylorPolynomial f a N).eval z)
      f atTop (Metric.ball a (R : ℝ)) := by
  have hp := hf.hasFPowerSeriesOnBall hR
  simpa only [powerSeries_partialSum_eq_taylorPolynomial_eval hp,
    Metric.eball_coe] using hp.tendstoLocallyUniformlyOn'

/-- Uniform approximation on a closed subdisk requires a strict radius gap. -/
theorem tendstoUniformlyOn_taylorPolynomial_eval_on_subdisk
    {f : ℂ → ℂ} {a : ℂ} {r R : NNReal} (hR : 0 < R) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall a (R : ℝ))) :
    TendstoUniformlyOn (fun N z => (taylorPolynomial f a N).eval z)
      f atTop (Metric.closedBall a (r : ℝ)) := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  have hp := hf.hasFPowerSeriesOnBall hR
  have hsR' : (s : ENNReal) < (R : ENNReal) := by exact_mod_cast hsR
  have hlim := hp.tendstoUniformlyOn' hsR'
  have hrs' : (r : ℝ) < (s : ℝ) := hrs
  simpa only [powerSeries_partialSum_eq_taylorPolynomial_eval hp] using
    hlim.mono (Metric.closedBall_subset_ball hrs')

/-- Geometric remainder control on a fixed subdisk of holomorphicity. -/
theorem taylorPolynomial_geometric_remainder_on_subdisk
    {f : ℂ → ℂ} {a : ℂ} {r R : NNReal} (hR : 0 < R) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall a (R : ℝ))) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ z ∈ Metric.closedBall a (r : ℝ), ∀ N : ℕ,
        ‖f z - (taylorPolynomial f a N).eval z‖ ≤ C * q ^ N := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  have hp := hf.hasFPowerSeriesOnBall hR
  have hsR' : (s : ENNReal) < (R : ENNReal) := by exact_mod_cast hsR
  obtain ⟨q, hq, C, hC, hbound⟩ := hp.uniform_geometric_approx hsR'
  refine ⟨q, hq.1, hq.2, C, hC, ?_⟩
  intro z hz N
  have hzs : z - a ∈ Metric.ball (0 : ℂ) (s : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz) hrs
  have h := hbound (z - a) hzs N
  rw [add_sub_cancel] at h
  rw [powerSeries_partialSum_eq_taylorPolynomial_eval hp] at h
  exact h

end

end FewInflection
