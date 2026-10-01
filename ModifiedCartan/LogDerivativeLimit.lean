import ModifiedCartan.FirstLogDerivLimit
import ModifiedCartan.HigherLogDerivLimit
import ModifiedCartan.LogDerivativePartitions
import ModifiedCartan.MeasureFiniteAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set

set_option autoImplicit false

namespace ModifiedCartan

theorem tendstoInMeasure_partitionPolynomial {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {f : ℕ → ℕ → A → ℂ} {g : ℕ → A → ℂ}
    (hf : ∀ j n, AEStronglyMeasurable (f j n) μ)
    (h : ∀ j, TendstoInMeasure μ (f j) atTop (g j)) (k : ℕ) :
    TendstoInMeasure μ (fun n x => logDerivativePartitionPolynomial k (fun j => f j n x))
      atTop (fun x => logDerivativePartitionPolynomial k (fun j => g j x)) := by
  unfold logDerivativePartitionPolynomial
  apply tendstoInMeasure_finsetSum
  · intro c _ n
    exact Finset.univ.aestronglyMeasurable_fun_prod (fun i _ => hf (c.partSize i - 1) n)
  · intro c _
    exact tendstoInMeasure_finsetProd Finset.univ (fun i _ n => hf (c.partSize i - 1) n)
      (fun i _ => h (c.partSize i - 1))

theorem normalized_logDeriv_jet_aestronglyMeasurable
    {U K : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (j : ℕ) (s : ℝ) :
    AEStronglyMeasurable (fun z => iteratedDeriv j (logDeriv f) z / (s : ℂ) ^ (j + 1))
      (volume.restrict K) := by
  have hm : AEStronglyMeasurable (iteratedDeriv j (logDeriv f)) (volume.restrict K) := by
    cases j with
    | zero =>
      exact (memLp_logDeriv_on_compact hf hKU hK (p := 1) zero_lt_one (by norm_num)).aestronglyMeasurable
    | succ j =>
      simpa only [Nat.succ_eq_add_one, iteratedDeriv_succ] using
        aestronglyMeasurable_deriv (iteratedDeriv j (logDeriv f)) (volume.restrict K)
  simpa only [div_eq_mul_inv] using hm.mul_const (((s : ℂ) ^ (j + 1))⁻¹)

theorem LocalLpConvergence.iteratedDeriv_div_localMeasure
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hnonzero : ∀ n, ∃ b ∈ U, f n b ≠ 0)
    (hs : Tendsto s atTop atTop) (hg : HasWeakComplexGradient U u g) (k : ℕ) :
    LocalMeasureConvergence U (fun n z => iteratedDeriv k (f n) z / ((s n : ℂ) ^ k * f n z))
      (fun z => g z ^ k) := by
  intro K hK hKU
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  have hjets (j : ℕ) : TendstoInMeasure (volume.restrict K)
      (fun n z => iteratedDeriv j (logDeriv (f n)) z / (s n : ℂ) ^ (j + 1))
      atTop (fun z => if j = 0 then g z else 0) := by
    cases j with
    | zero =>
      have hfirst := (hu.logDeriv_localLpConvergence hU hUc hf hnonzero hs hg
        (p := 1) le_rfl (by norm_num)).inMeasure (by norm_num) K hK hKU
      simpa only [iteratedDeriv_zero, zero_add, pow_one, if_pos rfl, Complex.real_smul,
        Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using! hfirst
    | succ j =>
      simpa only [Nat.succ_ne_zero, if_false] using!
        Paper.eq_higher_logderiv_measure hU hUc hu hf hnonzero hs (Nat.succ_pos j) K hK hKU
  have hpoly := tendstoInMeasure_partitionPolynomial
    (fun j n => normalized_logDeriv_jet_aestronglyMeasurable (hf n) hK hKU j (s n)) hjets k
  have hlim : TendstoInMeasure (volume.restrict K)
      (fun n z => logDerivativePartitionPolynomial k
        (fun j => iteratedDeriv j (logDeriv (f n)) z / (s n : ℂ) ^ (j + 1))) atTop
      (fun z => g z ^ k) := by
    simpa only [partitionPolynomial_constant_jet] using hpoly
  apply hlim.congr_left
  intro n
  have hfnz := (analytic_ae_ne_zero hU hUc (hf n) (hnonzero n)).filter_mono
    (ae_mono (Measure.restrict_mono_set _ hKU))
  filter_upwards [hfnz, ae_restrict_mem hK.measurableSet] with z hz hzK
  exact (normalized_iteratedDeriv_eq_partition (hf n z (hKU hzK)) hz k (s n)).symm

namespace Paper

/-- LaTeX label `lem:logderivlimit`, including `eq:logderivlimit`.
The holomorphic functions are expressed by complex differentiability on the
open domain. u is the real L1 representative and g encodes the distributional
gradient 2∂u. This stronger representative theorem needs no subharmonicity
hypothesis. The same g occurs in every convergence conclusion. -/
theorem lem_logderivlimit
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U) (hnonzero : ∀ n, ∃ b ∈ U, f n b ≠ 0)
    (hs : Tendsto s atTop atTop) :
    ∃ g : ℂ → ℂ, HasWeakComplexGradient U u g ∧
      (∀ p : ℝ, 1 ≤ p → p < 2 → MemW1pLoc (ENNReal.ofReal p) U u) ∧
      (∀ k : ℕ, 1 ≤ k → LocalMeasureConvergence U
        (fun n z => iteratedDeriv k (f n) z / ((s n : ℂ) ^ k * f n z)) (fun z => g z ^ k)) ∧
      (∀ p : ℝ, 1 ≤ p → p < 2 → LocalLpConvergence (ENNReal.ofReal p) U
        (fun n z => deriv (f n) z / ((s n : ℂ) * f n z)) g) := by
  have hfa (n : ℕ) := (hf n).analyticOnNhd hU
  obtain ⟨g, hg, _⟩ := hu.log_limit_weak_gradient hU hUc hfa hnonzero hs
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro p hp1 hp2
    exact hu.log_limit_memW1pLoc hU hUc hfa hnonzero hs hp1 hp2
  · intro k _
    exact hu.iteratedDeriv_div_localMeasure hU hUc hfa hnonzero hs hg k
  · intro p hp1 hp2
    apply (hu.logDeriv_localLpConvergence hU hUc hfa hnonzero hs hg hp1 hp2).congr_ae _ EventuallyEq.rfl
    intro n
    apply Eventually.of_forall
    intro z
    simp [logDeriv_apply, Complex.real_smul, div_eq_mul_inv, mul_comm, mul_assoc]

end Paper


end ModifiedCartan

