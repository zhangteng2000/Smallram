import ModifiedCartan.ExtendedLogConvergence

open scoped Topology ENNReal
open Filter MeasureTheory Set

set_option autoImplicit false

namespace ModifiedCartan

/-- The nonnegative logarithm, in a form continuous even at zero. -/
noncomputable def logPlusNorm (z : ℂ) : ℝ := Real.log (max ‖z‖ 1)

theorem continuous_logPlusNorm : Continuous logPlusNorm :=
  (continuous_norm.max continuous_const).log (fun z => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right ‖z‖ 1)))

theorem log_norm_le_logPlusNorm (z : ℂ) : Real.log ‖z‖ ≤ logPlusNorm z := by
  by_cases hz : z = 0
  · simp [hz, logPlusNorm]
  · exact Real.log_le_log (norm_pos_iff.mpr hz) (le_max_left _ _)

theorem tendstoInMeasure_scaled_logPlus {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {f : ℕ → A → ℂ} {g : A → ℂ} {s : ℕ → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (h : TendstoInMeasure μ f atTop g)
    (hs : Tendsto s atTop atTop) :
    TendstoInMeasure μ (fun n x => (s n)⁻¹ * logPlusNorm (f n x)) atTop (fun _ => 0) := by
  have hinv : TendstoInMeasure μ (fun n (_ : A) => (s n)⁻¹) atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => tendsto_inv_atTop_zero.comp hs))
  have hlog := tendstoInMeasure_continuous_map hf h continuous_logPlusNorm
  have hmul := tendstoInMeasure_continuous_map₂
    (fun _ => aestronglyMeasurable_const)
    (fun n => continuous_logPlusNorm.comp_aestronglyMeasurable (hf n)) hinv hlog
    (Φ := fun x : ℝ × ℝ => x.1 * x.2) (by fun_prop)
  simpa only [zero_mul] using hmul

theorem LocalMeasureConvergence.scaled_logPlus {U : Set ℂ}
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {s : ℕ → ℝ}
    (h : LocalMeasureConvergence U f g)
    (hf : ∀ K, IsCompact K → K ⊆ U → ∀ n, AEStronglyMeasurable (f n) (volume.restrict K))
    (hs : Tendsto s atTop atTop) :
    LocalMeasureConvergence U (fun n z => (s n)⁻¹ * logPlusNorm (f n z)) (fun _ => 0) := by
  intro K hK hKU
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact tendstoInMeasure_scaled_logPlus (hf K hK hKU) (h K hK hKU) hs

theorem scaled_log_scale_tendsto_zero {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) (κ : ℕ) :
    Tendsto (fun n => (κ : ℝ) * (s n)⁻¹ * Real.log (s n)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => Real.log (s n) / s n) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hs
  simpa only [div_eq_mul_inv, mul_zero, mul_assoc, mul_comm, mul_left_comm] using ht.const_mul (κ : ℝ)

theorem tendstoInMeasure_real_finsetSum {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] (S : Finset ι)
    {f : ι → ℕ → A → ℝ} {g : ι → A → ℝ}
    (hf : ∀ i ∈ S, ∀ n, AEStronglyMeasurable (f i n) μ)
    (h : ∀ i ∈ S, TendstoInMeasure μ (f i) atTop (g i)) :
    TendstoInMeasure μ (fun n x => ∑ i ∈ S, f i n x) atTop (fun x => ∑ i ∈ S, g i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => tendsto_const_nhds))
  | @insert i S hi ih =>
    have hsum := tendstoInMeasure_continuous_map₂ (hf i (Finset.mem_insert_self _ _))
      (fun n => S.aestronglyMeasurable_fun_sum (fun k hk => hf k (Finset.mem_insert_of_mem hk) n))
      (h i (Finset.mem_insert_self _ _))
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)) (fun k hk => h k (Finset.mem_insert_of_mem hk)))
      (Φ := fun x : ℝ × ℝ => x.1 + x.2) (by fun_prop)
    simpa only [Finset.sum_insert hi] using hsum

theorem LocalLpConvergence.real_sum_localMeasure {ι : Type*} [Fintype ι]
    {U : Set ℂ} {f : ι → ℕ → ℂ → ℝ} {g : ι → ℂ → ℝ}
    (h : ∀ i, LocalLpConvergence 1 U (f i) (g i)) :
    LocalMeasureConvergence U (fun n z => ∑ i, f i n z) (fun z => ∑ i, g i z) := by
  intro K hK hKU
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact tendstoInMeasure_real_finsetSum Finset.univ
    (fun i _ n => ((h i).source_mem K hK hKU n).aestronglyMeasurable)
    (fun i _ => (h i).inMeasure (by norm_num) K hK hKU)


end ModifiedCartan

