import ModifiedCartan.MeasureConvergenceAlgebra

open scoped Topology ENNReal
open Filter MeasureTheory Set

set_option autoImplicit false

namespace ModifiedCartan

/-! Finite products and sums of sequences converging in measure, for the
partition expansion in Step 3 of `lem:logderivlimit`. -/

theorem tendstoInMeasure_finsetProd {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] (S : Finset ι)
    {f : ι → ℕ → A → ℂ} {g : ι → A → ℂ}
    (hf : ∀ i ∈ S, ∀ n, AEStronglyMeasurable (f i n) μ)
    (h : ∀ i ∈ S, TendstoInMeasure μ (f i) atTop (g i)) :
    TendstoInMeasure μ (fun n x => ∏ i ∈ S, f i n x) atTop (fun x => ∏ i ∈ S, g i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => tendsto_const_nhds))
  | @insert i S hi ih =>
    have hprod := tendstoInMeasure_continuous_map₂ (hf i (Finset.mem_insert_self _ _))
      (fun n => S.aestronglyMeasurable_fun_prod (fun k hk => hf k (Finset.mem_insert_of_mem hk) n))
      (h i (Finset.mem_insert_self _ _))
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)) (fun k hk => h k (Finset.mem_insert_of_mem hk)))
      (Φ := fun x : ℂ × ℂ => x.1 * x.2) (by fun_prop)
    simpa only [Finset.prod_insert hi] using hprod

theorem tendstoInMeasure_finsetSum {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] (S : Finset ι)
    {f : ι → ℕ → A → ℂ} {g : ι → A → ℂ}
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
      (Φ := fun x : ℂ × ℂ => x.1 + x.2) (by fun_prop)
    simpa only [Finset.sum_insert hi] using hsum


end ModifiedCartan

