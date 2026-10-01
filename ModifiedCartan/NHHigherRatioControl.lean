import ModifiedCartan.NHLogDerivativeControl
import ModifiedCartan.LogDerivativePartitions

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The exact partition expansion converts the proved estimates for derivatives
of logDeriv into estimates for D_k f / f, uniformly in the original function. -/
theorem exists_NH_ratio_control_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (r ρ B : ℝ),
      0 < r → r < ρ → 1 ≤ B → ρ ≤ B → (ρ - r)⁻¹ ≤ B → r⁻¹ ≤ B →
      MeromorphicOn f (closedBall 0 ρ) → AnalyticAt ℂ f 0 → f 0 ≠ 0 →
      diskCharacteristic f ρ ≤ B → Real.posLog (1 / ‖f 0‖) ≤ B →
      ValueDistribution.proximity (fun z => iteratedDeriv k f z / f z) ⊤ r ≤
        C * (1 + Real.log B) := by
  classical
  choose C hCpos hC using exists_NH_logDeriv_control_bound
  let D : ℝ := ∑ c : OrderedFinpartition k, ∑ i, C (c.partSize i - 1)
  let N : ℝ := Real.log (Fintype.card (OrderedFinpartition k))
  have hD : 0 ≤ D := Finset.sum_nonneg (fun c _ =>
    Finset.sum_nonneg (fun i _ => (hCpos (c.partSize i - 1)).le))
  refine ⟨1 + D + |N|, by positivity, fun f r ρ B hr hrρ hB hρB hδB hrB hf hfa h0 hTB h0B => ?_⟩
  have hρ := hr.trans hrρ
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hsp : sphere (0 : ℂ) |r| ⊆ closedBall 0 ρ := by
    rw [abs_of_pos hr]
    exact sphere_subset_closedBall.trans (closedBall_subset_closedBall hrρ.le)
  let J : ℕ → ℂ → ℂ := fun m => iteratedDeriv m (logDeriv f)
  let G : OrderedFinpartition k → ℂ → ℂ := fun c z => ∏ i, J (c.partSize i - 1) z
  have hJ (m : ℕ) : MeromorphicOn (J m) (sphere 0 |r|) :=
    (meromorphic_iteratedDeriv_on hf.logDeriv m).mono_set hsp
  have hG (c : OrderedFinpartition k) : MeromorphicOn (G c) (sphere 0 |r|) :=
    MeromorphicOn.fun_prod (fun i _ => hJ (c.partSize i - 1))
  have hGbound (c : OrderedFinpartition k) :
      ValueDistribution.proximity (G c) ⊤ r ≤
        (∑ i, C (c.partSize i - 1)) * (1 + Real.log B) := by
    calc
      _ ≤ ∑ i, ValueDistribution.proximity (J (c.partSize i - 1)) ⊤ r :=
        local_proximity_prod_le Finset.univ (fun i => J (c.partSize i - 1)) (fun i _ => hJ _)
      _ ≤ ∑ i, C (c.partSize i - 1) * (1 + Real.log B) :=
        Finset.sum_le_sum (fun i _ => hC (c.partSize i - 1) f r ρ B hr hrρ hB hρB hδB hrB
          hf hfa h0 hTB h0B)
      _ = _ := by rw [Finset.sum_mul]
  have hsum := local_proximity_sum_le Finset.univ G (fun c _ => hG c)
  have hsumBound : (∑ c : OrderedFinpartition k, ValueDistribution.proximity (G c) ⊤ r) ≤
      D * (1 + Real.log B) := by
    calc
      _ ≤ ∑ c : OrderedFinpartition k, (∑ i, C (c.partSize i - 1)) * (1 + Real.log B) :=
        Finset.sum_le_sum (fun c _ => hGbound c)
      _ = _ := by rw [← Finset.sum_mul]
  have hn := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hf
    (disk_meromorphic_order_ne_top hρ hf hfa h0)
  have heq : (fun z => iteratedDeriv k f z / f z) =ᶠ[codiscreteWithin (closedBall 0 ρ)]
      (fun z => ∑ c : OrderedFinpartition k, G c z) := by
    filter_upwards [hf.analyticAt_mem_codiscreteWithin, hn] with z hz hz0
    exact iteratedDeriv_div_eq_partition hz hz0 k
  rw [local_proximity_congr hr.ne' (heq.filter_mono (codiscreteWithin_mono hsp))]
  have hmain := hsum.trans (add_le_add hsumBound le_rfl)
  simp only [Finset.card_univ] at hmain
  change ValueDistribution.proximity (fun z => ∑ c : OrderedFinpartition k, G c z) ⊤ r ≤
    D * (1 + Real.log B) + N at hmain
  exact hmain.trans (by nlinarith [le_abs_self N, mul_nonneg (abs_nonneg N) hlogB])

end ModifiedCartan
#print axioms ModifiedCartan.exists_NH_ratio_control_bound
