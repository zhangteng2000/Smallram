import ModifiedCartan.Counting

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem local_proximity_congr {f g : ℂ → ℂ} {r : ℝ} (hr : r ≠ 0)
    (heq : f =ᶠ[codiscreteWithin (sphere 0 |r|)] g) :
    ValueDistribution.proximity f ⊤ r = ValueDistribution.proximity g ⊤ r := by
  rw [ValueDistribution.proximity_top, ValueDistribution.proximity_top]
  apply Real.circleAverage_congr_codiscreteWithin _ hr
  filter_upwards [heq] with z hz
  rw [hz]

theorem local_proximity_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) {r : ℝ}
    (hf : ∀ i ∈ S, MeromorphicOn (f i) (sphere 0 |r|)) :
    ValueDistribution.proximity (fun z => ∑ i ∈ S, f i z) ⊤ r ≤
      (∑ i ∈ S, ValueDistribution.proximity (f i) ⊤ r) + Real.log S.card := by
  have hsum : MeromorphicOn (fun z => ∑ i ∈ S, f i z) (sphere 0 |r|) :=
    fun z hz => MeromorphicAt.fun_sum (fun i hi => hf i hi z hz)
  have hi (i : ι) (hi : i ∈ S) := (hf i hi).circleIntegrable_posLog_norm
  have his : CircleIntegrable (fun z => ∑ i ∈ S, Real.posLog ‖f i z‖) 0 r := by
    convert CircleIntegrable.sum S hi using 1
    ext z
    simp
  rw [ValueDistribution.proximity_top]
  calc
    _ ≤ Real.circleAverage (fun z => (∑ i ∈ S, Real.posLog ‖f i z‖) + Real.log S.card) 0 r :=
      Real.circleAverage_mono hsum.circleIntegrable_posLog_norm
        (his.add (circleIntegrable_const _ _ _)) (fun z _ => by
          simpa only [add_comm] using Real.posLog_norm_sum_le S (fun i => f i z))
    _ = _ := by
      rw [Real.circleAverage_fun_add his (circleIntegrable_const _ _ _),
        Real.circleAverage_fun_sum hi, Real.circleAverage_const]
      simp only [ValueDistribution.proximity_top]

theorem local_proximity_add_le {f g : ℂ → ℂ} {r : ℝ}
    (hf : MeromorphicOn f (sphere 0 |r|)) (hg : MeromorphicOn g (sphere 0 |r|)) :
    ValueDistribution.proximity (fun z => f z + g z) ⊤ r ≤
      ValueDistribution.proximity f ⊤ r + ValueDistribution.proximity g ⊤ r + Real.log 2 := by
  simpa using local_proximity_sum_le Finset.univ ![f, g]
    (fun i _ => by fin_cases i <;> assumption)

theorem local_proximity_prod_le {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) {r : ℝ}
    (hf : ∀ i ∈ S, MeromorphicOn (f i) (sphere 0 |r|)) :
    ValueDistribution.proximity (fun z => ∏ i ∈ S, f i z) ⊤ r ≤
      ∑ i ∈ S, ValueDistribution.proximity (f i) ⊤ r := by
  have hi (i : ι) (hi : i ∈ S) := (hf i hi).circleIntegrable_posLog_norm
  have his : CircleIntegrable (fun z => ∑ i ∈ S, Real.posLog ‖f i z‖) 0 r := by
    convert CircleIntegrable.sum S hi using 1
    ext z
    simp
  rw [ValueDistribution.proximity_top]
  calc
    _ ≤ Real.circleAverage (fun z => ∑ i ∈ S, Real.posLog ‖f i z‖) 0 r :=
      Real.circleAverage_mono (MeromorphicOn.fun_prod hf).circleIntegrable_posLog_norm his
        (fun z _ => by simpa only [norm_prod] using Real.posLog_prod S (fun i => ‖f i z‖))
    _ = _ := by
      rw [Real.circleAverage_fun_sum hi]
      simp only [ValueDistribution.proximity_top]

theorem local_proximity_le_of_norm_le {f : ℂ → ℂ} {r C : ℝ}
    (hf : MeromorphicOn f (sphere 0 |r|)) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ sphere (0 : ℂ) |r|, ‖f z‖ ≤ C) :
    ValueDistribution.proximity f ⊤ r ≤ Real.posLog C := by
  rw [ValueDistribution.proximity_top]
  exact Real.circleAverage_mono_on_of_le_circle hf.circleIntegrable_posLog_norm
    (fun z hz => Real.monotoneOn_posLog (norm_nonneg _) hC (hbound z hz))

end ModifiedCartan
#print axioms ModifiedCartan.local_proximity_sum_le
#print axioms ModifiedCartan.local_proximity_prod_le
