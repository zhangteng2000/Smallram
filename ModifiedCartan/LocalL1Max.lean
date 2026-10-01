import ModifiedCartan.LocalConvergenceAlgebra
import Mathlib.MeasureTheory.Function.LpOrder

open scoped Topology ENNReal
open Filter MeasureTheory Set
set_option autoImplicit false
namespace ModifiedCartan

theorem LocalLpConvergence.max {U : Set ℂ} {f g : ℕ → ℂ → ℝ} {u v : ℂ → ℝ}
    (hf : LocalLpConvergence 1 U f u) (hg : LocalLpConvergence 1 U g v) :
    LocalLpConvergence 1 U (fun ν z => max (f ν z) (g ν z)) (fun z => max (u z) (v z)) where
  source_mem K hK hKU ν := (hf.source_mem K hK hKU ν).sup (hg.source_mem K hK hKU ν)
  limit_mem K hK hKU := (hf.limit_mem K hK hKU).sup (hg.limit_mem K hK hKU)
  tendsto K hK hKU := by
    have hh := (hf.tendsto K hK hKU).add (hg.tendsto K hK hKU)
    simp only [add_zero] at hh
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
    intro ν
    have hfm := (hf.source_mem K hK hKU ν).sub (hf.limit_mem K hK hKU)
    have hgm := (hg.source_mem K hK hKU ν).sub (hg.limit_mem K hK hKU)
    calc
      _ ≤ eLpNorm (fun z => ‖f ν z - u z‖ + ‖g ν z - v z‖) 1 (volume.restrict K) := by
        apply eLpNorm_mono_ae
        exact Eventually.of_forall (fun z => by
          simpa only [Pi.sub_apply, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
            using norm_sup_sub_sup_le_add_norm (f ν z) (g ν z) (u z) (v z))
      _ ≤ eLpNorm (fun z => ‖f ν z - u z‖) 1 (volume.restrict K) +
          eLpNorm (fun z => ‖g ν z - v z‖) 1 (volume.restrict K) :=
        eLpNorm_add_le hfm.norm.aestronglyMeasurable hgm.norm.aestronglyMeasurable le_rfl
      _ = _ := by simp only [← Pi.sub_apply, eLpNorm_norm]

theorem localLpConvergence_finset_sup' {ι : Type*} {U : Set ℂ}
    {f : ι → ℕ → ℂ → ℝ} {u : ι → ℂ → ℝ} (s : Finset ι)
    (hne : s.Nonempty) (h : ∀ i ∈ s, LocalLpConvergence 1 U (f i) (u i)) :
    LocalLpConvergence 1 U (fun ν z => s.sup' hne (fun i => f i ν z))
      (fun z => s.sup' hne (fun i => u i z)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hne).elim
  | @insert a s hnot ih =>
    by_cases hs : s.Nonempty
    · have hh := (h a (Finset.mem_insert_self a s)).max
        (ih hs (fun i hi => h i (Finset.mem_insert_of_mem hi)))
      simpa only [Finset.sup'_insert hs] using hh
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simpa using h a (Finset.mem_insert_self a ∅)

end ModifiedCartan
#print axioms ModifiedCartan.LocalLpConvergence.max
#print axioms ModifiedCartan.localLpConvergence_finset_sup'
