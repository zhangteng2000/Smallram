import ModifiedCartan.SubharmonicBasic

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem IsSubharmonicOn.sup {U : Set ℂ} {u v : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hv : IsSubharmonicOn U v) :
    IsSubharmonicOn U (fun z => u z ⊔ v z) where
  upperSemicontinuousOn := hu.upperSemicontinuousOn.sup hv.upperSemicontinuousOn
  ne_top z hz := by
    exact ne_of_lt (sup_lt_iff.mpr ⟨lt_top_iff_ne_top.mpr (hu.ne_top z hz),
      lt_top_iff_ne_top.mpr (hv.ne_top z hz)⟩)
  disk_submean c r hr hball M hM := by
    have hum : ∀ z ∈ closedBall c r, u z ≤ (M : EReal) :=
      fun z hz => (le_sup_left : u z ≤ u z ⊔ v z).trans (hM z hz)
    have hvm : ∀ z ∈ closedBall c r, v z ≤ (M : EReal) :=
      fun z hz => (le_sup_right : v z ≤ u z ⊔ v z).trans (hM z hz)
    rcases le_total (u c) (v c) with h | h
    · rw [sup_eq_right.mpr h]
      apply le_trans (lintegral_mono (fun z =>
        EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl le_sup_right)))
      exact hv.disk_submean c r hr hball M hvm
    · rw [sup_eq_left.mpr h]
      apply le_trans (lintegral_mono (fun z =>
        EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl le_sup_left)))
      exact hu.disk_submean c r hr hball M hum

theorem isSubharmonicOn_finset_sup {ι : Type*} {U : Set ℂ}
    (s : Finset ι) (u : ι → ℂ → EReal) (hu : ∀ i ∈ s, IsSubharmonicOn U (u i)) :
    IsSubharmonicOn U (fun z => s.sup (fun i => u i z)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using isSubharmonicOn_bot U
  | @insert a s hnot ih =>
    have ha := hu a (Finset.mem_insert_self a s)
    have hs := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.sup_insert] using ha.sup hs

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.sup
#print axioms ModifiedCartan.isSubharmonicOn_finset_sup
