import ModifiedCartan.AlternantCoefficients
import ModifiedCartan.FiniteRowMinimum
import Mathlib.Data.List.Sort

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem strictAnti_staircase_le {m : ℕ} (e : Fin m → ℕ) (he : StrictAnti e)
    (i : Fin m) : i.rev.val ≤ e i := by
  have hm : StrictMono (fun j : Fin m => e j.rev) :=
    fun _ _ h => he (Fin.rev_strictAnti h)
  simpa only [Fin.rev_rev] using fin_nat_le_strictMono hm i.rev

theorem strictAnti_sub_staircase {m : ℕ} (e : Fin m → ℕ) (he : StrictAnti e) :
    Antitone (fun i : Fin m => e i - i.rev.val) := by
  cases m with
  | zero => intro i; exact Fin.elim0 i
  | succ m =>
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    have hlt := he (show i.castSucc < i.succ by simp)
    have hi := strictAnti_staircase_le e he i.castSucc
    have hj := strictAnti_staircase_le e he i.succ
    simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ] at *
    have := i.isLt
    omega

/-- Every strictly decreasing nonnegative exponent vector is the staircase
    plus the rows of a unique fitting partition (existence form).
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem exists_partitionAlternantExponent {m : ℕ} (e : Fin m → ℕ) (he : StrictAnti e) :
    ∃ μ : YoungDiagram, μ.colLen 0 ≤ m ∧ partitionAlternantExponent m μ = e := by
  let w := List.ofFn (fun i : Fin m => e i - i.rev.val)
  have hw : w.SortedGE := (strictAnti_sub_staircase e he).sortedGE_ofFn
  let μ := YoungDiagram.ofRowLens w hw
  have hr (i : Fin m) : μ.rowLen i.val = e i - i.rev.val := by
    apply eq_of_forall_lt_iff
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    simp only [μ, YoungDiagram.mem_ofRowLens, w, List.length_ofFn, List.getElem_ofFn]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨i.isLt, h⟩⟩
  refine ⟨μ, ?_, ?_⟩
  · by_contra hn
    have hc : (m, 0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    rw [YoungDiagram.mem_ofRowLens] at hc
    simp only [w, List.length_ofFn, lt_self_iff_false, IsEmpty.exists_iff] at hc
  · funext i
    rw [partitionAlternantExponent, hr]
    exact Nat.sub_add_cancel (strictAnti_staircase_le e he i)

theorem exists_perm_strictAnti {m : ℕ} (e : Fin m → ℕ) (he : Function.Injective e) :
    ∃ σ : Equiv.Perm (Fin m), StrictAnti (e ∘ σ) := by
  let s := Finset.univ.image e
  have hs : s.card = m := by simp only [s, Finset.card_image_of_injective _ he,
    Finset.card_univ, Fintype.card_fin]
  let g : Fin m ≃ s := Equiv.ofBijective
    (fun i => (⟨e i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ : s))
    ⟨fun i j h => he (congrArg Subtype.val h), by
      rintro ⟨a, ha⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
      exact ⟨i, Subtype.ext hi⟩⟩
  let σ : Equiv.Perm (Fin m) := Fin.revPerm.trans ((s.orderIsoOfFin hs).toEquiv.trans g.symm)
  have hσ (i : Fin m) : e (σ i) = s.orderEmbOfFin hs i.rev := by
    exact congrArg Subtype.val (g.apply_symm_apply ((s.orderIsoOfFin hs) i.rev))
  refine ⟨σ, ?_⟩
  intro i j hij
  simp only [Function.comp_apply, hσ]
  exact (s.orderEmbOfFin hs).strictMono (Fin.rev_strictAnti hij)

end
end ModifiedCartan

#print axioms ModifiedCartan.exists_partitionAlternantExponent
#print axioms ModifiedCartan.exists_perm_strictAnti
