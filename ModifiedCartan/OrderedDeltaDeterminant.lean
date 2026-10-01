import ModifiedCartan.AlternantCoefficients

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem strictMono_comp_perm_eq {m : ℕ} (e f : Fin m → ℕ)
    (he : StrictMono e) (hf : StrictMono f) (σ : Equiv.Perm (Fin m))
    (h : e ∘ σ = f) : σ = 1 ∧ e = f := by
  have hs : StrictMono σ := by
    intro i j hij
    by_contra hn
    have hx : e (σ j) ≤ e (σ i) := he.monotone (le_of_not_gt hn)
    have hi := congrFun h i
    have hj := congrFun h j
    change e (σ i) = f i at hi
    change e (σ j) = f j at hj
    rw [hi, hj] at hx
    exact (not_le_of_gt (hf hij)) hx
  have hσ : σ = 1 := Equiv.ext (fun i => congrFun hs.eq_id i)
  exact ⟨hσ, by simpa [hσ] using h⟩

/-- Two strictly increasing finite lists have identity determinant pairing
    precisely when they are equal. Auxiliary to `lem:KP-correspondence`. -/
theorem orderedDeltaMatrix_det {R : Type*} [CommRing R] {m : ℕ}
    (e f : Fin m → ℕ) (he : StrictMono e) (hf : StrictMono f) :
    Matrix.det (fun i j : Fin m => if e i = f j then (1 : R) else 0) =
      if e = f then 1 else 0 := by
  by_cases hef : e = f
  · subst f
    have hM : (fun i j : Fin m => if e i = e j then (1 : R) else 0) =
        (1 : Matrix (Fin m) (Fin m) R) := by
      ext i j
      simp [Matrix.one_apply, he.injective.eq_iff]
    rw [hM, Matrix.det_one, ite_eq_left rfl]
  · rw [ite_eq_right hef]
    erw [Matrix.det_apply]
    apply Finset.sum_eq_zero
    intro σ hσ
    have hn : ∃ i : Fin m, e (σ i) ≠ f i := by
      by_contra hnone
      push Not at hnone
      exact hef (strictMono_comp_perm_eq e f he hf σ (funext hnone)).2
    obtain ⟨i, hi⟩ := hn
    have hp : (∏ j : Fin m, if e (σ j) = f j then (1 : R) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [hp, smul_zero]

end
end ModifiedCartan
