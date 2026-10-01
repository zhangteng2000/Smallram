import ModifiedCartan.KPSubsetWeights

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def kpRootProduct (z : A → ℂ) (i : A) : ℂ :=
  ∏ j ∈ (Finset.univ : Finset A).erase i, (z j - z i)

theorem kpRootProduct_ne_zero (z : A → ℂ) (hz : Function.Injective z) (i : A) :
    kpRootProduct z i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hj).1 (hz he))

theorem kpWeight_at_root_zero (z : A → ℂ) (i : A) (I : Finset A) (hi : i ∉ I) :
    kpWeight z (-z i) I = 0 := by
  apply Finset.prod_eq_zero_iff.mpr
  exact ⟨i, by simp [hi], by simp⟩

theorem kpWeight_singleton_at_root (z : A → ℂ) (i : A) :
    kpWeight z (-z i) {i} = kpRootProduct z i := by
  simp only [kpWeight, kpRootProduct, Finset.sdiff_singleton_eq_erase]
  apply Finset.prod_congr rfl
  intro j hj
  ring

theorem kpRootProduct_eq_mul_pairWeight (z : A → ℂ) (i j : A) (hij : i ≠ j) :
    kpRootProduct z i = (z j - z i) * kpWeight z (-z i) {i, j} := by
  have he : ({i, j} : Finset A).erase j = {i} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hi | hj⟩
      · exact hi
      · exact False.elim (hx hj)
    · rintro rfl
      exact ⟨hij, Or.inl rfl⟩
  have hw := kpWeight_erase z (-z i) {i, j} j (by simp)
  rw [he, kpWeight_singleton_at_root] at hw
  simpa only [sub_eq_add_neg, add_comm] using hw

theorem kpWeight_pair_at_root (z : A → ℂ) (hz : Function.Injective z)
    (i j : A) (hij : i ≠ j) :
    kpWeight z (-z i) {i, j} = kpRootProduct z i * (z j - z i)⁻¹ := by
  have hn : z j - z i ≠ 0 := sub_ne_zero.mpr (fun he => hij (hz he).symm)
  rw [← div_eq_mul_inv]
  apply (eq_div_iff hn).mpr
  rw [mul_comm, ← kpRootProduct_eq_mul_pairWeight z i j hij]

end
end ModifiedCartan


