import ModifiedCartan.ExponentialTaylorApproximation
import FewInflection.FundamentalAnalytic

open scoped Topology BigOperators
open Filter Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem norm_finset_prod_le_pow {ι : Type*} (S : Finset ι) (u : ι → ℂ)
    {M : ℝ} (_hM : 0 ≤ M) (hu : ∀ i ∈ S, ‖u i‖ ≤ M) :
    ‖∏ i ∈ S, u i‖ ≤ M ^ S.card := by
  calc
    _ ≤ ∏ i ∈ S, ‖u i‖ := Finset.norm_prod_le S u
    _ ≤ ∏ _i ∈ S, M := by
      gcongr with i hi
      exact hu i hi
    _ = _ := by simp

theorem norm_finset_prod_sub_prod_le {ι : Type*} (S : Finset ι) (u v : ι → ℂ)
    {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hu : ∀ i ∈ S, ‖u i‖ ≤ M) (hv : ∀ i ∈ S, ‖v i‖ ≤ M)
    (hd : ∀ i ∈ S, ‖u i - v i‖ ≤ ε) :
    ‖(∏ i ∈ S, u i) - ∏ i ∈ S, v i‖ ≤ ε * S.card * M ^ S.card := by
  classical
  have hM0 : 0 ≤ M := by linarith
  revert hu hv hd
  induction S using Finset.induction_on with
  | empty => intros; simp
  | @insert i S hi ih =>
    intro hu hv hd
    have huS : ∀ j ∈ S, ‖u j‖ ≤ M := fun j hj => hu j (Finset.mem_insert_of_mem hj)
    have hvS : ∀ j ∈ S, ‖v j‖ ≤ M := fun j hj => hv j (Finset.mem_insert_of_mem hj)
    have hdS : ∀ j ∈ S, ‖u j - v j‖ ≤ ε := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    have huP := norm_finset_prod_le_pow S u hM0 huS
    have hdiff := ih huS hvS hdS
    have hdi : ‖u i - v i‖ ≤ ε := hd i (Finset.mem_insert_self i S)
    have hvi : ‖v i‖ ≤ M := hv i (Finset.mem_insert_self i S)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have heq : u i * (∏ j ∈ S, u j) - v i * (∏ j ∈ S, v j) =
        (u i - v i) * (∏ j ∈ S, u j) + v i * ((∏ j ∈ S, u j) - ∏ j ∈ S, v j) := by ring
    rw [heq]
    calc
      _ ≤ ‖(u i - v i) * (∏ j ∈ S, u j)‖ +
          ‖v i * ((∏ j ∈ S, u j) - ∏ j ∈ S, v j)‖ := norm_add_le _ _
      _ = ‖u i - v i‖ * ‖∏ j ∈ S, u j‖ +
          ‖v i‖ * ‖(∏ j ∈ S, u j) - ∏ j ∈ S, v j‖ := by rw [norm_mul, norm_mul]
      _ ≤ ε * M ^ S.card + M * (ε * S.card * M ^ S.card) := by gcongr
      _ ≤ ε * M ^ S.card * M + M * (ε * S.card * M ^ S.card) := by
        exact add_le_add (le_mul_of_one_le_right (by positivity) hM) le_rfl
      _ = _ := by rw [pow_succ, Nat.cast_add, Nat.cast_one]; ring

theorem norm_matrix_det_le_of_entry_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A.det‖ ≤ ((Fintype.card ι).factorial : ℝ) * M ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, M ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_units_zsmul]
      simpa only [Finset.card_univ] using
        norm_finset_prod_le_pow Finset.univ (fun i => A (σ i) i) hM (fun i _ => hA (σ i) i)
    _ = _ := by simp [Fintype.card_perm]

theorem norm_matrix_det_sub_le_of_entry_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hA : ∀ i j, ‖A i j‖ ≤ M) (hB : ∀ i j, ‖B i j‖ ≤ M)
    (hAB : ∀ i j, ‖A i j - B i j‖ ≤ ε) :
    ‖A.det - B.det‖ ≤ ((Fintype.card ι).factorial : ℝ) * ε *
      Fintype.card ι * M ^ Fintype.card ι := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι,
        ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i - Equiv.Perm.sign σ • ∏ i, B (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ε * Fintype.card ι * M ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      rw [← smul_sub, norm_units_zsmul]
      simpa only [Finset.card_univ] using
        norm_finset_prod_sub_prod_le Finset.univ (fun i => A (σ i) i) (fun i => B (σ i) i)
          hM hε (fun i _ => hA (σ i) i) (fun i _ => hB (σ i) i) (fun i _ => hAB (σ i) i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]; ring

theorem norm_wronskian_le_of_jet_bound {n : ℕ} (g : Index n → ℂ → ℂ) (z : ℂ)
    {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ j k, k ≤ n + 1 → ‖iteratedDeriv k (g j) z‖ ≤ M) :
    ‖FewInflection.wronskian n g z‖ ≤ ((n + 1).factorial : ℝ) * M ^ (n + 1) := by
  have he := norm_matrix_det_le_of_entry_bound
    (fun i j : Index n => iteratedDeriv i.val (g j) z) hM
    (fun i j => hg j i.val (by omega))
  simpa only [FewInflection.wronskian, Index, FewInflection.Index, Fintype.card_fin] using he

theorem norm_fundamentalNumerator_le_of_jet_bound {n : ℕ}
    (g : Index n → ℂ → ℂ) (z : ℂ) (i : Index n)
    {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ j k, k ≤ n + 1 → ‖iteratedDeriv k (g j) z‖ ≤ M) :
    ‖FewInflection.fundamentalNumerator n g i z‖ ≤ ((n + 1).factorial : ℝ) * M ^ (n + 1) := by
  let G : Matrix (Index n) (Index n) ℂ := Function.update
    (fun k j => iteratedDeriv k.val (g j) z) i (fun j => -iteratedDeriv (n + 1) (g j) z)
  have hentries : ∀ k j, ‖G k j‖ ≤ M := by
    intro k j
    by_cases hki : k = i
    · subst k
      simpa only [G, Function.update_self, norm_neg] using hg j (n + 1) le_rfl
    · simpa only [G, Function.update_of_ne hki] using hg j k.val (by omega)
  have he := norm_matrix_det_le_of_entry_bound G hM hentries
  simpa only [FewInflection.fundamentalNumerator, G, Index, FewInflection.Index,
    Fintype.card_fin] using he

theorem norm_wronskian_sub_le_of_jet_error {n : ℕ}
    (g h : Index n → ℂ → ℂ) (z : ℂ) {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hg : ∀ j k, k ≤ n + 1 → ‖iteratedDeriv k (g j) z‖ ≤ M)
    (hh : ∀ j k, k ≤ n + 1 → ‖iteratedDeriv k (h j) z‖ ≤ M)
    (hd : ∀ j k, k ≤ n + 1 → ‖iteratedDeriv k (g j) z - iteratedDeriv k (h j) z‖ ≤ ε) :
    ‖FewInflection.wronskian n g z - FewInflection.wronskian n h z‖ ≤
      ((n + 1).factorial : ℝ) * ε * (n + 1) * M ^ (n + 1) := by
  have he := norm_matrix_det_sub_le_of_entry_error
    (fun i j : Index n => iteratedDeriv i.val (g j) z)
    (fun i j : Index n => iteratedDeriv i.val (h j) z) hM hε
    (fun i j => hg j i.val (by omega)) (fun i j => hh j i.val (by omega))
    (fun i j => hd j i.val (by omega))
  simpa only [FewInflection.wronskian, Index, FewInflection.Index, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one] using he

theorem norm_fundamentalNumerator_sub_le_of_jet_error {n : ℕ}
    (g h : Index n → ℂ → ℂ) (z : ℂ) (i : Index n)
    {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hg : ∀ j k, k ≤ n + 1 → ‖iteratedDeriv k (g j) z‖ ≤ M)
    (hh : ∀ j k, k ≤ n + 1 → ‖iteratedDeriv k (h j) z‖ ≤ M)
    (hd : ∀ j k, k ≤ n + 1 → ‖iteratedDeriv k (g j) z - iteratedDeriv k (h j) z‖ ≤ ε) :
    ‖FewInflection.fundamentalNumerator n g i z - FewInflection.fundamentalNumerator n h i z‖ ≤
      ((n + 1).factorial : ℝ) * ε * (n + 1) * M ^ (n + 1) := by
  let G : Matrix (Index n) (Index n) ℂ := Function.update
    (fun k j => iteratedDeriv k.val (g j) z) i (fun j => -iteratedDeriv (n + 1) (g j) z)
  let H : Matrix (Index n) (Index n) ℂ := Function.update
    (fun k j => iteratedDeriv k.val (h j) z) i (fun j => -iteratedDeriv (n + 1) (h j) z)
  have he : ‖G.det - H.det‖ ≤ ((Fintype.card (Index n)).factorial : ℝ) * ε *
      Fintype.card (Index n) * M ^ Fintype.card (Index n) := by
    apply norm_matrix_det_sub_le_of_entry_error G H hM hε
    · intro k j
      by_cases hki : k = i
      · subst k
        simpa only [G, Function.update_self, norm_neg] using hg j (n + 1) le_rfl
      · simpa only [G, Function.update_of_ne hki] using hg j k.val (by omega)
    · intro k j
      by_cases hki : k = i
      · subst k
        simpa only [H, Function.update_self, norm_neg] using hh j (n + 1) le_rfl
      · simpa only [H, Function.update_of_ne hki] using hh j k.val (by omega)
    · intro k j
      by_cases hki : k = i
      · subst k
        simpa only [G, H, Function.update_self, neg_sub_neg, norm_sub_rev] using hd j (n + 1) le_rfl
      · simpa only [G, H, Function.update_of_ne hki] using hd j k.val (by omega)
  simpa only [FewInflection.fundamentalNumerator, G, H, Index, FewInflection.Index,
    Fintype.card_fin, Nat.cast_add, Nat.cast_one] using he

end ModifiedCartan
