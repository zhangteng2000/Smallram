import FewInflection.Gauge

open scoped BigOperators Topology
open Filter Asymptotics
namespace FewInflection
noncomputable section

def scalarGaugeMatrix (n : ℕ) (g : ℂ → ℂ) (z : ℂ) :
    Matrix (Index n) (Index n) ℂ :=
  fun i k => if (k : ℕ) ≤ (i : ℕ) then
    (Nat.choose (i : ℕ) ((i : ℕ) - (k : ℕ)) : ℂ) *
      iteratedDeriv ((i : ℕ) - (k : ℕ)) g z else 0

lemma scalarGaugeMatrix_lowerTriangular (n : ℕ) (g : ℂ → ℂ) (z : ℂ) :
    (scalarGaugeMatrix n g z).IsLowerTriangular := by
  intro i k hik
  simp only [scalarGaugeMatrix]
  split_ifs with h
  · have hik' : (i : ℕ) < (k : ℕ) := hik
    exact (Nat.not_le_of_lt hik' h).elim
  · rfl

lemma scalarGaugeMatrix_det (n : ℕ) (g : ℂ → ℂ) (z : ℂ)
    (_hg : ContDiffAt ℂ (n : WithTop ℕ∞) g z) :
    (scalarGaugeMatrix n g z).det = g z ^ (n + 1) := by
  rw [Matrix.det_of_isLowerTriangular _
    (scalarGaugeMatrix_lowerTriangular n g z)]
  simp only [scalarGaugeMatrix]
  have hdiag (i : Index n) :
      (if (i : ℕ) ≤ (i : ℕ) then
        (Nat.choose (i : ℕ) ((i : ℕ) - (i : ℕ)) : ℂ) *
          iteratedDeriv ((i : ℕ) - (i : ℕ)) g z else 0) = g z := by
    rw [if_pos (le_refl _)]
    rw [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, one_mul]
    rw [iteratedDeriv_zero]
  simp_rw [hdiag]
  simp [Fintype.card_fin]

lemma sum_fin_if_le {n : ℕ} (i : Fin (n+1)) (G : ℕ → ℂ) :
    (∑ k : Fin (n+1), if (k : ℕ) ≤ (i : ℕ) then G (k : ℕ) else 0) =
      ∑ k ∈ Finset.range ((i : ℕ) + 1), G k := by
  rw [Finset.sum_fin_eq_sum_range]
  have hconvert :
      (∑ k ∈ Finset.range (n+1), if h : k < n+1 then
        (if ((⟨k, h⟩ : Fin (n+1)) : ℕ) ≤ (i : ℕ) then
          G ((⟨k, h⟩ : Fin (n+1)) : ℕ) else 0) else 0) =
        ∑ k ∈ Finset.range (n+1), if k ≤ (i : ℕ) then G k else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.mem_range.mp hk]
  rw [hconvert]
  have hsub : Finset.range ((i : ℕ) + 1) ⊆ Finset.range (n+1) := by
    intro k hk
    apply Finset.mem_range.mpr
    exact lt_of_lt_of_le (Finset.mem_range.mp hk) i.is_lt
  have hbig :
      (∑ k ∈ Finset.range (n+1), if k ≤ (i : ℕ) then G k else 0) =
        ∑ k ∈ Finset.range ((i : ℕ) + 1),
          if k ≤ (i : ℕ) then G k else 0 := by
    symm
    apply Finset.sum_subset hsub
    intro k hk hnot
    have hki : (i : ℕ) < k := by
      exact Nat.lt_of_not_ge (by
        intro hle
        apply hnot
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    simp [not_le_of_gt hki]
  calc
    (∑ k ∈ Finset.range (n+1), if k ≤ (i : ℕ) then G k else 0) =
        ∑ k ∈ Finset.range ((i : ℕ) + 1), if k ≤ (i : ℕ) then G k else 0 := hbig
    _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), G k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [Nat.le_of_lt_succ (Finset.mem_range.mp hk)]

lemma scalarGaugeMatrix_mul_wronskianMatrix
    {n : ℕ} (g : ℂ → ℂ) (f : Index n → ℂ → ℂ) (z : ℂ)
    (hg : ContDiffAt ℂ (n : WithTop ℕ∞) g z)
    (hf : ∀ j : Index n, ContDiffAt ℂ (n : WithTop ℕ∞) (f j) z) :
    let M : Matrix (Index n) (Index n) ℂ :=
      fun (i : Index n) (j : Index n) => iteratedDeriv (i : ℕ) (f j) z
    scalarGaugeMatrix n g z * M =
      (fun (i : Index n) (j : Index n) =>
        iteratedDeriv (i : ℕ) (fun x => g x * f j x) z) := by
  dsimp
  let M : Matrix (Index n) (Index n) ℂ :=
    fun (i : Index n) (j : Index n) => iteratedDeriv (i : ℕ) (f j) z
  change scalarGaugeMatrix n g z * M = _
  funext i j
  change (∑ k : Index n,
      scalarGaugeMatrix n g z i k * iteratedDeriv (k : ℕ) (f j) z) = _
  have hcomm : (fun x => g x * f j x) = (f j) * g := by
    funext x
    simp [mul_comm]
  rw [hcomm]
  rw [iteratedDeriv_mul ((hf j).of_le (by exact_mod_cast i.is_le))
    (hg.of_le (by exact_mod_cast i.is_le))]
  simp only [scalarGaugeMatrix]
  let G : ℕ → ℂ := fun k =>
    (Nat.choose (i : ℕ) ((i : ℕ) - k) : ℂ) *
      iteratedDeriv ((i : ℕ) - k) g z * iteratedDeriv k (f j) z
  let H : ℕ → ℂ := fun k =>
    (Nat.choose (i : ℕ) k : ℂ) *
      iteratedDeriv k (f j) z * iteratedDeriv ((i : ℕ) - k) g z
  calc
    (∑ k : Index n,
        (if (k : ℕ) ≤ (i : ℕ) then
          (Nat.choose (i : ℕ) ((i : ℕ) - (k : ℕ)) : ℂ) *
            iteratedDeriv ((i : ℕ) - (k : ℕ)) g z else 0) *
          iteratedDeriv (k : ℕ) (f j) z) =
        ∑ k : Index n, if (k : ℕ) ≤ (i : ℕ) then G (k : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          split_ifs with h
          · rfl
          · simp
    _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), G k := by
          exact sum_fin_if_le i G
    _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), H k := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [G, H]
          have hki : k ≤ (i : ℕ) := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          rw [Nat.choose_symm hki]
          ring
    _ = ∑ i_1 ∈ Finset.range ((i : ℕ) + 1),
          (Nat.choose (i : ℕ) i_1 : ℂ) *
            iteratedDeriv i_1 (f j) z *
            iteratedDeriv ((i : ℕ) - i_1) g z := by rfl


theorem wronskian_scalar_mul
    {n : ℕ} (g : ℂ → ℂ) (f : Index n → ℂ → ℂ) (z : ℂ)
    (hg : ContDiffAt ℂ (n : WithTop ℕ∞) g z)
    (hf : ∀ j : Index n, ContDiffAt ℂ (n : WithTop ℕ∞) (f j) z) :
    wronskian n (fun j x => g x * f j x) z =
      g z ^ (n + 1) * wronskian n f z := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun (i : Index n) (j : Index n) => iteratedDeriv (i : ℕ) (f j) z
  have hM := scalarGaugeMatrix_mul_wronskianMatrix g f z hg hf
  calc
    wronskian n (fun j x => g x * f j x) z =
        (scalarGaugeMatrix n g z * M).det := by
          simp only [wronskian]
          rw [hM]
    _ = (scalarGaugeMatrix n g z).det * M.det :=
          Matrix.det_mul _ _
    _ = g z ^ (n + 1) * wronskian n f z := by
          rw [scalarGaugeMatrix_det n g z hg]
          rfl

theorem Curve.scalarGauge_wronskian
    {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g) (z : ℂ) :
    wronskian n (f.scalarGauge g hg hgd).coord z =
      g z ^ (n + 1) * wronskian n f.coord z := by
  apply wronskian_scalar_mul g f.coord z
  · exact hgd.contDiff.contDiffAt
  · intro j
    exact (f.holomorphic j).contDiff.contDiffAt

end
end FewInflection

