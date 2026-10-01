import FewInflection.Jensen

open scoped BigOperators Topology
open Filter

namespace FewInflection

noncomputable section

theorem differentiable_wronskian {n : ℕ} (f : Curve n) :
    Differentiable ℂ (fun z : ℂ => wronskian n f.coord z) := by
  classical
  have hcont (j : Index n) :
      ContDiff ℂ (⊤ : WithTop ℕ∞) (f.coord j) := by
    have hA : AnalyticOnNhd ℂ (f.coord j) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)
    exact contDiffOn_univ.mp (hA.contDiffOn_of_completeSpace)
  have hentry (i j : Index n) :
      Differentiable ℂ (fun z : ℂ => iteratedDeriv (i : ℕ) (f.coord j) z) := by
    exact (hcont j).differentiable_iteratedDeriv (i : ℕ) (by simp)
  unfold wronskian
  have hdet :
      (fun z : ℂ => Matrix.det (fun (i j : Index n) =>
        iteratedDeriv (i : ℕ) (f.coord j) z)) =
      (fun z : ℂ => ∑ σ : Equiv.Perm (Index n),
        Equiv.Perm.sign σ • ∏ i : Index n,
          iteratedDeriv ((σ i : Index n) : ℕ) (f.coord i) z) := by
    funext z
    exact Matrix.det_apply (n := Index n) (R := ℂ)
      (fun (i j : Index n) => iteratedDeriv (i : ℕ) (f.coord j) z)
  rw [hdet]
  apply Differentiable.fun_sum
  intro σ hσ
  apply Differentiable.const_smul
  apply Differentiable.fun_finsetProd
  intro i hi
  exact hentry (σ i) i

theorem wronskian_zero_or_nonzero_codiscrete {n : ℕ} (f : Curve n) :
    (∀ z, wronskian n f.coord z = 0) ∨
      (fun z : ℂ => wronskian n f.coord z) ⁻¹' ({0}ᶜ : Set ℂ) ∈ codiscrete ℂ := by
  classical
  have hA : AnalyticOnNhd ℂ (fun z : ℂ => wronskian n f.coord z) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_wronskian f)
  by_cases hzero : ∀ z, wronskian n f.coord z = 0
  · exact Or.inl hzero
  · right
    obtain ⟨z, hz⟩ := not_forall.mp hzero
    exact hA.preimage_zero_mem_codiscrete hz

theorem ramification_eq_circleAverage_sub_const_of_wronskian_nezero
    {n : ℕ} (f : Curve n) (hW0 : wronskian n f.coord 0 ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    ramification f r =
      Real.circleAverage
          (fun z : ℂ => Real.log ‖wronskian n f.coord z‖) 0 r -
        Real.log ‖wronskian n f.coord 0‖ := by
  exact ramification_eq_circleAverage_sub_const_of_wronskian_nezero_at_zero
    f (differentiable_wronskian f) hW0 hr

theorem ramification_nonneg_of_wronskian_nezero_at_zero
    {n : ℕ} (f : Curve n) (hW0 : wronskian n f.coord 0 ≠ 0)
    {r : ℝ} (hr : 0 < r) : 0 ≤ ramification f r := by
  rw [ramification_eq_circleAverage_sub_const_of_wronskian_nezero f hW0 hr]
  exact scalar_circleAverage_log_norm_sub_nonneg
    (differentiable_wronskian f) hr hW0

end

end FewInflection
