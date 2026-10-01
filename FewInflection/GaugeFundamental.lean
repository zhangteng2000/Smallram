import FewInflection.MatrixGaugeBounds
import FewInflection.FundamentalAnalytic

open scoped BigOperators Topology

namespace FewInflection

noncomputable section

/-! The fundamental relation is unchanged by an invertible constant change of
coordinates.  This is the coefficient-level form of gauge invariance used in
the canonical-operator construction. -/

theorem fundamentalCoefficients_matrixGauge
    {n : ℕ} (f : Curve n) (A : Matrix (Index n) (Index n) ℂ)
    (hA : IsUnit A.det) {z : ℂ}
    (hW : wronskian n f.coord z ≠ 0) :
    fundamentalCoefficients n (f.matrixGauge A hA).coord z =
      fundamentalCoefficients n f.coord z := by
  have hWg : wronskian n (f.matrixGauge A hA).coord z ≠ 0 := by
    rw [Curve.matrixGauge_wronskian]
    exact mul_ne_zero hW hA.ne_zero
  symm
  apply fundamentalCoefficients_unique hWg
  intro j
  have hspec := fundamentalCoefficients_spec (g := f.coord) hW
  have hderiv : ∀ (m : ℕ),
      iteratedDeriv m ((f.matrixGauge A hA).coord j) z =
        ∑ k : Index n, iteratedDeriv m (f.coord k) z * A k j := by
    intro m
    change iteratedDeriv m
      (fun x : ℂ => ∑ k : Index n, f.coord k x * A k j) z = _
    rw [iteratedDeriv_fun_sum]
    · simp only [iteratedDeriv_mul_const_field]
    · intro k hk
      have hAk : AnalyticOnNhd ℂ (f.coord k) Set.univ :=
        Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic k)
      simpa [smul_eq_mul] using
        (hAk z (Set.mem_univ z)).contDiffAt.smul_const (A k j)
  rw [hderiv (n + 1)]
  simp_rw [hderiv]
  have hsum : (∑ k : Index n,
          (iteratedDeriv (n + 1) (f.coord k) z +
            ∑ i : Index n, fundamentalCoefficients n f.coord z i *
              iteratedDeriv (i : ℕ) (f.coord k) z) * A k j) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hspec k, zero_mul]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul] at hsum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simpa only [mul_assoc] using hsum

end

end FewInflection
