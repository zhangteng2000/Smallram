import FewInflection.AffineDilation
import FewInflection.FundamentalAnalytic

open scoped BigOperators Topology
namespace FewInflection
noncomputable section

/-! Fundamental-operator coefficients under the affine rescaling used in
local blow-up arguments.  Translation contributes no derivative factor; all
orders acquire the same power of the nonzero scale. -/
theorem fundamentalCoefficients_affineDilate
    {n : ℕ} (f : Curve n) (a t z : ℂ)
    (hW : wronskian n f.coord (a + t * z) ≠ 0)
    (hWa : wronskian n (f.affineDilate a t).coord z ≠ 0) :
    fundamentalCoefficients n (f.affineDilate a t).coord z =
      (fun i : Index n =>
        t ^ (n + 1 - (i : ℕ)) *
          fundamentalCoefficients n f.coord (a + t * z) i) := by
  let B : Index n → ℂ := fun i =>
    t ^ (n + 1 - (i : ℕ)) *
      fundamentalCoefficients n f.coord (a + t * z) i
  have hB : ∀ j : Index n,
      iteratedDeriv (n + 1) ((f.affineDilate a t).coord j) z +
        ∑ i : Index n, B i *
          iteratedDeriv (i : ℕ) ((f.affineDilate a t).coord j) z = 0 := by
    intro j
    have htop := iteratedDeriv_comp_const_add (n + 1) (f.coord j) a
    have htop' := congrFun htop (t * z)
    let g : ℂ → ℂ := fun y => f.coord j (a + y)
    have hg : ContDiff ℂ (n + 1) g := by
      exact ((f.holomorphic j).contDiff (n := n + 1)).comp
        (contDiff_const.add contDiff_id)
    have hscale := iteratedDeriv_comp_const_mul hg t
    have hscale' := congrFun hscale z
    dsimp [g] at hscale'
    change iteratedDeriv (n + 1) (fun x => f.coord j (a + t * x)) z +
      ∑ i : Index n, B i *
        iteratedDeriv (i : ℕ) (fun x => f.coord j (a + t * x)) z = 0
    rw [hscale']
    rw [htop']
    have hsum_dilate :
        (∑ i : Index n, B i *
          iteratedDeriv (i : ℕ) (fun x => f.coord j (a + t * x)) z) =
          ∑ i : Index n, B i *
            (t ^ (i : ℕ) * iteratedDeriv (i : ℕ) (f.coord j) (a + t * z)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [iteratedDeriv_affineDilate f a t i j z]
    rw [hsum_dilate]
    have hsum :
        (∑ i : Index n, B i *
            (t ^ (i : ℕ) * iteratedDeriv (i : ℕ) (f.coord j) (a + t * z))) =
          t ^ (n + 1) *
            ∑ i : Index n, fundamentalCoefficients n f.coord (a + t * z) i *
              iteratedDeriv (i : ℕ) (f.coord j) (a + t * z) := by
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi'
      dsimp [B]
      have hile : (i : ℕ) ≤ n := i.is_le
      have hile' : (i : ℕ) ≤ n + 1 := le_trans hile (Nat.le_succ n)
      calc
        t ^ (n + 1 - (i : ℕ)) *
              fundamentalCoefficients n f.coord (a + t * z) i *
              (t ^ (i : ℕ) * iteratedDeriv (i : ℕ) (f.coord j) (a + t * z)) =
            (t ^ (n + 1 - (i : ℕ)) * t ^ (i : ℕ)) *
              (fundamentalCoefficients n f.coord (a + t * z) i *
                iteratedDeriv (i : ℕ) (f.coord j) (a + t * z)) := by ring
        _ = t ^ (n + 1) *
              (fundamentalCoefficients n f.coord (a + t * z) i *
                iteratedDeriv (i : ℕ) (f.coord j) (a + t * z)) := by
              rw [← pow_add, Nat.sub_add_cancel hile']
    rw [hsum]
    have hspec := fundamentalCoefficients_spec hW j
    linear_combination t ^ (n + 1) * hspec
  have hEq := fundamentalCoefficients_unique hWa hB
  exact hEq.symm

theorem fundamentalCoefficients_affineDilate_of_ne_zero
    {n : ℕ} (f : Curve n) (a t z : ℂ) (ht : t ≠ 0)
    (hW : wronskian n f.coord (a + t * z) ≠ 0) :
    fundamentalCoefficients n (f.affineDilate a t).coord z =
      (fun i : Index n =>
        t ^ (n + 1 - (i : ℕ)) *
          fundamentalCoefficients n f.coord (a + t * z) i) := by
  apply fundamentalCoefficients_affineDilate f a t z hW
  rw [wronskian_affineDilate]
  exact mul_ne_zero (pow_ne_zero _ ht) hW

end
end FewInflection
