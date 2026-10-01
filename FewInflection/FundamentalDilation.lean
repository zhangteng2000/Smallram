import FewInflection.Dilation
import FewInflection.FundamentalAnalytic

open scoped BigOperators Topology
namespace FewInflection
noncomputable section

/-- Fundamental-operator coefficients under dilation. -/
theorem fundamentalCoefficients_dilate
    {n : ℕ} (f : Curve n) (t z : ℂ)
    (hW : wronskian n f.coord (t * z) ≠ 0)
    (hWd : wronskian n (f.dilate t).coord z ≠ 0) :
    fundamentalCoefficients n (f.dilate t).coord z =
      (fun i : Index n =>
        t ^ (n + 1 - (i : ℕ)) *
          fundamentalCoefficients n f.coord (t * z) i) := by
  let B : Index n → ℂ := fun i =>
    t ^ (n + 1 - (i : ℕ)) *
      fundamentalCoefficients n f.coord (t * z) i
  have hB : ∀ j : Index n,
      iteratedDeriv (n + 1) ((f.dilate t).coord j) z +
        ∑ i : Index n, B i *
          iteratedDeriv (i : ℕ) ((f.dilate t).coord j) z = 0 := by
    intro j
    have htop := iteratedDeriv_comp_const_mul
      ((f.holomorphic j).contDiff (n := n + 1)) t
    have htopz := congrFun htop z
    change iteratedDeriv (n + 1) (fun x => f.coord j (t * x)) z +
      ∑ i : Index n, B i *
        iteratedDeriv (i : ℕ) (fun x => f.coord j (t * x)) z = 0
    rw [htopz]
    have hsum_dilate :
        (∑ i : Index n, B i *
          iteratedDeriv (i : ℕ) (fun x => f.coord j (t * x)) z) =
          ∑ i : Index n, B i *
            (t ^ (i : ℕ) * iteratedDeriv (i : ℕ) (f.coord j) (t * z)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [iteratedDeriv_dilate f t i j z]
    rw [hsum_dilate]
    have hsum :
        (∑ i : Index n, B i *
            (t ^ (i : ℕ) * iteratedDeriv (i : ℕ) (f.coord j) (t * z))) =
          t ^ (n + 1) *
            ∑ i : Index n, fundamentalCoefficients n f.coord (t * z) i *
              iteratedDeriv (i : ℕ) (f.coord j) (t * z) := by
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi'
      dsimp [B]
      have hile : (i : ℕ) ≤ n := i.is_le
      have hile' : (i : ℕ) ≤ n + 1 := le_trans hile (Nat.le_succ n)
      calc
        t ^ (n + 1 - (i : ℕ)) *
              fundamentalCoefficients n f.coord (t * z) i *
              (t ^ (i : ℕ) * iteratedDeriv (i : ℕ) (f.coord j) (t * z)) =
            (t ^ (n + 1 - (i : ℕ)) * t ^ (i : ℕ)) *
              (fundamentalCoefficients n f.coord (t * z) i *
                iteratedDeriv (i : ℕ) (f.coord j) (t * z)) := by ring
        _ = t ^ (n + 1) *
              (fundamentalCoefficients n f.coord (t * z) i *
                iteratedDeriv (i : ℕ) (f.coord j) (t * z)) := by
              rw [← pow_add, Nat.sub_add_cancel hile']
    rw [hsum]
    have hspec := fundamentalCoefficients_spec hW j
    linear_combination t ^ (n + 1) * hspec
  have hEq := fundamentalCoefficients_unique hWd hB
  exact hEq.symm

/-- For a nonzero dilation, nonvanishing of the original Wronskian supplies
the nonvanishing condition for the transformed operator. -/
theorem fundamentalCoefficients_dilate_of_ne_zero
    {n : ℕ} (f : Curve n) (t z : ℂ) (ht : t ≠ 0)
    (hW : wronskian n f.coord (t * z) ≠ 0) :
    fundamentalCoefficients n (f.dilate t).coord z =
      (fun i : Index n => t ^ (n + 1 - (i : ℕ)) *
        fundamentalCoefficients n f.coord (t * z) i) := by
  apply fundamentalCoefficients_dilate f t z hW
  rw [wronskian_dilate]
  exact mul_ne_zero (pow_ne_zero _ ht) hW

end
end FewInflection



