import FewInflection.DerivativeMinors

/-!
# Ratios of derivative minors

The derivative-minor gauge identity immediately gives the basis-independent
ratios used in the polynomial-space part of the paper.  This file records
that algebraic consequence explicitly, with the nonvanishing hypotheses that
are needed for division.
-/

open scoped BigOperators

namespace FewInflection

noncomputable section

theorem derivativeMinor_ratio_wronskian_matrixGauge
    {n : ℕ} (orders : Index n → ℕ) (f : Index n → ℂ → ℂ)
    (A : Matrix (Index n) (Index n) ℂ) (z : ℂ)
    (hf : ∀ i j : Index n, ContDiffAt ℂ (orders i) (f j) z)
    (hbase : ∀ i j : Index n,
      ContDiffAt ℂ (i : ℕ) (f j) z)
    (hW : wronskian n f z ≠ 0) (hA : A.det ≠ 0) :
    derivativeMinor orders
        (fun j x => ∑ k : Index n, f k x * A k j) z /
        wronskian n (fun j x => ∑ k : Index n, f k x * A k j) z =
      derivativeMinor orders f z / wronskian n f z := by
  rw [derivativeMinor_matrixGauge orders f A z hf]
  rw [show wronskian n (fun j x => ∑ k : Index n, f k x * A k j) z =
      wronskian n f z * A.det by
    simpa only [derivativeMinor_wronskian_special_case] using
      (derivativeMinor_matrixGauge
        (fun i : Index n => (i : ℕ)) f A z hbase)]
  field_simp [hW, hA]

theorem derivativeMinor_ratio_const_matrix_basis_change
    {n : ℕ} (orders : Index n → ℕ)
    (f g : Index n → ℂ → ℂ) (A : Matrix (Index n) (Index n) ℂ)
    (z : ℂ) (hf : ∀ i j : Index n, ContDiffAt ℂ (orders i) (f j) z)
    (hbase : ∀ i j : Index n, ContDiffAt ℂ (i : ℕ) (f j) z)
    (hfg : ∀ j x, g j x = ∑ k : Index n, f k x * A k j)
    (hW : wronskian n f z ≠ 0) (hA : A.det ≠ 0) :
    derivativeMinor orders g z / wronskian n g z =
      derivativeMinor orders f z / wronskian n f z := by
  have hfg' : g = fun j x => ∑ k : Index n, f k x * A k j := by
    funext j x
    exact hfg j x
  rw [hfg']
  exact derivativeMinor_ratio_wronskian_matrixGauge
    orders f A z hf hbase hW hA

end

end FewInflection
