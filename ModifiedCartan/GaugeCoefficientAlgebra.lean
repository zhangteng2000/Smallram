import ModifiedCartan.CanonicalGauge
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Topology.Instances.Matrix

open scoped Topology Classical BigOperators Matrix
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem covariantJet_eq_derivative_order_sum (a f : ℂ → ℂ) (m : ℕ) (z : ℂ) :
    covariantJet a f m z = ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℂ) * logarithmicJet a (m - i) z * iteratedDeriv i f z := by
  unfold covariantJet
  rw [← Finset.sum_range_reflect (fun k =>
    (m.choose k : ℂ) * logarithmicJet a k z * iteratedDeriv (m - k) f z) (m + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  have hr : m - (m - i) = i := by omega
  simp only [Nat.add_sub_cancel, hr, Nat.choose_symm hi']

theorem covariantJet_eq_sum_fin (a f : ℂ → ℂ) {m n : ℕ} (hm : m ≤ n) (z : ℂ) :
    covariantJet a f m z = ∑ i : Index n,
      (m.choose i.val : ℂ) * logarithmicJet a (m - i.val) z * iteratedDeriv i.val f z := by
  rw [covariantJet_eq_derivative_order_sum]
  change (∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℂ) * logarithmicJet a (m - i) z * iteratedDeriv i f z) =
      ∑ i : Fin (n + 1), (m.choose i.val : ℂ) * logarithmicJet a (m - i.val) z * iteratedDeriv i.val f z
  rw [← Finset.sum_range (n := n + 1)
    (fun i => (m.choose i : ℂ) * logarithmicJet a (m - i) z * iteratedDeriv i f z)]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i hi hn
  have hmi : m < i := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  rw [Nat.choose_eq_zero_of_lt hmi, Nat.cast_zero, zero_mul, zero_mul]

theorem covariantJet_top_eq (a f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    covariantJet a f (n + 1) z = iteratedDeriv (n + 1) f z +
      ∑ i : Index n, ((n + 1).choose i.val : ℂ) *
        logarithmicJet a (n + 1 - i.val) z * iteratedDeriv i.val f z := by
  rw [covariantJet_eq_derivative_order_sum, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, logarithmicJet, one_mul]
  rw [Finset.sum_range, add_comm]

theorem canonical_covariant_relation {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hW : FewInflection.wronskian n g z ≠ 0)
    (j : Index n) :
    covariantJet (canonicalLogDerivative n g) (g j) (n + 1) z +
      ∑ i : Index n, canonicalCoefficient n g i z *
        covariantJet (canonicalLogDerivative n g) (g j) i.val z = 0 := by
  obtain ⟨η, hη, hη0, hroot⟩ := exists_canonical_gauge_nhds hg hW
  have he := ((Filter.eventually_all.mpr (fun j => (hg j).eventually_analyticAt)).and
    hη.eventually_analyticAt).and hroot
  obtain ⟨U, hsub, hU, hz⟩ := _root_.eventually_nhds_iff.mp he
  have hgU (j : Index n) : AnalyticOnNhd ℂ (g j) U := fun w hw => (hsub w hw).1.1 j
  have hηU : AnalyticOnNhd ℂ η U := fun w hw => (hsub w hw).1.2
  have hrU : ∀ w ∈ U, η w ^ (n + 1) * FewInflection.wronskian n g w = 1 :=
    fun w hw => (hsub w hw).2
  have haU : AnalyticOnNhd ℂ (canonicalLogDerivative n g) U := by
    intro w hw
    apply analyticAt_canonicalLogDerivative (fun j => hgU j w hw)
    intro hw0
    have hr := hrU w hw
    simp only [hw0, mul_zero, zero_ne_one] at hr
  have hderiv : ∀ w ∈ U, deriv η w = canonicalLogDerivative n g w * η w :=
    fun w hw => normalizing_factor_deriv hU hgU hηU (fun w _ => hη0 w) hrU hw
  have hjet (m : ℕ) : iteratedDeriv m (fun w => η w * g j w) z =
      η z * covariantJet (canonicalLogDerivative n g) (g j) m z :=
    iteratedDeriv_mul_eq_covariantJet hU haU hηU (hgU j) hderiv m hz
  have hWη : FewInflection.wronskian n (fun j w => η w * g j w) z ≠ 0 := by
    rw [FewInflection.wronskian_scalar_mul η g z hη.contDiffAt (fun j => (hg j).contDiffAt),
      hrU z hz]
    exact one_ne_zero
  have hc (i : Index n) := canonicalCoefficient_eq_normalized_nhds hg hη hroot i
  have hspec := FewInflection.fundamentalCoefficients_spec hWη j
  simp_rw [← hc, hjet] at hspec
  have heq : η z * (covariantJet (canonicalLogDerivative n g) (g j) (n + 1) z +
      ∑ i : Index n, canonicalCoefficient n g i z *
        covariantJet (canonicalLogDerivative n g) (g j) i.val z) = 0 := by
    convert! hspec using 1
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact (mul_eq_zero.mp heq).resolve_left (hη0 z)

/-- Exact triangular relation obtained by expanding the normalized
fundamental equation. Auxiliary to LaTeX `eq:gaugecomparison`. -/
theorem canonical_coefficient_triangular_relation {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hW : FewInflection.wronskian n g z ≠ 0)
    (i : Index n) :
    FewInflection.fundamentalCoefficients n g z i =
      ((n + 1).choose i.val : ℂ) * logarithmicJet (canonicalLogDerivative n g) (n + 1 - i.val) z +
      ∑ k : Index n, canonicalCoefficient n g k z * (k.val.choose i.val : ℂ) *
        logarithmicJet (canonicalLogDerivative n g) (k.val - i.val) z := by
  let a := canonicalLogDerivative n g
  let b : Index n → ℂ := fun i => ((n + 1).choose i.val : ℂ) * logarithmicJet a (n + 1 - i.val) z +
    ∑ k : Index n, canonicalCoefficient n g k z * (k.val.choose i.val : ℂ) * logarithmicJet a (k.val - i.val) z
  have hb : b = FewInflection.fundamentalCoefficients n g z := by
    apply FewInflection.fundamentalCoefficients_unique hW
    intro j
    have hspec := canonical_covariant_relation hg hW j
    rw [covariantJet_top_eq] at hspec
    have hk (k : Index n) := covariantJet_eq_sum_fin a (g j) (n := n)
      (by omega : k.val ≤ n) z
    dsimp only [a] at hk
    simp_rw [hk] at hspec
    simp only [b, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
      Finset.mul_sum, mul_assoc] at hspec ⊢
    rw [Finset.sum_comm]
    simpa only [a, add_assoc] using hspec
  exact (congrFun hb i).symm

def jetTransitionMatrix (n : ℕ) (v : ℕ → ℂ) : Matrix (Index n) (Index n) ℂ :=
  fun k i => (k.val.choose i.val : ℂ) * v (k.val - i.val)

def jetLeadingRow (n : ℕ) (v : ℕ → ℂ) : Index n → ℂ :=
  fun i => ((n + 1).choose i.val : ℂ) * v (n + 1 - i.val)

theorem jetTransitionMatrix_det (n : ℕ) (v : ℕ → ℂ) (hv : v 0 = 1) :
    (jetTransitionMatrix n v).det = 1 := by
  have htri : (jetTransitionMatrix n v).IsLowerTriangular := by
    intro i j hij
    have hlt : i.val < j.val := hij
    simp only [jetTransitionMatrix, Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simp only [jetTransitionMatrix, Nat.choose_self, Nat.cast_one, Nat.sub_self, hv,
    one_mul, Finset.prod_const_one]

theorem weighted_gauge_product_div {N k i : ℕ} (hk : k ≤ N) (hi : i ≤ k)
    (b d t s : ℂ) :
    (b * d * t) / s ^ (N - i) =
      (b / s ^ (N - k)) * d * (t / s ^ (k - i)) := by
  have hp : s ^ (N - i) = s ^ (N - k) * s ^ (k - i) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem canonical_normalized_coefficient_vecMul {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hW : FewInflection.wronskian n g z ≠ 0) (s : ℝ) :
    (fun i : Index n => canonicalCoefficient n g i z / (s : ℂ) ^ (n + 1 - i.val)) ᵥ*
      jetTransitionMatrix n (fun k => logarithmicJet (canonicalLogDerivative n g) k z / (s : ℂ) ^ k) =
      (fun i : Index n => FewInflection.fundamentalCoefficients n g z i / (s : ℂ) ^ (n + 1 - i.val)) -
        jetLeadingRow n (fun k => logarithmicJet (canonicalLogDerivative n g) k z / (s : ℂ) ^ k) := by
  ext i
  let a := canonicalLogDerivative n g
  have he : FewInflection.fundamentalCoefficients n g z i / (s : ℂ) ^ (n + 1 - i.val) =
      jetLeadingRow n (fun k => logarithmicJet a k z / (s : ℂ) ^ k) i +
      ∑ k : Index n, (canonicalCoefficient n g k z / (s : ℂ) ^ (n + 1 - k.val)) *
        jetTransitionMatrix n (fun k => logarithmicJet a k z / (s : ℂ) ^ k) k i := by
    rw [canonical_coefficient_triangular_relation hg hW i, add_div, Finset.sum_div]
    congr 1
    · dsimp [jetLeadingRow]
      ring
    · apply Finset.sum_congr rfl
      intro k _
      dsimp [jetTransitionMatrix]
      by_cases hik : i.val ≤ k.val
      · simpa only [mul_assoc] using weighted_gauge_product_div
          (by omega : k.val ≤ n + 1) hik (canonicalCoefficient n g k z)
          (k.val.choose i.val : ℂ) (logarithmicJet a (k.val - i.val) z) (s : ℂ)
      · have hki : k.val < i.val := by omega
        simp only [Nat.choose_eq_zero_of_lt hki, Nat.cast_zero, mul_zero, zero_mul, zero_div]
  change (∑ k : Index n, _) = _
  dsimp only [Pi.sub_apply]
  dsimp only [a] at he
  linear_combination -he

/-- The gauge transformation is an explicit polynomial in the normalized
jets: the lower triangular transition matrix has determinant one, so its
adjugate gives the exact inverse. Auxiliary to `eq:gaugecomparison`. -/
theorem canonical_normalized_coefficient_adjugate {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hW : FewInflection.wronskian n g z ≠ 0) (s : ℝ) :
    (fun i : Index n => canonicalCoefficient n g i z / (s : ℂ) ^ (n + 1 - i.val)) =
      ((fun i : Index n => FewInflection.fundamentalCoefficients n g z i / (s : ℂ) ^ (n + 1 - i.val)) -
        jetLeadingRow n (fun k => logarithmicJet (canonicalLogDerivative n g) k z / (s : ℂ) ^ k)) ᵥ*
      (jetTransitionMatrix n (fun k => logarithmicJet (canonicalLogDerivative n g) k z /
        (s : ℂ) ^ k)).adjugate := by
  let v := fun k => logarithmicJet (canonicalLogDerivative n g) k z / (s : ℂ) ^ k
  have hv : v 0 = 1 := by simp [v, logarithmicJet]
  rw [← canonical_normalized_coefficient_vecMul hg hW s, Matrix.vecMul_vecMul,
    Matrix.mul_adjugate, jetTransitionMatrix_det n v hv, one_smul, Matrix.vecMul_one]

def finiteJetTransitionMatrix (n : ℕ) (v : Fin (n + 2) → ℂ) : Matrix (Index n) (Index n) ℂ :=
  fun k i => (k.val.choose i.val : ℂ) * v ⟨k.val - i.val, by omega⟩

def finiteJetLeadingRow (n : ℕ) (v : Fin (n + 2) → ℂ) : Index n → ℂ :=
  fun i => ((n + 1).choose i.val : ℂ) * v ⟨n + 1 - i.val, by omega⟩

def zeroGaugeJet (n : ℕ) : Fin (n + 2) → ℂ := fun k => if k.val = 0 then 1 else 0

def coefficientGaugePolynomial (n : ℕ) (b : Index n → ℂ) (v : Fin (n + 2) → ℂ) : Index n → ℂ :=
  (b - finiteJetLeadingRow n v) ᵥ* (finiteJetTransitionMatrix n v).adjugate

theorem finiteJetTransitionMatrix_zeroGaugeJet (n : ℕ) :
    finiteJetTransitionMatrix n (zeroGaugeJet n) = 1 := by
  ext k i
  by_cases hki : k = i
  · subst k
    simp [finiteJetTransitionMatrix, zeroGaugeJet, Matrix.one_apply]
  · have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
    by_cases hlt : k.val < i.val
    · simp [finiteJetTransitionMatrix, Nat.choose_eq_zero_of_lt hlt, Matrix.one_apply, hki]
    · have hpos : k.val - i.val ≠ 0 := by omega
      simp [finiteJetTransitionMatrix, zeroGaugeJet, hpos, Matrix.one_apply, hki]

theorem finiteJetLeadingRow_zeroGaugeJet (n : ℕ) :
    finiteJetLeadingRow n (zeroGaugeJet n) = 0 := by
  ext i
  have hpos : n + 1 - i.val ≠ 0 := by omega
  simp [finiteJetLeadingRow, zeroGaugeJet, hpos]

theorem coefficientGaugePolynomial_zeroGaugeJet (n : ℕ) (b : Index n → ℂ) :
    coefficientGaugePolynomial n b (zeroGaugeJet n) = b := by
  rw [coefficientGaugePolynomial, finiteJetLeadingRow_zeroGaugeJet, finiteJetTransitionMatrix_zeroGaugeJet,
    sub_zero, Matrix.adjugate_one, Matrix.vecMul_one]

theorem coefficientGaugePolynomial_continuous (n : ℕ) :
    Continuous (fun x : (Index n → ℂ) × (Fin (n + 2) → ℂ) =>
      coefficientGaugePolynomial n x.1 x.2) := by
  unfold coefficientGaugePolynomial finiteJetLeadingRow finiteJetTransitionMatrix
  apply Continuous.matrix_vecMul
  · fun_prop
  · apply Continuous.matrix_adjugate
    fun_prop

theorem canonical_normalized_coefficient_eq_polynomial {n : ℕ}
    {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hW : FewInflection.wronskian n g z ≠ 0) (s : ℝ) :
    (fun i : Index n => canonicalCoefficient n g i z / (s : ℂ) ^ (n + 1 - i.val)) =
      coefficientGaugePolynomial n
        (fun i => FewInflection.fundamentalCoefficients n g z i / (s : ℂ) ^ (n + 1 - i.val))
        (fun k => logarithmicJet (canonicalLogDerivative n g) k.val z / (s : ℂ) ^ k.val) := by
  exact canonical_normalized_coefficient_adjugate hg hW s

end
end ModifiedCartan
#print axioms ModifiedCartan.canonical_coefficient_triangular_relation
#print axioms ModifiedCartan.canonical_normalized_coefficient_adjugate
#print axioms ModifiedCartan.canonical_normalized_coefficient_eq_polynomial
