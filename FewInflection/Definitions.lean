import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Definitions for holomorphic curves with few inflection points

The paper uses the Euclidean norm on a homogeneous vector.  The finite
function space below carries mathlib's canonical finite-product norm; all
finite-dimensional norms are equivalent, and this is a convenient exact
choice for a formal development.
-/

open scoped BigOperators Topology
open Filter Asymptotics

namespace FewInflection

noncomputable section

abbrev Index (n : ℕ) := Fin (n + 1)

structure Curve (n : ℕ) where
  coord : Index n → ℂ → ℂ
  holomorphic : ∀ j, Differentiable ℂ (coord j)
  reduced : ∀ z, ∃ j, coord j z ≠ 0

namespace Curve

instance (n : ℕ) : CoeFun (Curve n) (fun _ => Index n → ℂ → ℂ) :=
  ⟨Curve.coord⟩

def vector {n : ℕ} (f : Curve n) : ℂ → (Index n → ℂ) :=
  fun z j => f.coord j z

theorem vector_ne_zero {n : ℕ} (f : Curve n) (z : ℂ) :
    f.vector z ≠ 0 := by
  intro hv
  rcases f.reduced z with ⟨j, hj⟩
  apply hj
  exact congrFun hv j

def linearlyNonDegenerate {n : ℕ} (f : Curve n) : Prop :=
  LinearIndependent ℂ f.coord

/- A polynomial representation is the algebraic form of the rational
   alternative used in the paper. -/
def HasPolynomialRepresentation {n : ℕ} (f : Curve n) : Prop :=
  ∃ (p : Index n → Polynomial ℂ) (g : ℂ → ℂ),
    (∀ z, g z ≠ 0) ∧ Differentiable ℂ g ∧
      ∀ j z, f.coord j z = g z * (p j).eval z

def Transcendental {n : ℕ} (f : Curve n) : Prop := ¬ f.HasPolynomialRepresentation

end Curve

def wronskian (n : ℕ) (f : Index n → ℂ → ℂ) (z : ℂ) : ℂ :=
  Matrix.det (fun (i : Index n) (j : Index n) =>
    iteratedDeriv (i : ℕ) (f j) z)

def monomialFamily (n : ℕ) : Index n → ℂ → ℂ :=
  fun j z => z ^ (j : ℕ)

theorem linearlyIndependent_of_wronskian_ne_zero
    {n : ℕ} (f : Index n → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i j : Index n, ContDiffAt ℂ (i : ℕ) (f j) z)
    (hW : wronskian n f z ≠ 0) :
    LinearIndependent ℂ f := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun i j => iteratedDeriv (i : ℕ) (f j) z
  have hdet : M.det ≠ 0 := by
    simpa [M, wronskian] using hW
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hmv : M.mulVec g = 0 := by
    funext i
    have hd := congrArg
      (fun h : ℂ → ℂ => iteratedDeriv (i : ℕ) h z) hg
    have hsum :
        (∑ k : Index n, g k • f k) =
          (fun x : ℂ => ∑ k : Index n, g k • f k x) := by
      funext x
      simp
    rw [hsum] at hd
    rw [iteratedDeriv_fun_sum] at hd
    · simpa [smul_eq_mul, Matrix.mulVec, dotProduct, M, mul_comm] using hd
    · intro k hk
      exact (hf i k).const_smul (g k)
  have hg0 : g = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
  exact congrFun hg0 j

def monomialCurve (n : ℕ) : Curve n where
  coord := monomialFamily n
  holomorphic := by
    intro j
    change Differentiable ℂ (fun z : ℂ => z ^ (j : ℕ))
    exact differentiable_id.pow (j : ℕ)
  reduced := by
    intro z
    refine ⟨0, ?_⟩
    simp [monomialFamily]

theorem monomialCurve_linearlyNonDegenerate (n : ℕ) :
    Curve.linearlyNonDegenerate (monomialCurve n) := by
  change LinearIndependent ℂ (monomialFamily n)
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hd := congrArg
    (fun h : ℂ → ℂ => iteratedDeriv (j : ℕ) h 0) hg
  have hsum :
      (∑ i : Index n, g i • monomialFamily n i) =
        (fun z : ℂ => ∑ i : Index n, g i • monomialFamily n i z) := by
    funext z
    simp
  have hd' := hd
  rw [hsum] at hd'
  rw [iteratedDeriv_fun_sum] at hd'
  · simp only [iteratedDeriv_fun_const_smul_field] at hd'
    have hjet (i : Index n) :
        iteratedDeriv (j : ℕ) (monomialFamily n i) 0 =
          if i = j then (Nat.factorial (j : ℕ) : ℂ) else 0 := by
      change iteratedDeriv (j : ℕ) (fun z : ℂ => z ^ (i : ℕ)) 0 = _
      rw [iteratedDeriv_pow]
      by_cases hij : i = j
      · subst i
        simp [Nat.descFactorial_self]
      · simp only [hij, ite_false]
        by_cases hlt : (i : ℕ) < (j : ℕ)
        · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
        · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
          have hpos : 0 < (i : ℕ) - (j : ℕ) := by omega
          simp [zero_pow (Nat.ne_of_gt hpos)]
    simp_rw [hjet] at hd'
    have hfac : (Nat.factorial (j : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (j : ℕ)
    simpa [hfac] using hd'
  · intro i hi
    exact (contDiffAt_id.pow (i : ℕ)).const_smul (g i)

theorem monomialCurve_hasPolynomialRepresentation (n : ℕ) :
    (monomialCurve n).HasPolynomialRepresentation := by
  refine ⟨fun j => Polynomial.X ^ (j : ℕ), fun _ => 1, ?_, ?_, ?_⟩
  · intro z
    norm_num
  · fun_prop
  · intro j z
    simp [monomialCurve, monomialFamily]

theorem monomialCurve_notTranscendental (n : ℕ) :
    ¬(monomialCurve n).Transcendental := by
  intro h
  exact h (monomialCurve_hasPolynomialRepresentation n)

theorem wronskian_monomialFamily (n : ℕ) (z : ℂ) :
    wronskian n (monomialFamily n) z =
      ∏ j : Index n, (Nat.factorial (j : ℕ) : ℂ) := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun i j => iteratedDeriv (i : ℕ) (monomialFamily n j) z
  have hupper : M.IsUpperTriangular := by
    intro i j hij
    have hlt : (j : ℕ) < (i : ℕ) := by exact hij
    change iteratedDeriv (i : ℕ) (fun x : ℂ => x ^ (j : ℕ)) z = 0
    rw [iteratedDeriv_pow]
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
  change M.det = _
  rw [Matrix.det_of_isUpperTriangular hupper]
  simp only [M]
  apply Finset.prod_congr rfl
  intro i hi
  change iteratedDeriv (i : ℕ) (fun x : ℂ => x ^ (i : ℕ)) z =
    (Nat.factorial (i : ℕ) : ℂ)
  rw [iteratedDeriv_pow, Nat.descFactorial_self]
  simp

theorem wronskian_monomialFamily_ne_zero (n : ℕ) (z : ℂ) :
    wronskian n (monomialFamily n) z ≠ 0 := by
  rw [wronskian_monomialFamily]
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => by
    exact_mod_cast Nat.factorial_ne_zero (j : ℕ))

/-! The characteristic and ramification functions used throughout the paper. -/

noncomputable def characteristic {n : ℕ} (f : Curve n) : ℝ → ℝ :=
  fun r =>
    Real.circleAverage (fun z : ℂ => Real.log ‖Curve.vector f z‖) 0 r -
      Real.log ‖Curve.vector f 0‖

theorem characteristic_zero {n : ℕ} (f : Curve n) :
    characteristic f 0 = 0 := by
  unfold characteristic
  simp

noncomputable def ramification {n : ℕ} (f : Curve n) : ℝ → ℝ :=
  ValueDistribution.logCounting (fun z => wronskian n f.coord z)
    (0 : WithTop ℂ)

/- The order is an extended real number: the quotient may have an infinite
   limsup/liminf, and `EReal` records those possibilities explicitly. -/
def logGrowthRatio {n : ℕ} (f : Curve n) (r : ℝ) : EReal :=
  ((Real.log (max (characteristic f r) 1) /
    Real.log (max r 2) : ℝ) : EReal)

theorem logGrowthRatio_nonneg {n : ℕ} (f : Curve n) {r : ℝ} (_hr : 2 ≤ r) :
    0 ≤ logGrowthRatio f r := by
  unfold logGrowthRatio
  have hnum : 0 ≤ Real.log (max (characteristic f r) 1) := by
    apply Real.log_nonneg
    exact le_max_right _ _
  have hden : 0 < Real.log (max r 2) := by
    apply Real.log_pos
    have hmax : 2 ≤ max r 2 := le_max_right _ _
    linarith
  have hquot : 0 ≤ Real.log (max (characteristic f r) 1) /
      Real.log (max r 2) := div_nonneg hnum (le_of_lt hden)
  exact_mod_cast hquot

theorem logGrowthRatio_eventually_nonneg {n : ℕ} (f : Curve n) :
    0 ≤ᶠ[atTop] logGrowthRatio f := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  exact logGrowthRatio_nonneg f hr

noncomputable def order {n : ℕ} (f : Curve n) : EReal :=
  limsup (logGrowthRatio f) atTop

noncomputable def lowerOrder {n : ℕ} (f : Curve n) : EReal :=
  liminf (logGrowthRatio f) atTop

def FiniteLowerOrder {n : ℕ} (f : Curve n) : Prop :=
  lowerOrder f < (⊤ : EReal)

def SmallRamification {n : ℕ} (f : Curve n) : Prop :=
  (fun r => ramification f r) =o[atTop] (fun r => characteristic f r)

/- The paper uses Karamata's definition: a slowly varying factor is positive
   and continuous on the positive half-line, with convergence uniform for
   multipliers in `[1, 2]`.  The epsilon form below avoids hiding that
   uniformity in an interface constant. -/
def SlowlyVarying (ℓ : ℝ → ℝ) : Prop :=
  (∀ r, 0 < r → 0 < ℓ r) ∧
  ContinuousOn ℓ (Set.Ioi 0) ∧
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ∀ r, R < r → ∀ c ∈ Set.Icc (1 : ℝ) 2,
      |ℓ (c * r) / ℓ r - 1| < ε

/- Regular variation is recorded in the locally uniform form used in the
   theorem: every compact set of positive multipliers has uniform convergence.
 -/
def RegularlyVarying (T : ℝ → ℝ) (ρ : ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 →
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ r, R < r → ∀ c ∈ K,
        |T (c * r) / T r - Real.rpow c ρ| < ε

theorem RegularlyVarying.tendsto
    {T : ℝ → ℝ} {ρ c : ℝ} (h : RegularlyVarying T ρ) (hc : 0 < c) :
    Tendsto (fun r => T (c * r) / T r) atTop
      (𝓝 (Real.rpow c ρ)) := by
  rw [Metric.tendsto_atTop']
  intro ε hε
  rcases h {c} isCompact_singleton (by
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ hc) ε hε with
    ⟨R, hR, hbound⟩
  refine ⟨R, ?_⟩
  intro r hr
  simpa [Real.dist_eq] using hbound r hr c (by simp)

theorem RegularlyVarying.unique
    {T : ℝ → ℝ} {ρ σ : ℝ}
    (hρ : RegularlyVarying T ρ) (hσ : RegularlyVarying T σ) : ρ = σ := by
  have hlim : Real.rpow 2 ρ = Real.rpow 2 σ :=
    tendsto_nhds_unique (hρ.tendsto (by norm_num)) (hσ.tendsto (by norm_num))
  exact (Real.strictMono_rpow_of_base_gt_one (by norm_num)).injective hlim

theorem regularlyVarying_rpow (ρ : ℝ) :
    RegularlyVarying (fun r : ℝ => Real.rpow r ρ) ρ := by
  intro K hK hKpos ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro r hr c hc
  have hcpos : 0 < c := hKpos hc
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hden : Real.rpow r ρ ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hrpos ρ)
  have hmul : Real.rpow (c * r) ρ = Real.rpow c ρ * Real.rpow r ρ := by
    exact Real.mul_rpow (le_of_lt hcpos) (le_of_lt hrpos)
  change |Real.rpow (c * r) ρ / Real.rpow r ρ - Real.rpow c ρ| < ε
  rw [hmul]
  field_simp
  simp
  exact hε

theorem slowlyVarying_one : SlowlyVarying (fun _ : ℝ => 1) := by
  refine ⟨?_, continuousOn_const, ?_⟩
  · intro r hr
    norm_num
  · intro ε hε
    refine ⟨1, by norm_num, ?_⟩
    intro r hr c hc
    norm_num
    exact hε

theorem slowlyVarying_div_rpow_of_regularlyVarying
    {T : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hTpos : ∀ r, 0 < r → 0 < T r)
    (hTcont : ContinuousOn T (Set.Ioi 0))
    (hreg : RegularlyVarying T ρ) :
    SlowlyVarying (fun r : ℝ => T r / Real.rpow r ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact div_pos (hTpos r hr) (Real.rpow_pos_of_pos hr ρ)
  · apply hTcont.div
      (continuousOn_id.rpow_const (fun x hx => Or.inr hρ))
    intro r hr
    exact ne_of_gt (Real.rpow_pos_of_pos hr ρ)
  · intro ε hε
    rcases hreg (Set.Icc (1 : ℝ) 2) isCompact_Icc (by
      intro c hc
      exact lt_of_lt_of_le zero_lt_one hc.1) ε hε with
      ⟨R, hR, hbound⟩
    refine ⟨max R 1, lt_max_of_lt_right zero_lt_one, ?_⟩
    intro r hr c hc
    have hrR : R < r := lt_of_le_of_lt (le_max_left _ _) hr
    have hr1 : 1 < r := lt_of_le_of_lt (le_max_right _ _) hr
    have hrpos : 0 < r := lt_trans zero_lt_one hr1
    have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc.1
    have hcrpos : 0 < c * r := mul_pos hcpos hrpos
    have hTr : T r ≠ 0 := ne_of_gt (hTpos r hrpos)
    have hTcr : T (c * r) ≠ 0 := ne_of_gt (hTpos (c * r) hcrpos)
    have hpr : Real.rpow r ρ ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hrpos ρ)
    have hpcr : Real.rpow (c * r) ρ ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hcrpos ρ)
    have hcpowpos : 0 < Real.rpow c ρ := Real.rpow_pos_of_pos hcpos ρ
    have hcpowge : 1 ≤ Real.rpow c ρ := Real.one_le_rpow hc.1 hρ
    have hmul : Real.rpow (c * r) ρ = Real.rpow c ρ * Real.rpow r ρ := by
      exact Real.mul_rpow (le_of_lt hcpos) (le_of_lt hrpos)
    have heq :
        T (c * r) / Real.rpow (c * r) ρ /
              (T r / Real.rpow r ρ) - 1 =
          (T (c * r) / T r - Real.rpow c ρ) / Real.rpow c ρ := by
      field_simp [hTr, hTcr, hpr, hpcr, ne_of_gt hcpowpos]
      rw [hmul]
      ring
    have hscaled :
        |T (c * r) / T r - Real.rpow c ρ| / Real.rpow c ρ < ε := by
      apply (div_lt_iff₀ hcpowpos).2
      have hb := hbound r hrR c hc
      nlinarith [abs_nonneg (T (c * r) / T r - Real.rpow c ρ)]
    change |T (c * r) / Real.rpow (c * r) ρ /
              (T r / Real.rpow r ρ) - 1| < ε
    rw [heq, abs_div]
    rw [abs_of_pos hcpowpos]
    exact hscaled

theorem regularlyVarying_factor_of_pos_continuous
    {T : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hTpos : ∀ r, 0 < r → 0 < T r)
    (hTcont : ContinuousOn T (Set.Ioi 0))
    (hreg : RegularlyVarying T ρ) :
    ∃ ℓ : ℝ → ℝ, SlowlyVarying ℓ ∧
      ∀ᶠ r in atTop, T r = Real.rpow r ρ * ℓ r := by
  refine ⟨fun r => T r / Real.rpow r ρ,
    slowlyVarying_div_rpow_of_regularlyVarying hρ hTpos hTcont hreg, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hrpos ρ)]

/-! Constant scalar multiplication is the elementary gauge identity used in
Section 2 of the paper.  Iterated derivatives are supplied with the local
`ContDiffAt` hypotheses required by mathlib's derivative convention. -/
theorem wronskian_const_gauge
    {n : ℕ} (f : Index n → ℂ → ℂ) (c : ℂ) (z : ℂ)
    (hf : ∀ i j : Index n, ContDiffAt ℂ (i : ℕ) (f j) z) :
    wronskian n (fun j x => c * f j x) z =
      c ^ (n + 1) * wronskian n f z := by
  let N : Matrix (Index n) (Index n) ℂ :=
    fun (i : Index n) (j : Index n) => iteratedDeriv (i : ℕ) (f j) z
  have hM :
      (fun (i : Index n) (j : Index n) =>
        iteratedDeriv (i : ℕ) (fun x => c * f j x) z) =
        c • N := by
    funext i j
    rw [iteratedDeriv_const_mul c (hf i j)]
    change c * iteratedDeriv (i : ℕ) (f j) z =
      c * iteratedDeriv (i : ℕ) (f j) z
    rfl
  calc
    wronskian n (fun j x => c * f j x) z = (c • N).det := by
      simp only [wronskian, hM]
    _ = c ^ Fintype.card (Index n) * N.det := Matrix.det_smul N c
    _ = c ^ (n + 1) * wronskian n f z := by
      rw [Fintype.card_fin]
      rfl

/- A constant change of the homogeneous coordinates acts on the Wronskian by
   the determinant of the change-of-coordinates matrix. -/
theorem wronskian_matrix_gauge
    {n : ℕ} (f : Index n → ℂ → ℂ) (A : Matrix (Index n) (Index n) ℂ)
    (z : ℂ)
    (hf : ∀ i j : Index n, ContDiffAt ℂ (i : ℕ) (f j) z) :
    wronskian n (fun j x => ∑ k : Index n, f k x * A k j) z =
      wronskian n f z * A.det := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun (i : Index n) (j : Index n) => iteratedDeriv (i : ℕ) (f j) z
  have hM :
      (fun (i : Index n) (j : Index n) =>
        iteratedDeriv (i : ℕ) (fun x => ∑ k : Index n, f k x * A k j) z) =
        M * A := by
    funext i j
    change iteratedDeriv (i : ℕ) (fun x => ∑ k : Index n, f k x * A k j) z =
      ∑ k : Index n, iteratedDeriv (i : ℕ) (f k) z * A k j
    rw [iteratedDeriv_fun_sum]
    · simp only [iteratedDeriv_mul_const_field]
    · intro k hk
      simpa [smul_eq_mul] using (hf i k).smul_const (A k j)
  calc
    wronskian n (fun j x => ∑ k : Index n, f k x * A k j) z = (M * A).det := by
      simp only [wronskian, hM]
    _ = M.det * A.det := Matrix.det_mul M A
    _ = wronskian n f z * A.det := by rfl

theorem wronskian_matrix_gauge_ne_zero
    {n : ℕ} (f : Index n → ℂ → ℂ)
    (A : Matrix (Index n) (Index n) ℂ) (z : ℂ)
    (hf : ∀ i j : Index n, ContDiffAt ℂ (i : ℕ) (f j) z)
    (hW : wronskian n f z ≠ 0) (hA : IsUnit A.det) :
    wronskian n (fun j x => ∑ k : Index n, f k x * A k j) z ≠ 0 := by
  rw [wronskian_matrix_gauge f A z hf]
  exact mul_ne_zero hW hA.ne_zero

theorem wronskian_monomial_matrix_gauge
    (n : ℕ) (A : Matrix (Index n) (Index n) ℂ) (z : ℂ) :
    wronskian n (fun j x => ∑ k : Index n, monomialFamily n k x * A k j) z =
      (∏ k : Index n, (Nat.factorial (k : ℕ) : ℂ)) * A.det := by
  rw [wronskian_matrix_gauge (monomialFamily n) A z]
  · rw [wronskian_monomialFamily]
  · intro i j
    exact (contDiffAt_id.pow (j : ℕ))

noncomputable def monomialWronskianConstant (n : ℕ) : ℂ :=
  ∏ j : Index n, (Nat.factorial (j : ℕ) : ℂ)

noncomputable def monomialWronskianNormalization (n : ℕ) :
    Matrix (Index n) (Index n) ℂ :=
  Matrix.diagonal (fun i =>
    if i = 0 then (monomialWronskianConstant n)⁻¹ else 1)

theorem monomialWronskianConstant_ne_zero (n : ℕ) :
    monomialWronskianConstant n ≠ 0 := by
  unfold monomialWronskianConstant
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => by
    exact_mod_cast Nat.factorial_ne_zero (j : ℕ))

theorem monomialWronskianNormalization_det (n : ℕ) :
    (monomialWronskianNormalization n).det =
      (monomialWronskianConstant n)⁻¹ := by
  rw [monomialWronskianNormalization, Matrix.det_diagonal]
  simp [monomialWronskianConstant]

theorem monomialWronskianNormalization_isUnit (n : ℕ) :
    IsUnit (monomialWronskianNormalization n).det := by
  rw [monomialWronskianNormalization_det]
  exact isUnit_iff_ne_zero.mpr (inv_ne_zero (monomialWronskianConstant_ne_zero n))

theorem monomialWronskianNormalization_wronskian_one (n : ℕ) :
    ∀ z, wronskian n
      (fun j x => ∑ k : Index n,
        monomialFamily n k x * monomialWronskianNormalization n k j) z = 1 := by
  intro z
  rw [wronskian_monomial_matrix_gauge]
  rw [monomialWronskianNormalization_det]
  change monomialWronskianConstant n *
      (monomialWronskianConstant n)⁻¹ = 1
  exact mul_inv_cancel₀ (monomialWronskianConstant_ne_zero n)

noncomputable def normalizedMonomialGauge (n : ℕ) : Curve n where
  coord := fun j x => ∑ k : Index n,
    monomialFamily n k x * monomialWronskianNormalization n k j
  holomorphic := by
    intro j
    change Differentiable ℂ (fun x : ℂ =>
      ∑ k : Index n, x ^ (k : ℕ) * monomialWronskianNormalization n k j)
    fun_prop
  reduced := by
    intro z
    refine ⟨0, ?_⟩
    classical
    simp [monomialWronskianNormalization, monomialFamily, Matrix.diagonal,
      monomialWronskianConstant_ne_zero]

theorem normalizedMonomialGauge_linearlyNonDegenerate (n : ℕ) :
    (normalizedMonomialGauge n).linearlyNonDegenerate := by
  unfold Curve.linearlyNonDegenerate
  apply linearlyIndependent_of_wronskian_ne_zero
    (normalizedMonomialGauge n).coord 0
  · intro i j
    change ContDiffAt ℂ (i : ℕ) (fun x : ℂ =>
      ∑ k : Index n, x ^ (k : ℕ) * monomialWronskianNormalization n k j) 0
    fun_prop
  · simpa [normalizedMonomialGauge]
      using congrArg (fun w : ℂ => w ≠ 0)
        (monomialWronskianNormalization_wronskian_one n 0)

theorem wronskian_monomial_matrix_gauge_ne_zero
    (n : ℕ) (A : Matrix (Index n) (Index n) ℂ)
    (hA : IsUnit A.det) (z : ℂ) :
    wronskian n (fun j x => ∑ k : Index n, monomialFamily n k x * A k j) z ≠ 0 := by
  have hf : ∀ i j : Index n, ContDiffAt ℂ (i : ℕ) (monomialFamily n j) z := by
    intro i j
    change ContDiffAt ℂ (i : ℕ) (fun x : ℂ => x ^ (j : ℕ)) z
    exact contDiffAt_id.pow (j : ℕ)
  rw [wronskian_matrix_gauge (f := monomialFamily n) A z hf]
  exact mul_ne_zero (wronskian_monomialFamily_ne_zero n z) hA.ne_zero

theorem ramification_eq_zero_of_wronskian_const
    {n : ℕ} (f : Curve n) (w : ℂ)
    (hW : ∀ z, wronskian n f.coord z = w) :
    ramification f = (fun _ : ℝ => 0) := by
  funext r
  unfold ramification
  have hfun :
      (fun z : ℂ => wronskian n f.coord z) = (fun _ : ℂ => w) := by
    funext z
    exact hW z
  rw [hfun]
  simp

theorem ramification_monomialCurve (n : ℕ) :
    ramification (monomialCurve n) = (fun _ : ℝ => 0) := by
  apply ramification_eq_zero_of_wronskian_const (monomialCurve n)
    (∏ j : Index n, (Nat.factorial (j : ℕ) : ℂ))
  intro z
  simpa [monomialCurve] using wronskian_monomialFamily n z

end

end FewInflection
