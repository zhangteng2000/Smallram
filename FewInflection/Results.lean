import FewInflection.Definitions

/-!
# Formal statements of the paper's results

This file records the exact propositions that the analytic part of the paper
has to prove.  It declares no unproved constants.  The propositions are
useful as targets for a future extension of mathlib, while the elementary
consequences below are proved here.
-/

open scoped BigOperators Topology
open Filter Asymptotics

namespace FewInflection

noncomputable section

/-! ## The admissible order set 𝓡_{n+1} -/

def AdmissibleOrder (n : ℕ) (ρ : ℝ) : Prop :=
  ∃ k q : ℕ, 2 ≤ q ∧ q ≤ n + 1 ∧
    ρ = 1 + (k : ℝ) / (q : ℝ)

theorem admissibleOrder_pos {n : ℕ} {ρ : ℝ}
    (hρ : AdmissibleOrder n ρ) : 0 < ρ := by
  rcases hρ with ⟨k, q, hq2, hqn, rfl⟩
  have hq : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq2)
  have hk : (0 : ℝ) ≤ k := by positivity
  positivity

theorem admissibleOrder_ge_one {n : ℕ} {ρ : ℝ}
    (hρ : AdmissibleOrder n ρ) : 1 ≤ ρ := by
  rcases hρ with ⟨k, q, hq2, hqn, rfl⟩
  have hq : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq2)
  have hk : (0 : ℝ) ≤ k := by positivity
  have hfrac : (0 : ℝ) ≤ (k : ℝ) / (q : ℝ) :=
    div_nonneg hk (le_of_lt hq)
  linarith

theorem admissibleOrder_eq_one_iff {n : ℕ} :
    AdmissibleOrder n 1 ↔ 2 ≤ n + 1 := by
  constructor
  · rintro ⟨k, q, hq, hqn, h⟩
    omega
  · intro hn
    refine ⟨0, 2, by decide, ?_, ?_⟩
    · omega
    · norm_num

/-! ## Exact target proposition for the main theorem -/

structure MainConclusion {n : ℕ} (f : Curve n) where
  rho : ℝ
  order_eq_lowerOrder : order f = lowerOrder f
  rho_eq_order : order f = (rho : EReal)
  rho_eq_lowerOrder : lowerOrder f = (rho : EReal)
  admissible : AdmissibleOrder n rho
  regularVariation : RegularlyVarying (characteristic f) rho
  slowlyVarying_factor :
    ∃ ℓ : ℝ → ℝ, SlowlyVarying ℓ ∧
      ∀ᶠ r in atTop, characteristic f r = Real.rpow r rho * ℓ r

def MainTheoremStatement
    {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n →
  f.Transcendental →
  f.linearlyNonDegenerate →
  FiniteLowerOrder f →
  SmallRamification f →
  ∃ ρ : ℝ,
    order f = lowerOrder f ∧
    order f = (ρ : EReal) ∧
    lowerOrder f = (ρ : EReal) ∧
    AdmissibleOrder n ρ ∧
    RegularlyVarying (characteristic f) ρ ∧
    ∃ ℓ : ℝ → ℝ, SlowlyVarying ℓ ∧
      ∀ᶠ r in atTop, characteristic f r = Real.rpow r ρ * ℓ r

theorem mainConclusion_to_statement
    {n : ℕ} {f : Curve n} (h : MainConclusion f) :
    MainTheoremStatement f := by
  intro _ _ _ _ _
  exact ⟨h.rho, h.order_eq_lowerOrder, h.rho_eq_order,
    h.rho_eq_lowerOrder, h.admissible,
    h.regularVariation, h.slowlyVarying_factor⟩

theorem mainStatement_iff_nonempty_mainConclusion
    {n : ℕ} {f : Curve n} :
    MainTheoremStatement f ↔
      (1 ≤ n →
        f.Transcendental →
        f.linearlyNonDegenerate →
        FiniteLowerOrder f →
        SmallRamification f →
        Nonempty (MainConclusion f)) := by
  constructor
  · intro h hn htrans hnd hfinite hsmall
    rcases h hn htrans hnd hfinite hsmall with
      ⟨rho, horder, hrho, hlower, hadm, hreg, hslow⟩
    exact ⟨⟨rho, horder, hrho, hlower, hadm, hreg, hslow⟩⟩
  · intro h hn htrans hnd hfinite hsmall
    rcases h hn htrans hnd hfinite hsmall with ⟨hmain⟩
    exact mainConclusion_to_statement hmain hn htrans hnd hfinite hsmall

/-! ## Exact target proposition for sharpness -/

structure RealizationWitness (n : ℕ) (ρ : ℝ) where
  curve : Curve n
  transcendental : curve.Transcendental
  linearlyNonDegenerate : curve.linearlyNonDegenerate
  wronskian_one : ∀ z, wronskian n curve.coord z = 1
  two_sided_growth :
    ∃ c C r₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        c * Real.rpow r ρ ≤ characteristic curve r ∧
        characteristic curve r ≤ C * Real.rpow r ρ

def SharpnessStatement (n : ℕ) : Prop :=
  1 ≤ n →
  ∀ ρ : ℝ, AdmissibleOrder n ρ →
    ∃ w : RealizationWitness n ρ,
      w.curve.Transcendental ∧
      w.curve.linearlyNonDegenerate ∧
      (∀ z, wronskian n w.curve.coord z = 1)

theorem realizationWitness_to_sharpness
    {n : ℕ} {ρ : ℝ} (w : RealizationWitness n ρ) :
    w.curve.Transcendental ∧
      w.curve.linearlyNonDegenerate ∧
      (∀ z, wronskian n w.curve.coord z = 1) := by
  exact ⟨w.transcendental, w.linearlyNonDegenerate, w.wronskian_one⟩

/-! ## Rational-normal alternative (the order < 1 target) -/

structure RationalNormalForm (n : ℕ) (f : Curve n) where
  A : Matrix (Index n) (Index n) ℂ
  A_invertible : IsUnit A.det
  factor : ∃ g : ℂ → ℂ,
    (∀ z, g z ≠ 0) ∧ Differentiable ℂ g ∧
      ∀ j z, f.coord j z = g z *
        (∑ k : Index n, z ^ (k : ℕ) * A k j)

def monomialCurve_rationalNormalForm (n : ℕ) :
    RationalNormalForm n (monomialCurve n) := by
  refine ⟨1, ?_, fun _ => 1, ?_, ?_, ?_⟩
  · simp
  · intro z
    norm_num
  · fun_prop
  · intro j z
    simp [monomialCurve, monomialFamily, Matrix.one_apply]

theorem smallRamification_of_wronskian_const
    {n : ℕ} (f : Curve n) (w : ℂ)
    (hW : ∀ z, wronskian n f.coord z = w) :
    SmallRamification f := by
  unfold SmallRamification
  rw [ramification_eq_zero_of_wronskian_const f w hW]
  exact isLittleO_zero _ _

def normalizedMonomialGauge_rationalNormalForm (n : ℕ) :
    RationalNormalForm n (normalizedMonomialGauge n) := by
  refine ⟨monomialWronskianNormalization n,
    monomialWronskianNormalization_isUnit n, fun _ => 1, ?_, ?_, ?_⟩
  · intro z
    norm_num
  · fun_prop
  · intro j z
    simp [normalizedMonomialGauge, monomialFamily]

theorem normalizedMonomialGauge_wronskian_one (n : ℕ) :
    ∀ z, wronskian n (normalizedMonomialGauge n).coord z = 1 := by
  intro z
  exact monomialWronskianNormalization_wronskian_one n z

theorem normalizedMonomialGauge_smallRamification (n : ℕ) :
    SmallRamification (normalizedMonomialGauge n) := by
  exact smallRamification_of_wronskian_const
    (normalizedMonomialGauge n) 1
    (normalizedMonomialGauge_wronskian_one n)

theorem monomialCurve_smallRamification (n : ℕ) :
    SmallRamification (monomialCurve n) := by
  unfold SmallRamification
  rw [ramification_monomialCurve]
  exact isLittleO_zero _ _

/- A purely filter-theoretic consequence used by the radial-area corollary.
   The analytic input is isolated in regular variation and the asymptotic
   equivalence `A/T → ρ`; the quotient limit itself is proved here. -/
theorem radial_ratio_of_regularlyVarying
    {T A : ℝ → ℝ} {ρ c : ℝ}
    (hρ : 0 < ρ)
    (hT : RegularlyVarying T ρ)
    (hA : Tendsto (fun r => A r / T r) atTop (𝓝 ρ))
    (hc : 0 < c) :
    Tendsto (fun r => A (c * r) / A r) atTop
      (𝓝 (Real.rpow c ρ)) := by
  have hscale : Tendsto (fun r : ℝ => c * r) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 tendsto_id
  have hA_c : Tendsto (fun r => A (c * r) / T (c * r)) atTop (𝓝 ρ) := by
    simpa [Function.comp_def] using hA.comp hscale
  have hT_ratio : Tendsto (fun r => T (c * r) / T r) atTop
      (𝓝 (Real.rpow c ρ)) := hT.tendsto hc
  have hquot : Tendsto
      (fun r =>
        (A (c * r) / T (c * r) * (T (c * r) / T r)) /
          (A r / T r)) atTop
      (𝓝 ((ρ * Real.rpow c ρ) / ρ)) := by
    exact (hA_c.mul hT_ratio).div hA (ne_of_gt hρ)
  have hne :
      (fun r =>
        (A (c * r) / T (c * r) * (T (c * r) / T r)) /
          (A r / T r)) =ᶠ[atTop]
      (fun r => A (c * r) / A r) := by
    have hAevent : ∀ᶠ r in atTop, A r / T r ≠ 0 :=
      hA.eventually_ne (ne_of_gt hρ)
    have hAevent_c : ∀ᶠ r in atTop, A (c * r) / T (c * r) ≠ 0 :=
      hA_c.eventually_ne (ne_of_gt hρ)
    filter_upwards [hAevent, hAevent_c] with r hr hcr
    have hTr : T r ≠ 0 := by
      intro h
      apply hr
      simp [h]
    have hAr : A r ≠ 0 := by
      intro h
      apply hr
      simp [h]
    have hTcr : T (c * r) ≠ 0 := by
      intro h
      apply hcr
      simp [h]
    field_simp [hTr, hAr, hTcr]
  have hquot' : Tendsto (fun r => A (c * r) / A r) atTop
      (𝓝 ((ρ * Real.rpow c ρ) / ρ)) := hquot.congr' hne
  have hlim : (ρ * Real.rpow c ρ) / ρ = Real.rpow c ρ := by
    field_simp
  simpa only [hlim] using hquot'

def SmallOrderStatement
    {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n →
  f.linearlyNonDegenerate →
  SmallRamification f →
  order f < (1 : EReal) →
  ∃ _h : RationalNormalForm n f, order f = (0 : EReal)

/-! ## Zero-order ramification target -/

def ZeroOrderStatement
    {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n →
  f.Transcendental →
  f.linearlyNonDegenerate →
  order f = (0 : EReal) →
  limsup (fun r => ramification f r / characteristic f r) atTop ≥ 1

/-! ## Radial-area target -/

def RadialArea {n : ℕ} (_f : Curve n) : Type := ℝ → ℝ

def RadialAreaStatement
    {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n →
  ∀ _ftrans : f.Transcendental,
    ∀ _fnd : f.linearlyNonDegenerate,
    ∀ hmain : MainConclusion f,
    ∀ A : RadialArea f,
      Tendsto (fun r => A r / characteristic f r) atTop (𝓝 hmain.rho) →
      ∀ c : ℝ, 0 < c →
        Tendsto (fun r => A (c * r) / A r) atTop
          (𝓝 (Real.rpow c hmain.rho))

theorem radial_area_statement_of_mainConclusion
    {n : ℕ} (f : Curve n) : RadialAreaStatement f := by
  intro _ _ _ hmain A harea c hc
  exact radial_ratio_of_regularlyVarying
    (admissibleOrder_pos hmain.admissible)
    hmain.regularVariation harea hc

end

end FewInflection
