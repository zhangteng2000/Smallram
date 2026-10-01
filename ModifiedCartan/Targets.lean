import ModifiedCartan.NormComparison
import FewInflection.Results

/-!
Literal targets for the submitted manuscript with its Euclidean characteristic.
These definitions specify propositions. None is a proof of the named paper result.
Their eventual proofs must have precisely these types, without added hypotheses.
-/

open scoped BigOperators Topology
open Filter

namespace ModifiedCartan

/-- LaTeX label `thm:main`. Reserved proof name: `Paper.thm_main`. -/
def MainTheoremTarget {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n → f.Transcendental → f.linearlyNonDegenerate →
    FiniteLowerOrder f → SmallRamification f →
      ∃ ρ : ℝ, order f = (ρ : EReal) ∧ lowerOrder f = (ρ : EReal) ∧
        FewInflection.AdmissibleOrder n ρ ∧
        ∃ ℓ : ℝ → ℝ, FewInflection.SlowlyVarying ℓ ∧
          ∀ᶠ r in atTop, characteristic f r = Real.rpow r ρ * ℓ r

/-- Initial-value system in LaTeX label `eq:sharpness-equation`. -/
def IsSharpnessSystem (n k q : ℕ) (g : Index n → ℂ → ℂ) : Prop :=
  (∀ j, Differentiable ℂ (g j)) ∧
  (∀ i j : Index n, iteratedDeriv (i : ℕ) (g j) 0 = if i = j then 1 else 0) ∧
  ∀ j z, iteratedDeriv (n + 1) (g j) z =
    z ^ k * iteratedDeriv (n + 1 - q) (g j) z

/-- Existence of the entire normalized solution system is a separate obligation. -/
def SharpnessSystemExistenceTarget (n k q : ℕ) : Prop :=
  1 ≤ n → 2 ≤ q → q ≤ n + 1 → ∃ g, IsSharpnessSystem n k q g

/-- LaTeX label `prop:sharpness-orders`, including its prescribed initial data
and exact asymptotic constant. Reserved proof name: `Paper.prop_sharpness_orders`. -/
def SharpnessOrdersTarget (n k q : ℕ) (g : Index n → ℂ → ℂ) : Prop :=
  1 ≤ n → 2 ≤ q → q ≤ n + 1 → IsSharpnessSystem n k q g →
    ∃ f : Curve n, f.coord = g ∧ f.Transcendental ∧ f.linearlyNonDegenerate ∧
      (∀ z, FewInflection.wronskian n g z = 1) ∧
      Tendsto (fun r => characteristic f r / Real.rpow r (1 + (k : ℝ) / q)) atTop
        (𝓝 ((q : ℝ) * Real.sin (Real.pi / q) /
          (Real.pi * (1 + (k : ℝ) / q))))

/-- LaTeX label `prop:small-order`. Reserved proof name:
`Paper.prop_small_order`. -/
def SmallOrderTarget {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n → f.linearlyNonDegenerate → SmallRamification f →
    order f < (1 : EReal) →
      Nonempty (FewInflection.RationalNormalForm n f)

/-- LaTeX labels `cor:zero-ratio`, `prop:zero-order-ramification`.
The limsup is extended-real valued, so an unbounded ratio is not assigned zero. -/
def ZeroRatioTarget {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n → f.Transcendental → f.linearlyNonDegenerate → order f = (0 : EReal) →
    (1 : EReal) ≤ limsup
      (fun r => (ramification f r / characteristic f r : ℝ) : ℝ → EReal) atTop

/-- The explicit infinite product in LaTeX label `eq:zero-sharp-example`. -/
noncomputable def zeroSharpFunction (z : ℂ) : ℂ :=
  ∏' j : ℕ, (1 + Complex.exp (-((j + 1 : ℕ) : ℂ)) * z)

noncomputable def zeroSharpCoordinates (n : ℕ) (j : Index n) (z : ℂ) : ℂ :=
  if (j : ℕ) < n then z ^ (j : ℕ) else zeroSharpFunction z

/-- LaTeX label `prop:sharpness-zero`, for its explicit coordinate tuple.
Convergence of the product is part of the conclusion, not an input hypothesis.
Reserved proof name: `Paper.prop_sharpness_zero`. -/
def SharpnessZeroTarget (n : ℕ) : Prop :=
  1 ≤ n →
    (∀ z : ℂ, Multipliable (fun j : ℕ => 1 + Complex.exp (-((j + 1 : ℕ) : ℂ)) * z)) ∧
    ∃ f : Curve n, f.coord = zeroSharpCoordinates n ∧
      f.Transcendental ∧ f.linearlyNonDegenerate ∧ order f = (0 : EReal) ∧
      Tendsto (fun r => ramification f r / characteristic f r) atTop (𝓝 1)

end ModifiedCartan
