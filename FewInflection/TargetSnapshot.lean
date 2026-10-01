import FewInflection.Results

/-!
The exact five target propositions are kept in the library so that the
completion gate can import them with the ordinary project module path.  The
file under `verification/` re-exports this snapshot and checks identity with
the current result declarations.
-/

open scoped BigOperators Topology
open Filter Asymptotics

namespace FewInflection

noncomputable section

def FrozenMainTheoremStatement
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

def FrozenSharpnessStatement (n : ℕ) : Prop :=
  1 ≤ n →
  ∀ ρ : ℝ, AdmissibleOrder n ρ →
    ∃ w : RealizationWitness n ρ,
      w.curve.Transcendental ∧
      w.curve.linearlyNonDegenerate ∧
      (∀ z, wronskian n w.curve.coord z = 1)

def FrozenSmallOrderStatement
    {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n →
  f.linearlyNonDegenerate →
  SmallRamification f →
  order f < (1 : EReal) →
  ∃ _h : RationalNormalForm n f, order f = (0 : EReal)

def FrozenZeroOrderStatement
    {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n →
  f.Transcendental →
  f.linearlyNonDegenerate →
  order f = (0 : EReal) →
  limsup (fun r => ramification f r / characteristic f r) atTop ≥ 1

def FrozenRadialAreaStatement
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

theorem frozen_main_target_matches :
    @FrozenMainTheoremStatement = @MainTheoremStatement := rfl

theorem frozen_sharpness_target_matches :
    FrozenSharpnessStatement = SharpnessStatement := rfl

theorem frozen_small_order_target_matches :
    @FrozenSmallOrderStatement = @SmallOrderStatement := rfl

theorem frozen_zero_order_target_matches :
    @FrozenZeroOrderStatement = @ZeroOrderStatement := rfl

theorem frozen_radial_area_target_matches :
    @FrozenRadialAreaStatement = @RadialAreaStatement := rfl

end

end FewInflection
