import FewInflection.TargetSnapshot

/-! Public verification entry point for the frozen target propositions. -/

namespace FewInflection

open scoped BigOperators Topology
open Filter Asymptotics

/- These five bodies are copied in the verification entry point as well as in
the importable library snapshot.  The duplicated names make this file
self-contained for human inspection of the frozen mathematical types. -/

def SnapshotMainTheoremStatement
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

def SnapshotSharpnessStatement (n : ℕ) : Prop :=
  1 ≤ n →
  ∀ ρ : ℝ, AdmissibleOrder n ρ →
    ∃ w : RealizationWitness n ρ,
      w.curve.Transcendental ∧
      w.curve.linearlyNonDegenerate ∧
      (∀ z, wronskian n w.curve.coord z = 1)

def SnapshotSmallOrderStatement
    {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n →
  f.linearlyNonDegenerate →
  SmallRamification f →
  order f < (1 : EReal) →
  ∃ _h : RationalNormalForm n f, order f = (0 : EReal)

def SnapshotZeroOrderStatement
    {n : ℕ} (f : Curve n) : Prop :=
  1 ≤ n →
  f.Transcendental →
  f.linearlyNonDegenerate →
  order f = (0 : EReal) →
  limsup (fun r => ramification f r / characteristic f r) atTop ≥ 1

def SnapshotRadialAreaStatement
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

theorem snapshot_main_matches_library :
    @SnapshotMainTheoremStatement = @FrozenMainTheoremStatement := rfl

theorem snapshot_sharpness_matches_library :
    SnapshotSharpnessStatement = FrozenSharpnessStatement := rfl

theorem snapshot_small_order_matches_library :
    @SnapshotSmallOrderStatement = @FrozenSmallOrderStatement := rfl

theorem snapshot_zero_order_matches_library :
    @SnapshotZeroOrderStatement = @FrozenZeroOrderStatement := rfl

theorem snapshot_radial_area_matches_library :
    @SnapshotRadialAreaStatement = @FrozenRadialAreaStatement := rfl

example : @FrozenMainTheoremStatement = @MainTheoremStatement :=
  frozen_main_target_matches

example : FrozenSharpnessStatement = SharpnessStatement :=
  frozen_sharpness_target_matches

example : @FrozenSmallOrderStatement = @SmallOrderStatement :=
  frozen_small_order_target_matches

example : @FrozenZeroOrderStatement = @ZeroOrderStatement :=
  frozen_zero_order_target_matches

example : @FrozenRadialAreaStatement = @RadialAreaStatement :=
  frozen_radial_area_target_matches

end FewInflection
