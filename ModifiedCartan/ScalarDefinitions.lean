import Mathlib.Analysis.Meromorphic.RCLike
import ModifiedCartan.OrdinaryGrowthOrders
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

open scoped Topology
open Filter Set Asymptotics Function MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

/-- Scalar rationality means equality as meromorphic germs to an actual
quotient of polynomials. LaTeX context of `thm:A`. -/
def ScalarIsRational (f : ℂ → ℂ) : Prop :=
  ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
    f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => P.eval z / Q.eval z)

def ScalarTranscendental (f : ℂ → ℂ) : Prop := ¬ ScalarIsRational f

noncomputable abbrev scalarCharacteristic (f : ℂ → ℂ) := ValueDistribution.characteristic f ⊤

/-- The intrinsic scalar critical divisor: at a pole of multiplicity k,
the derivative has order -k-1, so this divisor has multiplicity k-1.
Its nonnegativity and its Wronskian identification are proved separately. -/
noncomputable def scalarCriticalDivisor (f : ℂ → ℂ) : locallyFinsupp ℂ ℤ :=
  divisor (deriv f) univ + 2 • (divisor f univ)⁻

/-- The classical integrated critical-point count N1, including ramified poles. -/
noncomputable def scalarRamification (f : ℂ → ℂ) : ℝ → ℝ :=
  (scalarCriticalDivisor f).logCounting

/-- Literal lower limiting proximity ratio from the introduction preceding `thm:A`.
The extended-real definition does not discard a divergent limit. -/
noncomputable def scalarDeficiency (f : ℂ → ℂ) (a : WithTop ℂ) : EReal :=
  liminf (fun r => ((ValueDistribution.proximity f a r / scalarCharacteristic f r : ℝ) : EReal)) atTop

/-- Exact target for LaTeX `thm:A`; this definition is not a proof certificate.
The sum is HasSum, so an unspecified or divergent infinite sum cannot satisfy it. -/
def ScalarTheoremATarget (f : ℂ → ℂ) : Prop :=
  Meromorphic f → ScalarTranscendental f →
  lowerGrowthOrder (scalarCharacteristic f) < ⊤ →
  scalarRamification f =o[atTop] scalarCharacteristic f →
  ∃ (ρ : ℝ) (m : ℕ) (ℓ : ℝ → ℝ) (p : WithTop ℂ → ℕ),
    2 ≤ m ∧ ρ = (m : ℝ) / 2 ∧
    upperGrowthOrder (scalarCharacteristic f) = (ρ : EReal) ∧
    lowerGrowthOrder (scalarCharacteristic f) = (ρ : EReal) ∧
    FewInflection.SlowlyVarying ℓ ∧
    Tendsto (fun r => scalarCharacteristic f r / (r ^ ρ * ℓ r)) atTop (𝓝 1) ∧
    (∀ a, scalarDeficiency f a = (((p a : ℝ) / ρ : ℝ) : EReal)) ∧
    HasSum (fun a => (p a : ℝ)) (2 * ρ)

theorem scalarIsRational_of_codiscrete_const {f : ℂ → ℂ} {a : ℂ}
    (hf : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun _ => a)) : ScalarIsRational f := by
  refine ⟨Polynomial.C a, 1, one_ne_zero, ?_⟩
  simpa only [Polynomial.eval_C, Polynomial.eval_one, div_one] using hf

theorem scalarTranscendental_finite_orders {f : ℂ → ℂ} (hf : Meromorphic f)
    (htrans : ScalarTranscendental f) : ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
  apply hf.exists_meromorphicOrderAt_ne_top_iff_forall.mp
  by_contra hn
  apply htrans
  apply scalarIsRational_of_codiscrete_const (a := 0)
  filter_upwards [hf.meromorphicOn.analyticAt_mem_codiscreteWithin] with z hz
  by_contra hne
  have ho : meromorphicOrderAt f z = 0 := by
    rw [hz.meromorphicOrderAt_eq, hz.analyticOrderAt_eq_zero.mpr hne]
    rfl
  apply hn
  exact ⟨z, by rw [ho]; exact WithTop.zero_ne_top⟩

end ModifiedCartan
#print axioms ModifiedCartan.scalarTranscendental_finite_orders

