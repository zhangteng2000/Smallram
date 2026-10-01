import ModifiedCartan.Indices
import ModifiedCartan.SmallOrderClassification
import ModifiedCartan.RegularVariation
import FewInflection.PolynomialSpaces

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The common value in LaTeX `eq:indices-collapse` is admissible for a
transcendental curve: the zero case would give a rational normal form. -/
theorem exists_common_admissible_order {n : ℕ} (f : Curve n) (hn : 1 ≤ n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hfinite : FiniteLowerOrder f) (hsmall : SmallRamification f) :
    ∃ ρ : ℝ, strongLowerIndex (characteristic f) = (ρ : EReal) ∧
      lowerOrder f = (ρ : EReal) ∧ order f = (ρ : EReal) ∧
      strongUpperIndex (characteristic f) = (ρ : EReal) ∧
      FewInflection.AdmissibleOrder n ρ := by
  obtain ⟨ρ, hl, hlo, ho, hu, hz | hρ⟩ := Paper.prop_indices f htrans hlin hfinite hsmall
  · have horder : order f < (1 : EReal) := by rw [ho, hz]; norm_num
    obtain ⟨hform⟩ := Paper.prop_small_order f hn hlin hsmall horder
    exact False.elim (hform.not_transcendental htrans)
  · exact ⟨ρ, hl, hlo, ho, hu, hρ⟩

/-- LaTeX `reg`: the explicit slowly varying factor gives equality at
every positive radius, as well as the order and lower-order conclusions. -/
theorem Paper.thm_main_explicit_factor {n : ℕ} (f : Curve n) (hn : 1 ≤ n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hfinite : FiniteLowerOrder f) (hsmall : SmallRamification f) :
    ∃ ρ : ℝ, order f = (ρ : EReal) ∧ lowerOrder f = (ρ : EReal) ∧
      FewInflection.AdmissibleOrder n ρ ∧
      FewInflection.SlowlyVarying (fun r => characteristic f r / r ^ ρ) ∧
      ∀ r : ℝ, 0 < r → characteristic f r = r ^ ρ * (characteristic f r / r ^ ρ) := by
  obtain ⟨ρ, hl, hlo, ho, hu, hρ⟩ := exists_common_admissible_order f hn htrans hlin hfinite hsmall
  refine ⟨ρ, ho, hlo, hρ, ?_, ?_⟩
  · exact FewInflection.slowlyVarying_div_rpow_of_regularlyVarying
      (FewInflection.admissibleOrder_pos hρ).le
      (fun r hr => characteristic_pos_of_transcendental f htrans hr)
      (characteristic_continuous f).continuousOn
      (Paper.prop_regular_variation f htrans hlin hsmall hρ hl hu)
  · intro r hr
    field_simp [(Real.rpow_pos_of_pos hr ρ).ne']

/-- LaTeX `thm:main`, with the exact submitted hypotheses, Euclidean
characteristic, admissible order set and positive continuous slowly varying factor. -/
theorem Paper.thm_main {n : ℕ} (f : Curve n) : MainTheoremTarget f := by
  intro hn htrans hlin hfinite hsmall
  obtain ⟨ρ, ho, hlo, hρ, hslow, he⟩ :=
    Paper.thm_main_explicit_factor f hn htrans hlin hfinite hsmall
  refine ⟨ρ, ho, hlo, hρ, (fun r => characteristic f r / r ^ ρ), hslow, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact he r hr

end ModifiedCartan
#print axioms ModifiedCartan.exists_common_admissible_order
#print axioms ModifiedCartan.Paper.thm_main_explicit_factor
#print axioms ModifiedCartan.Paper.thm_main
