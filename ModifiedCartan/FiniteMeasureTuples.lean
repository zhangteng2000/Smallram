import ModifiedCartan.MeasureLimitTransfer

open scoped Topology ENNReal BigOperators
open Filter MeasureTheory Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Coordinatewise convergence in measure for a finite tuple. The proof
uses the union bound and does not impose additional measurability. -/
theorem tendstoInMeasure_finite_pi {A E ι : Type*} [MeasurableSpace A]
    [SeminormedAddCommGroup E] [Fintype ι] {μ : Measure A}
    {f : ℕ → A → ι → E} {g : A → ι → E}
    (h : ∀ i, TendstoInMeasure μ (fun ν x => f ν x i) atTop (fun x => g x i)) :
    TendstoInMeasure μ f atTop g := by
  classical
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have he : 0 < ε / 2 := by linarith
  have hlim := tendsto_finsetSum Finset.univ
    (fun i _ => (tendstoInMeasure_iff_norm.mp (h i)) (ε / 2) he)
  simp only [Finset.sum_const_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro ν
  apply (measure_mono (t := ⋃ i : ι, {x | ε / 2 ≤ ‖f ν x i - g x i‖}) ?_).trans
    (measure_iUnion_fintype_le μ _)
  intro x hx
  by_contra hn
  have hi (i : ι) : ‖f ν x i - g x i‖ < ε / 2 := by
    apply lt_of_not_ge
    intro hi
    exact hn (mem_iUnion.mpr ⟨i, hi⟩)
  have hnorm : ‖f ν x - g x‖ ≤ ε / 2 :=
    (pi_norm_le_iff_of_nonneg he.le).mpr (fun i => (hi i).le)
  change ε ≤ ‖f ν x - g x‖ at hx
  linarith

theorem LocalMeasureConvergence.finite_pi {E ι : Type*}
    [SeminormedAddCommGroup E] [Fintype ι] {U : Set ℂ}
    {f : ℕ → ℂ → ι → E} {g : ℂ → ι → E}
    (h : ∀ i, LocalMeasureConvergence U (fun ν z => f ν z i) (fun z => g z i)) :
    LocalMeasureConvergence U f g := by
  intro K hK hKU
  exact tendstoInMeasure_finite_pi (fun i => h i K hK hKU)

end ModifiedCartan
#print axioms ModifiedCartan.tendstoInMeasure_finite_pi
