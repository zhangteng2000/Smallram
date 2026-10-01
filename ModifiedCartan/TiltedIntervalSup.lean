import ModifiedCartan.NeighborGrowth

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Supremum of a logarithmic growth profile after subtracting its target slope.
No continuity or attainment of the supremum is required. -/
def tiltedIntervalSup (u : ℝ → ℝ) (μ a b : ℝ) : ℝ :=
  sSup ((fun x => u x - μ * x) '' Icc a b)

theorem tiltedInterval_bddAbove {u : ℝ → ℝ} (hu : Monotone u)
    {μ a b : ℝ} (hμ : 0 ≤ μ) :
    BddAbove ((fun x => u x - μ * x) '' Icc a b) := by
  refine ⟨u b - μ * a, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  have hu' := hu hx.2
  have hm := mul_le_mul_of_nonneg_left hx.1 hμ
  linarith

theorem le_tiltedIntervalSup {u : ℝ → ℝ} (hu : Monotone u)
    {μ a b x : ℝ} (hμ : 0 ≤ μ) (hx : x ∈ Icc a b) :
    u x - μ * x ≤ tiltedIntervalSup u μ a b := by
  exact le_csSup (tiltedInterval_bddAbove hu hμ) ⟨x, hx, rfl⟩

theorem tiltedIntervalSup_le {u : ℝ → ℝ} (hu : Monotone u)
    {μ a b : ℝ} (hμ : 0 ≤ μ) (hab : a ≤ b) :
    tiltedIntervalSup u μ a b ≤ u b - μ * a := by
  apply csSup_le (s := (fun x => u x - μ * x) '' Icc a b)
    ⟨u a - μ * a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩⟩
  rintro z ⟨x, hx, rfl⟩
  have hu' := hu hx.2
  have hm := mul_le_mul_of_nonneg_left hx.1 hμ
  linarith

/-- Absence of approximate peaks forces a gap between neighboring interval
suprema, even when the monotone function has jumps. -/
theorem tiltedIntervalSup_neighbor_gap {u : ℝ → ℝ} (hu : Monotone u)
    {μ a H d : ℝ} (hμ : 0 ≤ μ) (hH : 0 < H) (hd : 0 < d)
    (hgain : ∀ x ∈ Icc (a + H) (a + 2 * H),
      ∃ y, x - H ≤ y ∧ y ≤ x + H ∧
        (u x - μ * x) + d ≤ u y - μ * y) :
    tiltedIntervalSup u μ (a + H) (a + 2 * H) + d ≤
      max (tiltedIntervalSup u μ a (a + H))
        (tiltedIntervalSup u μ (a + 2 * H) (a + 3 * H)) := by
  let L := tiltedIntervalSup u μ a (a + H)
  let M := tiltedIntervalSup u μ (a + H) (a + 2 * H)
  let R := tiltedIntervalSup u μ (a + 2 * H) (a + 3 * H)
  have hb : M ≤ max L (max M R) - d := by
    apply csSup_le (s := (fun x => u x - μ * x) '' Icc (a + H) (a + 2 * H))
      ⟨u (a + H) - μ * (a + H),
      ⟨a + H, ⟨le_rfl, by linarith⟩, rfl⟩⟩
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨y, hy0, hy1, hxy⟩ := hgain x hx
    have hy : u y - μ * y ≤ max L (max M R) := by
      by_cases hyl : y ≤ a + H
      · exact (le_tiltedIntervalSup hu hμ ⟨by linarith [hx.1], hyl⟩).trans
          (le_max_left _ _)
      · by_cases hym : y ≤ a + 2 * H
        · exact (le_tiltedIntervalSup hu hμ ⟨by linarith, hym⟩).trans
            ((le_max_left M R).trans (le_max_right L (max M R)))
        · exact (le_tiltedIntervalSup hu hμ ⟨by linarith, by linarith [hx.2]⟩).trans
            ((le_max_right M R).trans (le_max_right L (max M R)))
    linarith
  have hgap : M + d ≤ max L (max M R) := by linarith
  change M + d ≤ max L R
  rcases le_max_iff.mp hgap with hl | hmr
  · exact hl.trans (le_max_left _ _)
  · rcases le_max_iff.mp hmr with hm | hr
    · linarith
    · exact hr.trans (le_max_right _ _)

end
end ModifiedCartan
#print axioms ModifiedCartan.tiltedIntervalSup_neighbor_gap
