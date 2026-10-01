import ModifiedCartan.KPTranslation

namespace ModifiedCartan
noncomputable section

theorem kpGeneratedAlgebra_shift {A : Type*} [Fintype A] [DecidableEq A]
    (z : A → ℂ) (t : ℂ) :
    kpGeneratedAlgebra (fun l => z l + t) = kpGeneratedAlgebra z := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x ⟨μ, rfl⟩
    change kpBeta μ (fun l => z l + t) 0 ∈ kpGeneratedAlgebra z
    rw [← kpBeta_parameter_shift μ z 0 t]
    exact kpBeta_mem_generated μ z (0 + t)
  · apply Algebra.adjoin_le
    rintro x ⟨μ, rfl⟩
    change kpBeta μ z 0 ∈ kpGeneratedAlgebra (fun l => z l + t)
    have hm := kpBeta_mem_generated μ (fun l => z l + t) (-t)
    rw [← kpBeta_parameter_shift μ z (-t) t, neg_add_cancel] at hm
    exact hm

end
end ModifiedCartan


