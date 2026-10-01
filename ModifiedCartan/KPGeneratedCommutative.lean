import ModifiedCartan.KPBetaCommutation
import ModifiedCartan.KPTranslation

open scoped Classical MonoidAlgebra IsMulCommutative

namespace ModifiedCartan
noncomputable section

theorem kpGeneratedAlgebra_isMulCommutative {N : ℕ} (z : Fin N → ℂ) :
    IsMulCommutative (kpGeneratedAlgebra z) := by
  apply Algebra.isMulCommutative_adjoin ℂ
  rintro x ⟨μ, rfl⟩ y ⟨ν, rfl⟩
  exact (kpBeta_commute z μ ν 0 0).eq

theorem kpGeneratedAlgebra_elements_commute {N : ℕ} (z : Fin N → ℂ)
    (x y : kpGeneratedAlgebra z) : x * y = y * x := by
  letI := kpGeneratedAlgebra_isMulCommutative z
  exact mul_comm x y

end
end ModifiedCartan


