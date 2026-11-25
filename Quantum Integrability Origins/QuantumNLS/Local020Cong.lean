import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Scale

/-! LOCAL-020: the reduction objects depend on the potential only through its a.e. class on the interval. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory QuantumNLS.LocalSpectral

namespace QuantumNLS.Local020Cong

variable {L κ : ℝ} {u u' : ℝ → ℂ}

theorem resolvent_congr (h : u =ᵐ[μI L] u') (σ : ℤˣ) (z : ℂ) :
    resolvent L κ u σ z = resolvent L κ u' σ z := by
  unfold QuantumNLS.LocalSpectral.resolvent IsResolvent
  rw [Local020Scale.LuGraph_congr_ae h]

theorem rieszProj_congr (h : u =ᵐ[μI L] u') (σ : ℤˣ) (n : ℤ) (r : ℝ) :
    rieszProj L κ u σ n r = rieszProj L κ u' σ n r := by
  unfold rieszProj
  simp only [resolvent_congr h]

theorem dressedIntegral_congr (h : u =ᵐ[μI L] u') (n : ℤ) (r : ℝ) :
    dressedIntegral L κ u n r = dressedIntegral L κ u' n r := by
  unfold dressedIntegral
  simp only [resolvent_congr h]

theorem compressionMatrix_congr (h : u =ᵐ[μI L] u') (n : ℤ) (r : ℝ) :
    compressionMatrix L κ u n r = compressionMatrix L κ u' n r := by
  unfold compressionMatrix perturbedProj
  rw [rieszProj_congr h]

theorem smallCompression_congr (h : u =ᵐ[μI L] u') (n : ℤ) (r : ℝ) :
    SmallCompression L κ u n r ↔ SmallCompression L κ u' n r := by
  unfold SmallCompression
  rw [compressionMatrix_congr h]

theorem reducedMatrix2_congr (h : u =ᵐ[μI L] u') (n : ℤ) (r : ℝ) (h1 : SmallCompression L κ u n r)
    (h2 : SmallCompression L κ u' n r) :
    reducedMatrix2 L κ u n r h1 = reducedMatrix2 L κ u' n r h2 := by
  unfold reducedMatrix2 normalizedIsometry2 invSqrtCompression perturbedProj
  rw [rieszProj_congr h, compressionMatrix_congr h, dressedIntegral_congr h]

end QuantumNLS.Local020Cong
