import QuantumNLS.TerraMultiRound27SwapNormalized

/-! Antiunitary covariance of the actual reduced map. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.LocalSpectral.Round27
open QuantumNLS.Local002 Round23 Round24 Round25 Round26

variable {L κ r : ℝ} (hyp : FreeResolventHyp L κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : qpar κ L r u < 1) (hu : SmallCompression L κ (u : ℝ → ℂ) n r)
include hyp hr hr2 hq

theorem adjoint_normalized_swap (x : H2 L) :
    (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu)) (swapOp L x) =
      swapConj ((ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu)) x) := by
  apply ext_inner_left ℂ
  intro v
  have hs := swapOp_inner L (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu (swapConj v)) x
  rw [← normalized_swap hyp hr hr2 n u hq hu, swapConj_involutive] at hs
  have hf := swapFiber_inner (swapConj v)
    ((ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu)) x)
  rw [swapConj_involutive] at hf
  calc
    ⟪v, (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu)) (swapOp L x)⟫_ℂ =
        ⟪normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu v, swapOp L x⟫_ℂ :=
          ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = conj ⟪normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu (swapConj v), x⟫_ℂ := hs
    _ = conj ⟪swapConj v, (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu)) x⟫_ℂ :=
      congrArg (starRingEnd ℂ) (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = ⟪v, swapConj ((ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu)) x)⟫_ℂ := hf.symm

theorem reducedMatrix_swap (v : E2) :
    reducedMatrix2 L κ (u : ℝ → ℂ) n r hu (swapConj v) =
      swapConj (reducedMatrix2 L κ (u : ℝ → ℂ) n r hu v) := by
  have hf : swapConj ((pm L n : ℂ) • v) = (pm L n : ℂ) • swapConj v := by
    ext i
    fin_cases i <;> simp [swapConj, vec2, map_mul]
  change (pm L n : ℂ) • swapConj v +
      (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu))
        (dressedIntegral L κ (u : ℝ → ℂ) n r (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu (swapConj v))) =
    swapFiberReal ((pm L n : ℂ) • v +
      (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu))
        (dressedIntegral L κ (u : ℝ → ℂ) n r (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu v)))
  rw [map_add]
  change (pm L n : ℂ) • swapConj v +
      (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu))
        (dressedIntegral L κ (u : ℝ → ℂ) n r (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu (swapConj v))) =
    swapConj ((pm L n : ℂ) • v) + swapConj
      ((ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu))
        (dressedIntegral L κ (u : ℝ → ℂ) n r (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu v)))
  rw [hf, normalized_swap hyp hr hr2 n u hq hu,
    (contour_swap hyp hr hr2 n u hq _).2,
    adjoint_normalized_swap hyp hr hr2 n u hq hu]

end QuantumNLS.LocalSpectral.Round27
#print axioms QuantumNLS.LocalSpectral.Round27.adjoint_normalized_swap
#print axioms QuantumNLS.LocalSpectral.Round27.reducedMatrix_swap
