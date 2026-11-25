import Mathlib
import QuantumNLS.RootTraceSymbolFinal
import QuantumNLS.DEF014DiscriminantAnalytic
import QuantumNLS.NormalizedTransfer

/-!
# R-C4F43CA8 part (a), stage 2: real-analyticity of `z ↦ productSymbol L κ u z` on all of ℂ

From `RootTraceSymbolFinal.traceSymbol_all`: `exp(−(i z L/2)) · productSymbol = L2SpatialTransfer.discriminant`, hence
`productSymbol L κ u z = exp(i z L/2) · discriminant κ u z` for every `z ∈ ℂ`. The discriminant is jointly real-analytic in
`(u, z)` by `DEF014DiscriminantAnalytic.analyticAt_discriminant_joint` (read-only import, its standard axioms).
Therefore `z ↦ productSymbol L κ u z` is real-analytic at every `z₀ ∈ ℂ` (`analyticAt_productSymbol_z`).

Proved (standard axioms only):
* `productSymbol_eq_exp_mul_discriminant`;
* `analyticAt_productSymbol_z`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex

namespace QuantumNLS.RootProductSymbolAnalytic

variable (L : ℝ) [Fact (0 < L)]

theorem productSymbol_eq_exp_mul_discriminant (κ : ℝ) (hκ : 0 ≤ κ) (u : PhysicalTensor.L2T L) (z : ℂ) :
    QuantumNLS.NormalizedTransfer.productSymbol L κ u z =
      Complex.exp (Complex.I * z * (L : ℂ) / 2) * QuantumNLS.L2SpatialTransfer.discriminant κ u z := by
  have h := QuantumNLS.RootTraceSymbolFinal.traceSymbol_all (L := L) hκ u z
  rw [← h, ← mul_assoc, ← Complex.exp_add]
  have e : Complex.I * z * (L : ℂ) / 2 + -(Complex.I * z * (L : ℂ) / 2) = 0 := by ring
  rw [e, Complex.exp_zero, one_mul]

theorem analyticAt_productSymbol_z (κ : ℝ) (hκ : 0 ≤ κ) (u : PhysicalTensor.L2T L) (z₀ : ℂ) :
    AnalyticAt ℝ (fun z : ℂ => QuantumNLS.NormalizedTransfer.productSymbol L κ u z) z₀ := by
  have hD : AnalyticAt ℝ (fun z : ℂ => QuantumNLS.L2SpatialTransfer.discriminant κ u z) z₀ :=
    (QuantumNLS.DEF014DiscriminantAnalytic.analyticAt_discriminant_joint (L := L) κ (u, z₀)).comp
      (f := fun z : ℂ => (u, z)) (analyticAt_const.prod analyticAt_id)
  have hd : Differentiable ℂ (fun z : ℂ => Complex.exp (Complex.I * z * (L : ℂ) / 2)) := by
    fun_prop
  have hE : AnalyticAt ℝ (fun z : ℂ => Complex.exp (Complex.I * z * (L : ℂ) / 2)) z₀ :=
    (hd.analyticAt z₀).restrictScalars
  have e : (fun z : ℂ => QuantumNLS.NormalizedTransfer.productSymbol L κ u z) =
      fun z : ℂ => Complex.exp (Complex.I * z * (L : ℂ) / 2) * QuantumNLS.L2SpatialTransfer.discriminant κ u z :=
    funext fun z => productSymbol_eq_exp_mul_discriminant L κ hκ u z
  rw [e]
  exact hE.mul hD

end QuantumNLS.RootProductSymbolAnalytic

#print axioms QuantumNLS.RootProductSymbolAnalytic.analyticAt_productSymbol_z
#print axioms QuantumNLS.RootProductSymbolAnalytic.productSymbol_eq_exp_mul_discriminant
