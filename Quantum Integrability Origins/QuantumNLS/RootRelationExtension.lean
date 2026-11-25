import Mathlib
import QuantumNLS.RootCauchyHolo
import QuantumNLS.RootProductSymbolAnalytic
import QuantumNLS.FullMass

/-!
# R-C4F43CA8 part (a), stage 3a: the implicit relation on the whole upper half-plane

`fz L κ z (G_z u) = productSymbol L κ u z` (`FullMass.mass_characterization`) is known where `HighHalf L (κ‖u‖²) z`.
Both sides are real-analytic in `z` on the connected open set `{Im z > 0}`:
* `G_z u = cauchyTransform (Mmeas κ u) z` (`RootCauchyHolo.analyticOnNhd_cauchyTransform`);
* `z ↦ fz L κ z (G_z u)` is real-analytic (composition with entire functions);
* `z ↦ productSymbol L κ u z` is real-analytic (`RootProductSymbolAnalytic`).
They agree on a nonempty open subset (large `Im z`), so the identity theorem gives agreement on all of `{Im z > 0}`.

Proved (standard axioms only):
* `fz_analyticOnNhd`, `fz_eq_productSymbol_upper`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex
open QuantumNLS.RootMeasureComplex QuantumNLS.RootCauchyHolo QuantumNLS.RootProductSymbolAnalytic

namespace QuantumNLS.RootRelationExtension

variable (L : ℝ) [Fact (0 < L)]

theorem analyticAt_comp_entire {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℝ f z₀) : AnalyticAt ℝ (fun z => φ (f z)) z₀ :=
  ((hφ.analyticAt (f z₀)).restrictScalars).comp hf

/-- `z ↦ fz L κ z (G_z u)` is real-analytic on the upper half-plane. -/
theorem fz_analyticOnNhd (κ : ℝ) (u : PhysicalTensor.L2T L) :
    AnalyticOnNhd ℝ
      (fun z : ℂ => fz L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)) upperHalf := by
  intro z₀ hz₀
  have hG : AnalyticAt ℝ (fun z => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) z₀ :=
    analyticOnNhd_cauchyTransform (FullMass.Mmeas κ u) z₀ hz₀
  have hA1 := analyticAt_comp_entire (φ := fun w : ℂ => Complex.exp (Complex.I * κ * w)) (by fun_prop) hG
  have hA3 := analyticAt_comp_entire (φ := fun w : ℂ => Complex.exp (-(Complex.I * κ * w))) (by fun_prop) hG
  have hA2 : AnalyticAt ℝ (fun z : ℂ => Complex.exp (Complex.I * z * (L : ℂ))) z₀ :=
    ((show Differentiable ℂ (fun z : ℂ => Complex.exp (Complex.I * z * (L : ℂ))) by fun_prop).analyticAt z₀).restrictScalars
  exact hA1.add (hA2.mul hA3)

/-- **The implicit relation on the whole upper half-plane.** For `u ≠ 0` and `Im z > 0`:
`fz L κ z (G_z u) = productSymbol L κ u z`. -/
theorem fz_eq_productSymbol_upper (κ : ℝ) (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (hu : u ≠ 0) (z : ℂ)
    (hz : 0 < z.im) :
    fz L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) =
      QuantumNLS.NormalizedTransfer.productSymbol L κ u z := by
  have hL : 0 < L := Fact.out
  have hlog : 0 ≤ Real.log 16 / L := div_nonneg (Real.log_nonneg (by norm_num)) hL.le
  have hk : 0 ≤ 4 * κ * ‖u‖ ^ 2 := by positivity
  set T : ℝ := 4 * κ * ‖u‖ ^ 2 + Real.log 16 / L + 1 with hT
  have hT0 : 0 < T := by rw [hT]; linarith
  set z₀ : ℂ := ⟨0, T⟩ with hz₀def
  have hz₀im : z₀.im = T := rfl
  have hz₀U : z₀ ∈ upperHalf := by
    show 0 < z₀.im
    rw [hz₀im]
    exact hT0
  have hS : IsOpen {w : ℂ | T - 1 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hz₀S : z₀ ∈ {w : ℂ | T - 1 < w.im} := by
    show T - 1 < z₀.im
    rw [hz₀im]
    linarith
  have hfg : (fun w : ℂ => fz L κ w (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) w)) =ᶠ[𝓝 z₀]
      (fun w : ℂ => QuantumNLS.NormalizedTransfer.productSymbol L κ u w) := by
    have hev : ∀ᶠ w in 𝓝 z₀, T - 1 < w.im := IsOpen.mem_nhds hS hz₀S
    refine hev.mono fun w hw => ?_
    have hw' : T - 1 < w.im := hw
    have h4 : 4 * (κ * ‖u‖ ^ 2) ≤ w.im := by
      have : 4 * κ * ‖u‖ ^ 2 ≤ T - 1 := by rw [hT]; linarith
      nlinarith
    have hlogw : Real.log 16 ≤ L * w.im := by
      have h1 : Real.log 16 / L ≤ T - 1 := by rw [hT]; linarith
      have h2 : Real.log 16 / L < w.im := lt_of_le_of_lt h1 hw'
      rw [div_lt_iff₀ hL] at h2
      linarith
    have hHigh : HighHalf L (κ * ‖u‖ ^ 2) w := by
      unfold HighHalf
      exact ⟨h4, hlogw⟩
    obtain ⟨-, h2, -⟩ := FullMass.mass_characterization hκ hu hHigh
    exact h2
  have hF := fz_analyticOnNhd L κ u
  have hP : AnalyticOnNhd ℝ (fun w : ℂ => QuantumNLS.NormalizedTransfer.productSymbol L κ u w) upperHalf :=
    fun w _ => analyticAt_productSymbol_z L κ hκ.le u w
  have hconn : IsPreconnected upperHalf := (convex_halfSpace_im_gt 0).isPreconnected
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hP hconn hz₀U hfg hz
  exact heq

end QuantumNLS.RootRelationExtension

#print axioms QuantumNLS.RootRelationExtension.fz_eq_productSymbol_upper
