import QuantumNLS.RootGFullDomain
import QuantumNLS.RootGReduced
import QuantumNLS.RootGBracket
import QuantumNLS.RootSymbolBrackets

/-!
# R-C4F43CA8 boundary bracket: the reduced zero brackets on the CLOSED branch domain

RootGReduced.reduced_bracket_zero is stated on the open domain (`4κ < Im z`, `log 16 < L Im z`). The source domain is
closed: `4κ ≤ Im z` and `log 16 ≤ L·Im z`. Terra r160 HOLD asked for the assembly on the closed domain.

The strict proof used `gFDeriv_exists` only for the derivative of `G_z`. Here it is replaced by
`RootGFullDomain.G_hasFDerivAt_full`, which holds on the closed domain. The symbol derivative comes from
`productSymbol_contDiffOn` at radius `3/2` (requires only `κ (3/2)² < Im z`, true when `4κ ≤ Im z`). The symbol zero
brackets (`RootSymbolBrackets.bracket_A`, `bracket_B`) need only `κ < Im z`. The scalar, chain and swap rules and the
reduced-bracket equivalence (`pbR_eq_reducedR`, `pbC_eq_reducedC`) are unchanged.

Proved here (standard axioms only):
* `symbol_hasFDerivAt`: the symbol is Fréchet differentiable at a unit vector on the closed domain;
* `G_pbC_zero_closed`: `pbC G_z G_w = 0` and `pbC G_z (conj G_w) = 0` at unit `u₀` on the closed domain;
* `reduced_bracket_zero_closed`: the two complex and four real reduced zero brackets on the closed domain.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric

namespace QuantumNLS.RootGBoundaryBracket

open QuantumNLS.SymplecticBracket QuantumNLS.RootGBracket QuantumNLS.RootGNeighbourhood
  QuantumNLS.RootGLocal QuantumNLS.RootGFullDomain QuantumNLS.RootGReduced QuantumNLS.PhysicalTensor
  QuantumNLS.RootSymbolFrechet QuantumNLS.RootSymbolBrackets QuantumNLS.NormalizedTransfer

theorem symbol_hasFDerivAt (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ ≤ z.im)
    (u0 : L2T L) (hu0 : ‖u0‖ = 1) :
    HasFDerivAt (fun v : L2T L => productSymbol L κ v z)
      (fderiv ℝ (fun v : L2T L => productSymbol L κ v z) u0) u0 := by
  have hκz : κ < z.im := by linarith
  have hRz : κ * (3 / 2) ^ 2 < z.im := by nlinarith
  have hsC := productSymbol_contDiffOn L κ hκ.le z hκz (3 / 2) (by norm_num) hRz
  have hmem : u0 ∈ ball (0 : L2T L) (3 / 2) := by
    rw [mem_ball_zero_iff, hu0]
    norm_num
  exact ((hsC.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hmem)).hasFDerivAt

theorem G_pbC_zero_closed (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z w : ℂ)
    (hz4 : 4 * κ ≤ z.im) (hzL : Real.log 16 ≤ L * z.im)
    (hw4 : 4 * κ ≤ w.im) (hwL : Real.log 16 ≤ L * w.im) (u0 : L2T L) (hu0 : ‖u0‖ = 1) :
    pbC (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
        (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) w) u0 = 0 ∧
    pbC (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
        (fun u : L2T L => conj (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) w)) u0 = 0 := by
  have hu0p : 0 < ‖u0‖ := by rw [hu0]; norm_num
  have hu0r : ‖u0‖ ^ 2 < 4 / 3 := by rw [hu0]; norm_num
  obtain ⟨hzne, hGz⟩ := G_hasFDerivAt_full L κ hκ z hz4 hzL u0 hu0p hu0r
  obtain ⟨hwne, hGw⟩ := G_hasFDerivAt_full L κ hκ w hw4 hwL u0 hu0p hu0r
  have hκz : κ < z.im := by linarith
  have hκw : κ < w.im := by linarith
  have hsz := symbol_hasFDerivAt L κ hκ z hz4 u0 hu0
  have hsw := symbol_hasFDerivAt L κ hκ w hw4 u0 hu0
  constructor
  · rw [pbC_of_hasFDerivAt _ _ _ _ u0 hGz hsz _ (diff_re_im hGw).1 (diff_re_im hGw).2]
    rw [pbC_second _ _ _ _ _ u0 hGw hsw (diff_re_im hsz).1 (diff_re_im hsz).2]
    rw [bracket_A L κ hκ z w hκz hκw u0 hu0]
    ring
  · have hcG : HasFDerivAt (fun v => conj (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w))
        (conj _ • Complex.conjCLE.toContinuousLinearMap.comp _) u0 :=
      (hasFDerivAt_conj hGw).congr_fderiv (conjCLM_smul _ _)
    have hcs := hasFDerivAt_conj hsw
    rw [pbC_of_hasFDerivAt _ _ _ _ u0 hGz hsz _ (diff_re_im hcG).1 (diff_re_im hcG).2]
    rw [pbC_second _ _ _ _ _ u0 hcG hcs (diff_re_im hsz).1 (diff_re_im hsz).2]
    rw [bracket_B L κ hκ z w hκz hκw u0 hu0]
    ring

/-- **Reduced zero brackets of `G_z`, `G_w` on the closed domain.** Two complex (with the conjugate) and four real
components, the same statements as `RootGReduced.reduced_bracket_zero`. -/
theorem reduced_bracket_zero_closed (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z w : ℂ)
    (hz4 : 4 * κ ≤ z.im) (hzL : Real.log 16 ≤ L * z.im)
    (hw4 : 4 * κ ≤ w.im) (hwL : Real.log 16 ≤ L * w.im) (u0 : L2T L) (hu0 : ‖u0‖ = 1) :
    reducedC L (fun v => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z)
        (fun v => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w) u0 = 0 ∧
    reducedC L (fun v => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z)
        (fun v => conj (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w)) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).re) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).im) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).re) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).im) u0 = 0 := by
  obtain ⟨h1, h2⟩ := G_pbC_zero_closed L κ hκ z w hz4 hzL hw4 hwL u0 hu0
  have hu0p : 0 < ‖u0‖ := by rw [hu0]; norm_num
  have hu0r : ‖u0‖ ^ 2 < 4 / 3 := by rw [hu0]; norm_num
  obtain ⟨hzne, hGz⟩ := G_hasFDerivAt_full L κ hκ z hz4 hzL u0 hu0p hu0r
  have hd := diff_re_im hGz
  have hph := G_phaseInv L κ hκ z
  -- real components from the complex zero brackets (as in RootGBracket.G_pbR_zero)
  have hA := Complex.ext_iff.mp h1
  have hB := Complex.ext_iff.mp h2
  simp only [pbC, Complex.zero_re, Complex.zero_im, Complex.conj_re, Complex.conj_im,
    pbR_neg_right] at hA hB
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  have r1 : pbR (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re)
      (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).re) u0 = 0 := by linarith
  have r2 : pbR (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im)
      (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).im) u0 = 0 := by linarith
  have r3 : pbR (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im)
      (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).re) u0 = 0 := by linarith
  have r4 : pbR (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re)
      (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).im) u0 = 0 := by linarith
  have hre := hd.1
  have him := hd.2
  refine ⟨(pbC_eq_reducedC L hre him hph).symm.trans h1, (pbC_eq_reducedC L hre him hph).symm.trans h2,
    (pbR_eq_reducedR L hre (phaseInv_re hph)).symm.trans r1,
    (pbR_eq_reducedR L him (phaseInv_im hph)).symm.trans r2,
    (pbR_eq_reducedR L him (phaseInv_im hph)).symm.trans r3,
    (pbR_eq_reducedR L hre (phaseInv_re hph)).symm.trans r4⟩

end QuantumNLS.RootGBoundaryBracket

#print axioms QuantumNLS.RootGBoundaryBracket.reduced_bracket_zero_closed
