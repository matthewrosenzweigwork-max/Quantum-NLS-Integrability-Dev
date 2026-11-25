import QuantumNLS.RootGLocal
import QuantumNLS.RootSymbolBrackets
import QuantumNLS.RootHolomorphicBracket

/-!
# R-C4F43CA8 part (3)(iii): zero brackets of the real and imaginary parts of `G_z`, and the identification with `gStar`

**Convention (integrator decision):** `G_z(u) := cauchyTransform (FullMass.Mmeas κ u) z`, full space (see `RootGLocal`).
The brackets are the SAME full-space `pbR`/`pbC` as in Part 2 (`SymplecticBracket`), evaluated at a unit `u₀`.
Terra checks the correspondence with the source's "reduced bracket" reading; if the phase-quotient form is preferred, Terra says so.

Proved here (standard axioms only):
* `pbC_swap`: `pbC F G u = − pbC G F u` (from `pbR_swap`).
* `pbC_of_hasFDerivAt`, `pbC_second`: the bracket depends on each argument only through its derivative at `u`
  (first and second slot), with a complex scalar factor (from `RootHolomorphicBracket`).
* `G_pbC_zero`: at a unit `u₀`, for `4κ < Im z`, `4κ < Im w`:
  `pbC (G_z) (G_w) u₀ = 0` and `pbC (G_z) (conj ∘ G_w) u₀ = 0`.
* `G_pbR_zero`: the four real brackets `{Re G_z, Re G_w}`, `{Im G_z, Im G_w}`, `{Im G_z, Re G_w}`, `{Re G_z, Im G_w}` vanish at `u₀`.
* `G_eq_gStar`: for a unit `u` and `HighHalf L κ z`, `cauchyTransform (Mmeas κ u) z = gStar L κ hκ u hu z`
  (uniqueness clause of `FullMass.mass_characterization` with `gStar_spec`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.RootGBracket

open QuantumNLS.SymplecticBracket QuantumNLS.RootBracketScalars QuantumNLS.RootHolomorphicBracket
  QuantumNLS.RootGLocal QuantumNLS.RootSymbolBrackets QuantumNLS.RootMeasureComplex QuantumNLS.PhysicalTensor
  QuantumNLS.RootMeasureConcentration QuantumNLS.NormalizedTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem diff_re_im {f : H → ℂ} {F' : H →L[ℝ] ℂ} {u : H} (h : HasFDerivAt f F' u) :
    DifferentiableAt ℝ (fun v => (f v).re) u ∧ DifferentiableAt ℝ (fun v => (f v).im) u :=
  ⟨(Complex.reCLM.hasFDerivAt.comp u h).differentiableAt,
    (Complex.imCLM.hasFDerivAt.comp u h).differentiableAt⟩

theorem pbC_swap (F G : H → ℂ) (u : H) : pbC F G u = -pbC G F u := by
  unfold pbC
  apply Complex.ext
  · dsimp only
    simp only [Complex.neg_re]
    rw [pbR_swap (fun v => (F v).re) (fun v => (G v).re) u,
      pbR_swap (fun v => (F v).im) (fun v => (G v).im) u]
    ring
  · dsimp only
    simp only [Complex.neg_im]
    rw [pbR_swap (fun v => (F v).im) (fun v => (G v).re) u,
      pbR_swap (fun v => (F v).re) (fun v => (G v).im) u]
    ring

/-- First-slot: the bracket depends on the first argument only through its derivative at `u`. -/
theorem pbC_of_hasFDerivAt (X s : H → ℂ) (c : ℂ) (S : H →L[ℝ] ℂ) (u : H)
    (hX : HasFDerivAt X (c • S) u) (hs : HasFDerivAt s S u) (K : H → ℂ)
    (hK1 : DifferentiableAt ℝ (fun v => (K v).re) u) (hK2 : DifferentiableAt ℝ (fun v => (K v).im) u) :
    pbC X K u = c * pbC s K u := by
  have hsc : HasFDerivAt (fun v => c * s v) (c • S) u := hs.const_mul c
  have hre : fderiv ℝ (fun v => (X v).re) u = fderiv ℝ (fun v => (c * s v).re) u := by
    have h1 : fderiv ℝ (fun v => (X v).re) u = Complex.reCLM.comp (c • S) :=
      (Complex.reCLM.hasFDerivAt.comp u hX).fderiv
    have h2 : fderiv ℝ (fun v => (c * s v).re) u = Complex.reCLM.comp (c • S) :=
      (Complex.reCLM.hasFDerivAt.comp u hsc).fderiv
    rw [h1, h2]
  have him : fderiv ℝ (fun v => (X v).im) u = fderiv ℝ (fun v => (c * s v).im) u := by
    have h1 : fderiv ℝ (fun v => (X v).im) u = Complex.imCLM.comp (c • S) :=
      (Complex.imCLM.hasFDerivAt.comp u hX).fderiv
    have h2 : fderiv ℝ (fun v => (c * s v).im) u = Complex.imCLM.comp (c • S) :=
      (Complex.imCLM.hasFDerivAt.comp u hsc).fderiv
    rw [h1, h2]
  have hkre : ∀ K' : H → ℂ, pbR (fun v => (X v).re) (fun v => (K' v).re) u =
      pbR (fun v => (c * s v).re) (fun v => (K' v).re) u :=
    fun K' => pbR_of_fderiv_eq _ _ _ u hre
  have hkim : ∀ K' : H → ℂ, pbR (fun v => (X v).im) (fun v => (K' v).im) u =
      pbR (fun v => (c * s v).im) (fun v => (K' v).im) u :=
    fun K' => pbR_of_fderiv_eq _ _ _ u him
  have hkmr : ∀ K' : H → ℂ, pbR (fun v => (X v).im) (fun v => (K' v).re) u =
      pbR (fun v => (c * s v).im) (fun v => (K' v).re) u :=
    fun K' => pbR_of_fderiv_eq _ _ _ u him
  have hkrm : ∀ K' : H → ℂ, pbR (fun v => (X v).re) (fun v => (K' v).im) u =
      pbR (fun v => (c * s v).re) (fun v => (K' v).im) u :=
    fun K' => pbR_of_fderiv_eq _ _ _ u hre
  have hC : pbC X K u = pbC (fun v => c * s v) K u := by
    unfold pbC
    simp only [hkre, hkim, hkmr, hkrm]
  rw [hC]
  obtain ⟨hs1, hs2⟩ := diff_re_im hs
  exact pbC_const_mul c s K u hs1 hs2

/-- Second-slot version of `pbC_of_hasFDerivAt`, via `pbC_swap`. -/
theorem pbC_second (K X s : H → ℂ) (c : ℂ) (S : H →L[ℝ] ℂ) (u : H)
    (hX : HasFDerivAt X (c • S) u) (hs : HasFDerivAt s S u)
    (hK1 : DifferentiableAt ℝ (fun v => (K v).re) u) (hK2 : DifferentiableAt ℝ (fun v => (K v).im) u) :
    pbC K X u = c * pbC K s u := by
  rw [pbC_swap K X u, pbC_of_hasFDerivAt X s c S u hX hs K hK1 hK2, pbC_swap s K u]
  ring

theorem hasFDerivAt_conj {f : H → ℂ} {F' : H →L[ℝ] ℂ} {u : H} (h : HasFDerivAt f F' u) :
    HasFDerivAt (fun v => conj (f v)) (Complex.conjCLE.toContinuousLinearMap.comp F') u :=
  Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp u h

theorem conjCLM_smul (c : ℂ) (S : H →L[ℝ] ℂ) :
    Complex.conjCLE.toContinuousLinearMap.comp (c • S) = conj c • Complex.conjCLE.toContinuousLinearMap.comp S := by
  ext x
  simp [map_mul]

/-- **Zero complex brackets of `G_z`, `G_w` at a unit `u₀`** (both with the full-space `pbC`). -/
theorem G_pbC_zero (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z w : ℂ)
    (hz4 : 4 * κ < z.im) (hzL : Real.log 16 < L * z.im)
    (hw4 : 4 * κ < w.im) (hwL : Real.log 16 < L * w.im) (u0 : L2T L) (hu0 : ‖u0‖ = 1) :
    pbC (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
        (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) w) u0 = 0 ∧
    pbC (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
        (fun u : L2T L => conj (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) w)) u0 = 0 := by
  obtain ⟨a, S, _ha, hGz, hsz⟩ := gFDeriv_exists L κ hκ z hz4 hzL u0 hu0
  obtain ⟨b, T, _hb, hGw, hsw⟩ := gFDeriv_exists L κ hκ w hw4 hwL u0 hu0
  have hκz : κ < z.im := by linarith
  have hκw : κ < w.im := by linarith
  have hdGw := diff_re_im hGw
  constructor
  · rw [pbC_of_hasFDerivAt _ _ a S u0 hGz hsz _ (diff_re_im hGw).1 (diff_re_im hGw).2]
    rw [pbC_second _ _ _ b T u0 hGw hsw (diff_re_im hsz).1 (diff_re_im hsz).2]
    rw [bracket_A L κ hκ z w hκz hκw u0 hu0]
    ring
  · have hcG : HasFDerivAt (fun v => conj (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w))
        (conj b • Complex.conjCLE.toContinuousLinearMap.comp T) u0 :=
      (hasFDerivAt_conj hGw).congr_fderiv (conjCLM_smul b T)
    have hcs := hasFDerivAt_conj hsw
    rw [pbC_of_hasFDerivAt _ _ a S u0 hGz hsz _ (diff_re_im hcG).1 (diff_re_im hcG).2]
    rw [pbC_second _ _ _ (conj b) _ u0 hcG hcs (diff_re_im hsz).1 (diff_re_im hsz).2]
    rw [bracket_B L κ hκ z w hκz hκw u0 hu0]
    ring

/-- **Real zero brackets of `G_z`, `G_w`** (the four combinations of real and imaginary parts, at a unit `u₀`). -/
theorem G_pbR_zero (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z w : ℂ)
    (hz4 : 4 * κ < z.im) (hzL : Real.log 16 < L * z.im)
    (hw4 : 4 * κ < w.im) (hwL : Real.log 16 < L * w.im) (u0 : L2T L) (hu0 : ‖u0‖ = 1) :
    pbR (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).re) u0 = 0 ∧
    pbR (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).im) u0 = 0 ∧
    pbR (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).re) u0 = 0 ∧
    pbR (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).im) u0 = 0 := by
  obtain ⟨h1, h2⟩ := G_pbC_zero L κ hκ z w hz4 hzL hw4 hwL u0 hu0
  have hA := Complex.ext_iff.mp h1
  have hB := Complex.ext_iff.mp h2
  simp only [pbC, Complex.zero_re, Complex.zero_im, Complex.conj_re, Complex.conj_im,
    pbR_neg_right] at hA hB
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Identification with `gStar`:** for a unit `u` and `HighHalf L κ z`, `G_z(u) = gStar z` (uniqueness clause of
`FullMass.mass_characterization`, with `gStar_spec`). -/
theorem G_eq_gStar (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ)
    (hz : HighHalf L κ z) :
    QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z = gStar L κ hκ u hu z := by
  have hn : ‖u‖ ^ 2 = 1 := by rw [hu]; norm_num
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    norm_num at hu
  have hzm : HighHalf L (κ * ‖u‖ ^ 2) z := by
    rw [hn, mul_one]
    exact hz
  obtain ⟨_, _, hG3⟩ := FullMass.mass_characterization hκ hu0 hzm
  obtain ⟨hs1, hs2⟩ := gStar_spec hκ u hu hz
  have key := hG3 (gStar L κ hκ u hu z) (by rw [hn, one_div]; exact hs1) hs2
  exact key.symm

end QuantumNLS.RootGBracket

#print axioms QuantumNLS.RootGBracket.pbC_swap
#print axioms QuantumNLS.RootGBracket.pbC_of_hasFDerivAt
#print axioms QuantumNLS.RootGBracket.pbC_second
#print axioms QuantumNLS.RootGBracket.G_pbC_zero
#print axioms QuantumNLS.RootGBracket.G_pbR_zero
#print axioms QuantumNLS.RootGBracket.G_eq_gStar
