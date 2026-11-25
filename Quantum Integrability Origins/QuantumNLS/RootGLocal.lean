import QuantumNLS.FullMass
import QuantumNLS.RootFzRadius
import QuantumNLS.RootSymbolFrechet
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# R-C4F43CA8 part (3)(ii)-b: local differentiability of `u ↦ G_z(u)` near the unit sphere

**Convention (integrator decision, recorded for Terra):** `G_z(u) := cauchyTransform (FullMass.Mmeas κ u) z`, the Cauchy
transform of the full-space mass measure `M_{κ,u}` of `FullMass`, for every `u ∈ L²`. It satisfies the implicit relation
`fz L κ z (G_z u) = productSymbol L κ u z` (`FullMass.mass_characterization`, for `u ≠ 0` with
`HighHalf L (κ‖u‖²) z`), with uniqueness in the disk `‖G‖ ≤ ‖u‖²/Im z`. On the unit sphere `Mmeas κ u` is `μ_{κ,u}`.
The same full-space `productSymbol` is used as in Part 2.

Proved here (standard axioms only):
* `fz_hasDerivAt`: `fz L κ z` has derivative `Iκ(e^{iκw} − E e^{−iκw})`, `E = e^{izL}`.
* `fz_deriv_lower`: on the disk `‖w‖ ≤ r` with `κ r ≤ 1/4` and `HighHalf L κ z`, `κ/2 ≤ ‖fz'(w)‖`.
* `gFDeriv_exists`: for `4κ < Im z`, `log 16 < L Im z` and a unit `u₀`, there are `a ≠ 0`, `S` with
  `HasFDerivAt (fun u => G_z u) (a • S) u₀` and `HasFDerivAt (fun u => productSymbol L κ u z) S u₀`.
  Route: strict derivative of `fz` at `G_z u₀`, its local inverse `ψ` (Mathlib `HasStrictDerivAt.localInverse`),
  `G_z = ψ ∘ productSymbol` eventually near `u₀` (continuity of `G_z` from the Lipschitz bound `fz_lower_radius`,
  and the eventual left inverse), then the chain rule.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric

namespace QuantumNLS.RootGLocal

open QuantumNLS.RootMeasureComplex QuantumNLS.RootFzRadius QuantumNLS.NormalizedTransfer
  QuantumNLS.PhysicalTensor QuantumNLS.RootSymbolFrechet

theorem fz_hasDerivAt (L κ : ℝ) (z w : ℂ) :
    HasDerivAt (fz L κ z)
      (Complex.I * κ * (Complex.exp (Complex.I * κ * w) -
        Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))) w := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.I * κ * w) (Complex.I * κ) w := by
    simpa using (hasDerivAt_id w).const_mul (Complex.I * κ)
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (Complex.I * κ * w))
      (Complex.exp (Complex.I * κ * w) * (Complex.I * κ)) w := h1.cexp
  have h3 : HasDerivAt (fun w : ℂ => Complex.exp (-(Complex.I * κ * w)))
      (Complex.exp (-(Complex.I * κ * w)) * (-(Complex.I * κ))) w := h1.neg.cexp
  have h4 := h2.add (h3.const_mul (Complex.exp (Complex.I * z * L)))
  convert h4 using 1
  · funext x
    simp [fz]
  · ring

theorem fz_deriv_lower {L κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {r : ℝ}
    (hr : κ * r ≤ 1 / 4) {w : ℂ} (hw : ‖w‖ ≤ r) :
    κ / 2 ≤ ‖Complex.I * κ * (Complex.exp (Complex.I * κ * w) -
      Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))‖ := by
  have hE16 : ‖Complex.exp (Complex.I * z * L)‖ ≤ 1 / 16 := norm_exp_izL_le hz
  have hxn : ‖Complex.I * κ * w‖ ≤ 1 / 4 := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, one_mul]
    calc κ * ‖w‖ ≤ κ * r := mul_le_mul_of_nonneg_left hw hκ.le
      _ ≤ 1 / 4 := hr
  have e1 := norm_exp_sub_one_le' hxn
  have hneg : ‖-(Complex.I * κ * w)‖ ≤ 1 / 4 := by rw [norm_neg]; exact hxn
  have e2 : ‖Complex.exp (-(Complex.I * κ * w))‖ ≤ 4 / 3 := norm_exp_le_four_thirds hneg
  have h5 : ‖Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w))‖ ≤ 1 / 16 * (4 / 3) := by
    rw [norm_mul]
    exact mul_le_mul hE16 e2 (norm_nonneg _) (by norm_num)
  have h6 : ‖Complex.exp (Complex.I * κ * w) - 1‖ ≤ 1 / 3 := by
    have : 4 / 3 * ‖Complex.I * κ * w‖ ≤ 4 / 3 * (1 / 4) := mul_le_mul_of_nonneg_left hxn (by norm_num)
    linarith
  have hkey : ‖Complex.exp (Complex.I * κ * w) - 1 -
      Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w))‖ ≤ 5 / 12 := by
    have := norm_sub_le (Complex.exp (Complex.I * κ * w) - 1)
      (Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))
    linarith
  have hIκ : ‖Complex.I * κ‖ = κ := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, one_mul]
  have hY : ‖Complex.I * κ * (Complex.exp (Complex.I * κ * w) - 1 -
      Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))‖ ≤ κ * (5 / 12) := by
    rw [norm_mul, hIκ]
    exact mul_le_mul_of_nonneg_left hkey hκ.le
  have htri : κ ≤ ‖Complex.I * κ * (Complex.exp (Complex.I * κ * w) -
      Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))‖ +
      ‖Complex.I * κ * (Complex.exp (Complex.I * κ * w) - 1 -
        Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))‖ := by
    calc κ = ‖Complex.I * κ‖ := hIκ.symm
      _ = ‖Complex.I * κ * (Complex.exp (Complex.I * κ * w) -
            Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w))) -
          Complex.I * κ * (Complex.exp (Complex.I * κ * w) - 1 -
            Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))‖ := by
          congr 1
          ring
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- **(ii)-b.** For `4κ < Im z`, `log 16 < L·Im z` and a unit `u₀`, the full-space Cauchy transform
`G_z(u) = cauchyTransform (Mmeas κ u) z` is Fréchet differentiable at `u₀` with derivative `a • S`, where `S` is the
derivative of `productSymbol · z` at `u₀` and `a ≠ 0`. -/
theorem gFDeriv_exists (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ < z.im)
    (hzL : Real.log 16 < L * z.im) (u0 : L2T L) (hu0 : ‖u0‖ = 1) :
    ∃ (a : ℂ) (S : L2T L →L[ℝ] ℂ), a ≠ 0 ∧
      HasFDerivAt (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
        (a • S) u0 ∧
      HasFDerivAt (fun u : L2T L => productSymbol L κ u z) S u0 := by
  have hη : 0 < z.im := by linarith
  have hκz : κ < z.im := by linarith
  have hHigh' : HighHalf L κ z := ⟨hz4.le, hzL.le⟩
  set δ : ℝ := (z.im - 4 * κ) / (8 * κ) with hδ
  have hδpos : 0 < δ := div_pos (by linarith) (by linarith)
  have hmarg : 4 * κ * (1 + δ) ≤ z.im := by
    have h4 : 4 * κ * δ = (z.im - 4 * κ) / 2 := by
      rw [hδ]; field_simp; ring
    nlinarith
  have hHigh : ∀ u : L2T L, ‖u‖ ^ 2 ≤ 1 + δ → HighHalf L (κ * ‖u‖ ^ 2) z := by
    intro u hu
    unfold HighHalf
    refine ⟨?_, hzL.le⟩
    calc 4 * (κ * ‖u‖ ^ 2) = (4 * κ) * ‖u‖ ^ 2 := by ring
      _ ≤ (4 * κ) * (1 + δ) := mul_le_mul_of_nonneg_left hu (by linarith)
      _ ≤ z.im := hmarg
  have hchar : ∀ u : L2T L, u ≠ 0 → ‖u‖ ^ 2 ≤ 1 + δ →
      ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z‖ ≤ ‖u‖ ^ 2 / z.im ∧
      fz L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) =
        productSymbol L κ u z := by
    intro u hu hn
    obtain ⟨h1, h2, _⟩ := FullMass.mass_characterization hκ hu (hHigh u hn)
    exact ⟨h1, h2⟩
  have hu0ne : u0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu0
    norm_num at hu0
  have hn0 : ‖u0‖ ^ 2 = 1 := by rw [hu0]; norm_num
  obtain ⟨hg0b, hfz0⟩ := hchar u0 hu0ne (by rw [hn0]; linarith)
  set g0 : ℂ := QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u0) z with hg0
  have hg0n : ‖g0‖ ≤ 1 / z.im := by
    have := hg0b
    rwa [hn0] at this
  set r0 : ℝ := (1 + δ) / z.im with hr0
  have hκr0 : κ * r0 ≤ 1 / 4 := by
    have e : κ * r0 = (κ * (1 + δ)) / z.im := by rw [hr0]; ring
    rw [e, div_le_iff₀ hη]
    nlinarith
  have hev : ∀ᶠ u in 𝓝 u0, u ≠ 0 ∧ ‖u‖ ^ 2 ≤ 1 + δ := by
    have hc : Tendsto (fun u : L2T L => ‖u‖ ^ 2) (𝓝 u0) (𝓝 (‖u0‖ ^ 2)) :=
      ((continuous_norm.pow 2).tendsto u0)
    have hI : ∀ᶠ u in 𝓝 u0, ‖u‖ ^ 2 ∈ Set.Ioo (0 : ℝ) (1 + δ) :=
      hc.eventually (Ioo_mem_nhds (by rw [hn0]; norm_num) (by rw [hn0]; linarith))
    filter_upwards [hI] with u hu
    obtain ⟨h1, h2⟩ := hu
    refine ⟨?_, h2.le⟩
    intro h
    rw [h, norm_zero] at h1
    norm_num at h1
  have hlip : ∀ u : L2T L, u ≠ 0 → ‖u‖ ^ 2 ≤ 1 + δ →
      κ / 2 * ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z - g0‖ ≤
        ‖productSymbol L κ u z - productSymbol L κ u0 z‖ := by
    intro u hu hn
    obtain ⟨hGu, hfu⟩ := hchar u hu hn
    have hGu' : ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z‖ ≤ r0 :=
      hGu.trans (div_le_div_of_nonneg_right hn hη.le)
    have hg0' : ‖g0‖ ≤ r0 :=
      hg0n.trans (div_le_div_of_nonneg_right (by linarith) hη.le)
    have key := fz_lower_radius hκ hHigh' hκr0 hGu' hg0'
    rw [hfu, hfz0] at key
    exact key
  have hsC : ContDiffOn ℝ 1 (fun u : L2T L => productSymbol L κ u z) (ball (0 : L2T L) 2) :=
    productSymbol_contDiffOn L κ hκ.le z hκz 2 (by norm_num) (by nlinarith)
  have hu0ball : u0 ∈ ball (0 : L2T L) 2 := by
    rw [mem_ball_zero_iff, hu0]; norm_num
  have hsd : DifferentiableAt ℝ (fun u : L2T L => productSymbol L κ u z) u0 :=
    (hsC.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hu0ball)
  have hs' : HasFDerivAt (fun u : L2T L => productSymbol L κ u z)
      (fderiv ℝ (fun u : L2T L => productSymbol L κ u z) u0) u0 := hsd.hasFDerivAt
  -- continuity of `G_z` at `u₀`
  have hbnd : ∀ᶠ u in 𝓝 u0, ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z - g0‖ ≤
      2 / κ * ‖productSymbol L κ u z - productSymbol L κ u0 z‖ := by
    filter_upwards [hev] with u hu
    have h := hlip u hu.1 hu.2
    have hk : 0 < κ / 2 := by linarith
    have h' : ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z - g0‖ * (κ / 2) ≤
        ‖productSymbol L κ u z - productSymbol L κ u0 z‖ := by
      rw [mul_comm]; exact h
    have h2 : 2 / κ * ‖productSymbol L κ u z - productSymbol L κ u0 z‖ =
        ‖productSymbol L κ u z - productSymbol L κ u0 z‖ / (κ / 2) := by
      field_simp
    rw [h2]
    exact (le_div_iff₀ hk).mpr h'
  have hs0 : Tendsto (fun u : L2T L => ‖productSymbol L κ u z - productSymbol L κ u0 z‖) (𝓝 u0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hsd.continuousAt
  have hb0 : Tendsto (fun u : L2T L => 2 / κ * ‖productSymbol L κ u z - productSymbol L κ u0 z‖) (𝓝 u0)
      (𝓝 0) := by
    simpa using hs0.const_mul (2 / κ)
  have hGcont : Tendsto (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
      (𝓝 u0) (𝓝 g0) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      hbnd hb0)
  -- the local inverse of `fz` at `g₀`
  have hC : ContDiff ℂ 1 (fz L κ z) := by
    unfold fz
    fun_prop
  set d : ℂ := Complex.I * κ * (Complex.exp (Complex.I * κ * g0) -
    Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * g0))) with hd
  have hStrict : HasStrictDerivAt (fz L κ z) d g0 := by
    have h := hC.hasStrictDerivAt (x := g0) one_ne_zero
    rw [(fz_hasDerivAt L κ z g0).deriv] at h
    exact h
  have hκq : κ * (1 / z.im) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_iff₀ hη]
    linarith
  have hd0 : d ≠ 0 := by
    have hdn : κ / 2 ≤ ‖d‖ := fz_deriv_lower hκ hHigh' hκq hg0n
    intro h
    rw [h, norm_zero] at hdn
    linarith
  have hψd : HasStrictDerivAt (HasStrictDerivAt.localInverse (fz L κ z) d g0 hStrict hd0) d⁻¹
      (fz L κ z g0) := hStrict.to_localInverse hd0
  have hleft : ∀ᶠ g in 𝓝 g0, HasStrictDerivAt.localInverse (fz L κ z) d g0 hStrict hd0 (fz L κ z g) = g :=
    hStrict.eventually_left_inverse hd0
  set ψ := HasStrictDerivAt.localInverse (fz L κ z) d g0 hStrict hd0 with hψdef
  -- `G_z = ψ ∘ productSymbol` eventually near `u₀`
  have hid : ∀ᶠ u in 𝓝 u0, ψ (productSymbol L κ u z) =
      QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z := by
    have hGt := hGcont.eventually hleft
    filter_upwards [hev, hGt] with u hu hGu
    rw [← (hchar u hu.1 hu.2).2]
    exact hGu
  -- chain rule
  have hs0eq : productSymbol L κ u0 z = fz L κ z g0 := hfz0.symm
  have hψd0 : HasDerivAt ψ d⁻¹ (productSymbol L κ u0 z) := by
    rw [hs0eq]
    exact hψd.hasDerivAt
  have hcomp : HasFDerivAt (fun u : L2T L => ψ (productSymbol L κ u z))
      (((ContinuousLinearMap.toSpanSingleton ℂ d⁻¹).restrictScalars ℝ).comp
        (fderiv ℝ (fun u : L2T L => productSymbol L κ u z) u0)) u0 :=
    (hψd0.hasFDerivAt.restrictScalars ℝ).comp u0 hs'
  have hder_eq : ((ContinuousLinearMap.toSpanSingleton ℂ d⁻¹).restrictScalars ℝ).comp
      (fderiv ℝ (fun u : L2T L => productSymbol L κ u z) u0) =
      d⁻¹ • fderiv ℝ (fun u : L2T L => productSymbol L κ u z) u0 := by
    ext x
    simp [mul_comm]
  refine ⟨d⁻¹, fderiv ℝ (fun u : L2T L => productSymbol L κ u z) u0, inv_ne_zero hd0, ?_, hs'⟩
  rw [← hder_eq]
  exact hcomp.congr_of_eventuallyEq (hid.mono fun u hu => hu.symm)

end QuantumNLS.RootGLocal

#print axioms QuantumNLS.RootGLocal.fz_hasDerivAt
#print axioms QuantumNLS.RootGLocal.fz_deriv_lower
#print axioms QuantumNLS.RootGLocal.gFDeriv_exists
