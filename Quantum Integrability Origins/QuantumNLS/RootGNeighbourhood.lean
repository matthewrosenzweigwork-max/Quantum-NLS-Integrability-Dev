import QuantumNLS.FullMass
import QuantumNLS.RootFzRadius
import QuantumNLS.RootSymbolFrechet
import QuantumNLS.RootGLocal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# R-C4F43CA8 part (3)(ii)-b, neighbourhood form: `G_z` is C¹ on an open neighbourhood of the unit sphere

**Convention (integrator decision, as in `RootGLocal`):** `G_z(u) := cauchyTransform (FullMass.Mmeas κ u) z` for
every `u ∈ L²`, the full-space Cauchy transform. The same full-space `productSymbol` as in Part 2.

The region is `gRegion L κ z = {u | 0 < ‖u‖ ∧ ‖u‖² < 1 + δ ∧ ‖u‖ < 2}` with `δ = gMargin κ z = (Im z − 4κ)/(8κ)`.
It is open, contains the unit sphere (`δ > 0`), and lies in the strict region: `4κ‖u‖² ≤ 4κ(1+δ) ≤ Im z`
(`gRegion_strict`), so `HighHalf L (κ‖u‖²) z` holds there.

Proved here (standard axioms only):
* `G_hasFDerivAt_region`: at every `u₀ ∈ gRegion` (not only at unit vectors) `fz'(G_z u₀) ≠ 0` and `G_z` is Fréchet
  differentiable at `u₀` with derivative `(fz'(G_z u₀))⁻¹ • S(u₀)`, `S = fderiv (productSymbol · z)`. Same route as
  `RootGLocal.gFDeriv_exists`, with the uniform radius `r₀ = (1+δ)/Im z` in place of `1/Im z`
  (on the region `‖G_z u‖ ≤ ‖u‖²/Im z ≤ r₀`).
* `G_fderiv_formula_gRegion`: the derivative formula at every point of the region.
* `G_contDiffOn_gRegion`: `ContDiffOn ℝ 1 G_z gRegion` (the derivative is continuous: `G_z` is continuous, `fz'` is
  continuous and nonzero, `S` is continuous by `productSymbol_contDiffOn`).
* `G_c1_sphere_neighbourhood`: the final statement, with an explicit open neighbourhood of the unit sphere.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric

namespace QuantumNLS.RootGNeighbourhood

open QuantumNLS.RootMeasureComplex QuantumNLS.RootFzRadius QuantumNLS.NormalizedTransfer
  QuantumNLS.PhysicalTensor QuantumNLS.RootSymbolFrechet QuantumNLS.RootGLocal

/-- The strict margin `δ = (Im z − 4κ)/(8κ)`, as in `gFDeriv_exists`. -/
def gMargin (κ : ℝ) (z : ℂ) : ℝ := (z.im - 4 * κ) / (8 * κ)

/-- The derivative of `fz L κ z` as a function of the point `w` (same expression as `fz_hasDerivAt`). -/
def gFzD (L κ : ℝ) (z w : ℂ) : ℂ :=
  Complex.I * κ * (Complex.exp (Complex.I * κ * w) -
    Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))

/-- The open neighbourhood `{0 < ‖u‖, ‖u‖² < 1+δ, ‖u‖ < 2}` of the unit sphere. -/
def gRegion (L : ℝ) [Fact (0 < L)] (κ : ℝ) (z : ℂ) : Set (L2T L) :=
  {u | 0 < ‖u‖ ∧ ‖u‖ ^ 2 < 1 + gMargin κ z ∧ ‖u‖ < 2}

theorem gMargin_pos {κ : ℝ} {z : ℂ} (hκ : 0 < κ) (hz4 : 4 * κ < z.im) : 0 < gMargin κ z :=
  div_pos (by linarith) (by linarith)

theorem gMargin_marg {κ : ℝ} {z : ℂ} (hκ : 0 < κ) (hz4 : 4 * κ < z.im) :
    4 * κ * (1 + gMargin κ z) ≤ z.im := by
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have h4 : 4 * κ * gMargin κ z = (z.im - 4 * κ) / 2 := by
    unfold gMargin
    field_simp
    ring
  have e : 4 * κ * (1 + gMargin κ z) = 4 * κ + 4 * κ * gMargin κ z := by ring
  rw [e, h4]
  linarith

theorem continuous_gFzD (L κ : ℝ) (z : ℂ) : Continuous (gFzD L κ z) := by
  unfold gFzD
  fun_prop

theorem G_hasFDerivAt_region (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ < z.im)
    (hzL : Real.log 16 < L * z.im) (u0 : L2T L) (hu0p : 0 < ‖u0‖) (hu0r : ‖u0‖ ^ 2 < 1 + gMargin κ z)
    (hu0b : ‖u0‖ < 2) :
    gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u0) z) ≠ 0 ∧
      HasFDerivAt (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
        ((gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u0) z))⁻¹ •
          fderiv ℝ (fun u : L2T L => productSymbol L κ u z) u0) u0 := by
  have hη : 0 < z.im := by linarith
  have hκz : κ < z.im := by linarith
  have hHigh' : HighHalf L κ z := ⟨hz4.le, hzL.le⟩
  have hmarg : 4 * κ * (1 + gMargin κ z) ≤ z.im := gMargin_marg hκ hz4
  have hHigh : ∀ u : L2T L, ‖u‖ ^ 2 ≤ 1 + gMargin κ z → HighHalf L (κ * ‖u‖ ^ 2) z := by
    intro u hu
    unfold HighHalf
    refine ⟨?_, hzL.le⟩
    calc 4 * (κ * ‖u‖ ^ 2) = (4 * κ) * ‖u‖ ^ 2 := by ring
      _ ≤ (4 * κ) * (1 + gMargin κ z) := mul_le_mul_of_nonneg_left hu (by linarith [gMargin_pos hκ hz4])
      _ ≤ z.im := hmarg
  have hchar : ∀ u : L2T L, u ≠ 0 → ‖u‖ ^ 2 ≤ 1 + gMargin κ z →
      ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z‖ ≤ ‖u‖ ^ 2 / z.im ∧
      fz L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) =
        productSymbol L κ u z := by
    intro u hu hn
    obtain ⟨h1, h2, _⟩ := FullMass.mass_characterization hκ hu (hHigh u hn)
    exact ⟨h1, h2⟩
  set r0 : ℝ := (1 + gMargin κ z) / z.im with hr0
  have hκr0 : κ * r0 ≤ 1 / 4 := by
    have e : κ * r0 = (κ * (1 + gMargin κ z)) / z.im := by rw [hr0]; ring
    rw [e, div_le_iff₀ hη]
    nlinarith
  have hgr : ∀ u : L2T L, u ≠ 0 → ‖u‖ ^ 2 ≤ 1 + gMargin κ z →
      ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z‖ ≤ r0 := by
    intro u hu hn
    exact (hchar u hu hn).1.trans (div_le_div_of_nonneg_right hn hη.le)
  have hu0ne : u0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu0p
    exact lt_irrefl _ hu0p
  have hu0sq : ‖u0‖ ^ 2 ≤ 1 + gMargin κ z := hu0r.le
  obtain ⟨-, hfz0⟩ := hchar u0 hu0ne hu0sq
  set g0 : ℂ := QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u0) z with hg0
  have hg0r : ‖g0‖ ≤ r0 := hgr u0 hu0ne hu0sq
  have hev : ∀ᶠ u in 𝓝 u0, u ≠ 0 ∧ ‖u‖ ^ 2 ≤ 1 + gMargin κ z := by
    have hc : Tendsto (fun u : L2T L => ‖u‖ ^ 2) (𝓝 u0) (𝓝 (‖u0‖ ^ 2)) :=
      ((continuous_norm.pow 2).tendsto u0)
    have hI : ∀ᶠ u in 𝓝 u0, ‖u‖ ^ 2 ∈ Set.Ioo (0 : ℝ) (1 + gMargin κ z) :=
      hc.eventually (Ioo_mem_nhds (pow_pos hu0p 2) hu0r)
    filter_upwards [hI] with u hu
    obtain ⟨h1, h2⟩ := hu
    refine ⟨?_, h2.le⟩
    intro h
    rw [h, norm_zero] at h1
    norm_num at h1
  have hlip : ∀ u : L2T L, u ≠ 0 → ‖u‖ ^ 2 ≤ 1 + gMargin κ z →
      κ / 2 * ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z - g0‖ ≤
        ‖productSymbol L κ u z - productSymbol L κ u0 z‖ := by
    intro u hu hn
    obtain ⟨-, hfu⟩ := hchar u hu hn
    have key := fz_lower_radius hκ hHigh' hκr0 (hgr u hu hn) hg0r
    rw [hfu, hfz0] at key
    exact key
  have hsC : ContDiffOn ℝ 1 (fun u : L2T L => productSymbol L κ u z) (ball (0 : L2T L) 2) :=
    productSymbol_contDiffOn L κ hκ.le z hκz 2 (by norm_num) (by nlinarith)
  have hu0ball : u0 ∈ ball (0 : L2T L) 2 := by
    rw [mem_ball_zero_iff]
    exact hu0b
  have hsd : DifferentiableAt ℝ (fun u : L2T L => productSymbol L κ u z) u0 :=
    (hsC.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hu0ball)
  have hs' : HasFDerivAt (fun u : L2T L => productSymbol L κ u z)
      (fderiv ℝ (fun u : L2T L => productSymbol L κ u z) u0) u0 := hsd.hasFDerivAt
  have hbnd : ∀ᶠ u in 𝓝 u0, ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z - g0‖ ≤
      2 / κ * ‖productSymbol L κ u z - productSymbol L κ u0 z‖ := by
    filter_upwards [hev] with u hu
    have h := hlip u hu.1 hu.2
    have hk : 0 < κ / 2 := by linarith
    have h' : ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z - g0‖ * (κ / 2) ≤
        ‖productSymbol L κ u z - productSymbol L κ u0 z‖ := by
      rw [mul_comm]
      exact h
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
      (𝓝 u0) (𝓝 g0) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbnd hb0)
  have hC : ContDiff ℂ 1 (fz L κ z) := by
    unfold fz
    fun_prop
  set d : ℂ := gFzD L κ z g0 with hd
  have hStrict : HasStrictDerivAt (fz L κ z) d g0 := by
    have h := hC.hasStrictDerivAt (x := g0) one_ne_zero
    rw [(fz_hasDerivAt L κ z g0).deriv] at h
    exact h
  have hd0 : d ≠ 0 := by
    have hdn : κ / 2 ≤ ‖d‖ := fz_deriv_lower hκ hHigh' hκr0 hg0r
    intro h
    rw [h, norm_zero] at hdn
    linarith
  have hψd : HasStrictDerivAt (HasStrictDerivAt.localInverse (fz L κ z) d g0 hStrict hd0) d⁻¹
      (fz L κ z g0) := hStrict.to_localInverse hd0
  have hleft : ∀ᶠ g in 𝓝 g0, HasStrictDerivAt.localInverse (fz L κ z) d g0 hStrict hd0 (fz L κ z g) = g :=
    hStrict.eventually_left_inverse hd0
  set ψ := HasStrictDerivAt.localInverse (fz L κ z) d g0 hStrict hd0 with hψdef
  have hid : ∀ᶠ u in 𝓝 u0, ψ (productSymbol L κ u z) =
      QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z := by
    have hGt := hGcont.eventually hleft
    filter_upwards [hev, hGt] with u hu hGu
    rw [← (hchar u hu.1 hu.2).2]
    exact hGu
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
  refine ⟨hd0, ?_⟩
  rw [← hder_eq]
  exact hcomp.congr_of_eventuallyEq (hid.mono fun u hu => hu.symm)

theorem gRegion_isOpen (L : ℝ) [Fact (0 < L)] (κ : ℝ) (z : ℂ) : IsOpen (gRegion L κ z) := by
  have h1 : IsOpen {u : L2T L | 0 < ‖u‖} := isOpen_lt continuous_const continuous_norm
  have h2 : IsOpen {u : L2T L | ‖u‖ ^ 2 < 1 + gMargin κ z} :=
    isOpen_lt (continuous_norm.pow 2) continuous_const
  have h3 : IsOpen {u : L2T L | ‖u‖ < 2} := isOpen_lt continuous_norm continuous_const
  have e : gRegion L κ z =
      ({u : L2T L | 0 < ‖u‖} ∩ {u : L2T L | ‖u‖ ^ 2 < 1 + gMargin κ z}) ∩ {u : L2T L | ‖u‖ < 2} := by
    ext u
    simp only [gRegion, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [e]
  exact (h1.inter h2).inter h3

theorem sphere_subset_gRegion (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ < z.im) :
    Metric.sphere (0 : L2T L) 1 ⊆ gRegion L κ z := by
  intro u hu
  rw [mem_sphere_zero_iff_norm] at hu
  have hδ : 0 < gMargin κ z := gMargin_pos hκ hz4
  show 0 < ‖u‖ ∧ ‖u‖ ^ 2 < 1 + gMargin κ z ∧ ‖u‖ < 2
  rw [hu]
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [one_pow]
  linarith

theorem gRegion_strict (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ < z.im) (u : L2T L)
    (hu : u ∈ gRegion L κ z) : 4 * κ * ‖u‖ ^ 2 ≤ z.im := by
  obtain ⟨-, h2, -⟩ := hu
  have h4 : 0 ≤ 4 * κ := by linarith
  have := mul_le_mul_of_nonneg_left h2.le h4
  linarith [gMargin_marg hκ hz4]

theorem G_fderiv_formula_gRegion (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ < z.im)
    (hzL : Real.log 16 < L * z.im) :
    ∀ u ∈ gRegion L κ z,
      fderiv ℝ (fun v : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z) u =
        (gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z))⁻¹ •
          fderiv ℝ (fun v : L2T L => productSymbol L κ v z) u := by
  intro u hu
  obtain ⟨h1, h2, h3⟩ := hu
  exact (G_hasFDerivAt_region L κ hκ z hz4 hzL u h1 h2 h3).2.fderiv

theorem G_contDiffOn_gRegion (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ < z.im)
    (hzL : Real.log 16 < L * z.im) :
    ContDiffOn ℝ 1 (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
      (gRegion L κ z) := by
  have hκz : κ < z.im := by linarith
  have hDiff : DifferentiableOn ℝ
      (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) (gRegion L κ z) := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := hu
    exact ((G_hasFDerivAt_region L κ hκ z hz4 hzL u h1 h2 h3).2.differentiableAt).differentiableWithinAt
  have hsC : ContDiffOn ℝ 1 (fun u : L2T L => productSymbol L κ u z) (ball (0 : L2T L) 2) :=
    productSymbol_contDiffOn L κ hκ.le z hκz 2 (by norm_num) (by nlinarith)
  have hsub : gRegion L κ z ⊆ ball (0 : L2T L) 2 := by
    intro u hu
    obtain ⟨-, -, h3⟩ := hu
    exact mem_ball_zero_iff.2 h3
  have hscont : ContinuousOn (fun u : L2T L => fderiv ℝ (fun v : L2T L => productSymbol L κ v z) u)
      (gRegion L κ z) :=
    (hsC.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)).mono hsub
  have hGcont : ContinuousOn
      (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) (gRegion L κ z) :=
    hDiff.continuousOn
  have hfz : ContinuousOn
      (fun u : L2T L => gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z))
      (gRegion L κ z) :=
    (continuous_gFzD L κ z).comp_continuousOn hGcont
  have hne : ∀ u ∈ gRegion L κ z,
      gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) ≠ 0 := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := hu
    exact (G_hasFDerivAt_region L κ hκ z hz4 hzL u h1 h2 h3).1
  have hinv : ContinuousOn
      (fun u : L2T L => (gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z))⁻¹)
      (gRegion L κ z) :=
    hfz.inv₀ hne
  have hderiv : ContinuousOn
      (fun u : L2T L => fderiv ℝ (fun v : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z) u)
      (gRegion L κ z) :=
    ContinuousOn.congr (hinv.smul hscont) fun u hu => G_fderiv_formula_gRegion L κ hκ z hz4 hzL u hu
  have key := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 0)
      (f := fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
      (s := gRegion L κ z) (gRegion_isOpen L κ z)).2
    ⟨hDiff, fun h => absurd h (by simp), contDiffOn_zero.2 hderiv⟩
  exact key

/-- **(ii)-b, neighbourhood form.** For `4κ < Im z`, `log 16 < L·Im z`, there is an open neighbourhood `V` of the unit
sphere on which the full-space `G_z(u) = cauchyTransform (Mmeas κ u) z` is continuously Fréchet differentiable. -/
theorem G_c1_sphere_neighbourhood (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ < z.im)
    (hzL : Real.log 16 < L * z.im) :
    ∃ V : Set (L2T L), IsOpen V ∧ Metric.sphere (0 : L2T L) 1 ⊆ V ∧
      ContDiffOn ℝ 1
        (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) V :=
  ⟨gRegion L κ z, gRegion_isOpen L κ z, sphere_subset_gRegion L κ hκ z hz4,
    G_contDiffOn_gRegion L κ hκ z hz4 hzL⟩

end QuantumNLS.RootGNeighbourhood

#print axioms QuantumNLS.RootGNeighbourhood.G_c1_sphere_neighbourhood
#print axioms QuantumNLS.RootGNeighbourhood.G_hasFDerivAt_region
