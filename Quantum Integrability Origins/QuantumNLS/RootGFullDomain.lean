import Mathlib
import QuantumNLS.RootGNeighbourhood
import QuantumNLS.RootRelationExtension
import QuantumNLS.RootFzRadius3
import QuantumNLS.RootCauchyHolo

/-!
# R-C4F43CA8 part (a), stage 3d: `G_z` is C¹ on an open neighbourhood of the unit sphere, on the full branch domain

Domain: `4κ ≤ Im z` and `log 16 ≤ L Im z` (the source's `Im z ≥ max(4κ, log16/L)`, boundary included).
Region: `gRegion3 L = {u | 0 < ‖u‖ ∧ ‖u‖² < 4/3}`, open, containing the unit sphere.

Ingredients (all frozen): the implicit relation on the whole upper half-plane (`RootRelationExtension.fz_eq_productSymbol_upper`),
the norm bound `‖G_z u‖ ≤ ‖u‖²/Im z` (`RootCauchyHolo.cauchyTransform_norm_le` and the total mass `‖u‖²`), the estimates
with `κ r ≤ 1/3` (`RootFzRadius3`), and the symbol's C¹ on `ball 0 (3/2)` (`productSymbol_contDiffOn`, which needs only
`κ (3/2)² < Im z`, so it holds at the boundary `Im z = 4κ`).

Proved (standard axioms only):
* `mmeas_real_univ`, `G_norm_le`;
* `G_hasFDerivAt_full`: derivative `(gFzD(G_z u₀))⁻¹ • S(u₀)` at each `u₀ ∈ gRegion3`;
* `G_c1_full_domain`: the final statement, `∃ V` open, containing the sphere, with `ContDiffOn ℝ 1 G_z V`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric

namespace QuantumNLS.RootGFullDomain

open QuantumNLS.RootMeasureComplex QuantumNLS.RootGNeighbourhood QuantumNLS.RootGLocal
  QuantumNLS.PhysicalTensor QuantumNLS.RootFzRadius3 QuantumNLS.RootRelationExtension
  QuantumNLS.RootCauchyHolo QuantumNLS.NormalizedTransfer QuantumNLS.RootSymbolFrechet

/-- The open region `{0 < ‖u‖, ‖u‖² < 4/3}` (contains the unit sphere). -/
def gRegion3 (L : ℝ) [Fact (0 < L)] : Set (L2T L) :=
  {u | 0 < ‖u‖ ∧ ‖u‖ ^ 2 < 4 / 3}

theorem gRegion3_isOpen (L : ℝ) [Fact (0 < L)] : IsOpen (gRegion3 L) := by
  have h1 : IsOpen {u : L2T L | 0 < ‖u‖} := isOpen_lt continuous_const continuous_norm
  have h2 : IsOpen {u : L2T L | ‖u‖ ^ 2 < 4 / 3} := isOpen_lt (continuous_norm.pow 2) continuous_const
  have e : gRegion3 L = {u : L2T L | 0 < ‖u‖} ∩ {u : L2T L | ‖u‖ ^ 2 < 4 / 3} := by
    ext u
    simp only [gRegion3, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [e]
  exact h1.inter h2

theorem sphere_subset_gRegion3 (L : ℝ) [Fact (0 < L)] :
    Metric.sphere (0 : L2T L) 1 ⊆ gRegion3 L := by
  intro u hu
  rw [mem_sphere_zero_iff_norm] at hu
  show 0 < ‖u‖ ∧ ‖u‖ ^ 2 < 4 / 3
  rw [hu]
  norm_num

theorem mmeas_real_univ (L : ℝ) [Fact (0 < L)] (κ : ℝ) (u : L2T L) : (FullMass.Mmeas κ u).real Set.univ = ‖u‖ ^ 2 := by
  rw [MeasureTheory.measureReal_def, FullMass.Mmeas_univ, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem G_norm_le (L : ℝ) [Fact (0 < L)] (κ : ℝ) (u : L2T L) {z : ℂ} (hz : 0 < z.im) :
    ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z‖ ≤ ‖u‖ ^ 2 / z.im := by
  have h := cauchyTransform_norm_le (FullMass.Mmeas κ u) hz
  rwa [mmeas_real_univ L κ u] at h

/-- **Pointwise C¹-input.** At `u₀ ∈ gRegion3` on the full domain: `fz'(G_z u₀) ≠ 0` and `G_z` is Fréchet differentiable
at `u₀` with derivative `(fz'(G_z u₀))⁻¹ • S(u₀)`. -/
theorem G_hasFDerivAt_full (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ ≤ z.im)
    (hzL : Real.log 16 ≤ L * z.im) (u0 : L2T L) (hu0p : 0 < ‖u0‖) (hu0r : ‖u0‖ ^ 2 < 4 / 3) :
    gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u0) z) ≠ 0 ∧
      HasFDerivAt (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
        ((gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u0) z))⁻¹ •
          fderiv ℝ (fun u : L2T L => productSymbol L κ u z) u0) u0 := by
  have hη : 0 < z.im := by linarith
  have hκz : κ < z.im := by linarith
  have hHigh' : HighHalf L κ z := ⟨hz4, hzL⟩
  set r0 : ℝ := (4 / 3) / z.im with hr0
  have hκr0 : κ * r0 ≤ 1 / 3 := by
    have e : κ * r0 = (κ * (4 / 3)) / z.im := by rw [hr0]; ring
    rw [e, div_le_iff₀ hη]
    linarith
  have hgr : ∀ u : L2T L, ‖u‖ ^ 2 ≤ 4 / 3 →
      ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z‖ ≤ r0 := by
    intro u hn
    exact (G_norm_le L κ u hη).trans (div_le_div_of_nonneg_right hn hη.le)
  have hu0ne : u0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu0p
    exact lt_irrefl _ hu0p
  have hu0sq : ‖u0‖ ^ 2 ≤ 4 / 3 := hu0r.le
  have hfz : ∀ u : L2T L, u ≠ 0 →
      fz L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) =
        productSymbol L κ u z :=
    fun u hu => fz_eq_productSymbol_upper L κ hκ u hu z hη
  set g0 : ℂ := QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u0) z with hg0
  have hg0r : ‖g0‖ ≤ r0 := hgr u0 hu0sq
  have hfz0 : fz L κ z g0 = productSymbol L κ u0 z := hfz u0 hu0ne
  have hev : ∀ᶠ u in 𝓝 u0, u ≠ 0 ∧ ‖u‖ ^ 2 ≤ 4 / 3 := by
    have hc : Tendsto (fun u : L2T L => ‖u‖ ^ 2) (𝓝 u0) (𝓝 (‖u0‖ ^ 2)) :=
      ((continuous_norm.pow 2).tendsto u0)
    have hI : ∀ᶠ u in 𝓝 u0, ‖u‖ ^ 2 ∈ Set.Ioo (0 : ℝ) (4 / 3) :=
      hc.eventually (Ioo_mem_nhds (pow_pos hu0p 2) hu0r)
    filter_upwards [hI] with u hu
    obtain ⟨h1, h2⟩ := hu
    refine ⟨?_, h2.le⟩
    intro h
    rw [h, norm_zero] at h1
    norm_num at h1
  have hlip : ∀ u : L2T L, u ≠ 0 → ‖u‖ ^ 2 ≤ 4 / 3 →
      κ / 5 * ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z - g0‖ ≤
        ‖productSymbol L κ u z - productSymbol L κ u0 z‖ := by
    intro u hu hn
    have key := fz_lower_radius3 hκ hHigh' hκr0 (hgr u hn) hg0r
    rw [hfz u hu, hfz0] at key
    exact key
  have hsC : ContDiffOn ℝ 1 (fun u : L2T L => productSymbol L κ u z) (ball (0 : L2T L) (3 / 2)) :=
    productSymbol_contDiffOn L κ hκ.le z hκz (3 / 2) (by norm_num) (by nlinarith)
  have hu0ball : u0 ∈ ball (0 : L2T L) (3 / 2) := by
    rw [mem_ball_zero_iff]
    nlinarith [norm_nonneg u0]
  have hsd : DifferentiableAt ℝ (fun u : L2T L => productSymbol L κ u z) u0 :=
    (hsC.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hu0ball)
  have hs' : HasFDerivAt (fun u : L2T L => productSymbol L κ u z)
      (fderiv ℝ (fun u : L2T L => productSymbol L κ u z) u0) u0 := hsd.hasFDerivAt
  have hbnd : ∀ᶠ u in 𝓝 u0, ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z - g0‖ ≤
      5 / κ * ‖productSymbol L κ u z - productSymbol L κ u0 z‖ := by
    filter_upwards [hev] with u hu
    have h := hlip u hu.1 hu.2
    have hk : 0 < κ / 5 := by linarith
    have h' : ‖QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z - g0‖ * (κ / 5) ≤
        ‖productSymbol L κ u z - productSymbol L κ u0 z‖ := by
      rw [mul_comm]
      exact h
    have h2 : 5 / κ * ‖productSymbol L κ u z - productSymbol L κ u0 z‖ =
        ‖productSymbol L κ u z - productSymbol L κ u0 z‖ / (κ / 5) := by
      field_simp
    rw [h2]
    exact (le_div_iff₀ hk).mpr h'
  have hs0 : Tendsto (fun u : L2T L => ‖productSymbol L κ u z - productSymbol L κ u0 z‖) (𝓝 u0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hsd.continuousAt
  have hb0 : Tendsto (fun u : L2T L => 5 / κ * ‖productSymbol L κ u z - productSymbol L κ u0 z‖) (𝓝 u0)
      (𝓝 0) := by
    simpa using hs0.const_mul (5 / κ)
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
    have hdn : κ / 5 ≤ ‖d‖ := fz_deriv_lower3 hκ hHigh' hκr0 hg0r
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
    rw [← hfz u hu.1]
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

theorem G_fderiv_formula_full (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ ≤ z.im)
    (hzL : Real.log 16 ≤ L * z.im) :
    ∀ u ∈ gRegion3 L,
      fderiv ℝ (fun v : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z) u =
        (gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z))⁻¹ •
          fderiv ℝ (fun v : L2T L => productSymbol L κ v z) u := by
  intro u hu
  obtain ⟨h1, h2⟩ := hu
  exact (G_hasFDerivAt_full L κ hκ z hz4 hzL u h1 h2).2.fderiv

theorem G_contDiffOn_full (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ ≤ z.im)
    (hzL : Real.log 16 ≤ L * z.im) :
    ContDiffOn ℝ 1 (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
      (gRegion3 L) := by
  have hκz : κ < z.im := by linarith
  have hDiff : DifferentiableOn ℝ
      (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) (gRegion3 L) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    exact ((G_hasFDerivAt_full L κ hκ z hz4 hzL u h1 h2).2.differentiableAt).differentiableWithinAt
  have hsC : ContDiffOn ℝ 1 (fun u : L2T L => productSymbol L κ u z) (ball (0 : L2T L) (3 / 2)) :=
    productSymbol_contDiffOn L κ hκ.le z hκz (3 / 2) (by norm_num) (by nlinarith)
  have hsub : gRegion3 L ⊆ ball (0 : L2T L) (3 / 2) := by
    intro u hu
    obtain ⟨-, h2⟩ := hu
    rw [mem_ball_zero_iff]
    nlinarith [norm_nonneg u]
  have hscont : ContinuousOn (fun u : L2T L => fderiv ℝ (fun v : L2T L => productSymbol L κ v z) u)
      (gRegion3 L) :=
    (hsC.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)).mono hsub
  have hGcont : ContinuousOn
      (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) (gRegion3 L) :=
    hDiff.continuousOn
  have hfz' : ContinuousOn
      (fun u : L2T L => gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z))
      (gRegion3 L) :=
    (continuous_gFzD L κ z).comp_continuousOn hGcont
  have hne : ∀ u ∈ gRegion3 L,
      gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) ≠ 0 := by
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    exact (G_hasFDerivAt_full L κ hκ z hz4 hzL u h1 h2).1
  have hinv : ContinuousOn
      (fun u : L2T L => (gFzD L κ z (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z))⁻¹)
      (gRegion3 L) :=
    hfz'.inv₀ hne
  have hderiv : ContinuousOn
      (fun u : L2T L => fderiv ℝ (fun v : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z) u)
      (gRegion3 L) :=
    ContinuousOn.congr (hinv.smul hscont) fun u hu => G_fderiv_formula_full L κ hκ z hz4 hzL u hu
  have key := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 0)
      (f := fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z)
      (s := gRegion3 L) (gRegion3_isOpen L)).2
    ⟨hDiff, fun h => absurd h (by simp), contDiffOn_zero.2 hderiv⟩
  exact key

/-- **Part (a), full branch domain.** For `4κ ≤ Im z` and `log 16 ≤ L·Im z` (boundary included) there is an open
neighbourhood `V` of the unit sphere on which `G_z(u) = cauchyTransform (Mmeas κ u) z` is continuously Fréchet
differentiable. -/
theorem G_c1_full_domain (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ ≤ z.im)
    (hzL : Real.log 16 ≤ L * z.im) :
    ∃ V : Set (L2T L), IsOpen V ∧ Metric.sphere (0 : L2T L) 1 ⊆ V ∧
      ContDiffOn ℝ 1
        (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) V :=
  ⟨gRegion3 L, gRegion3_isOpen L, sphere_subset_gRegion3 L, G_contDiffOn_full L κ hκ z hz4 hzL⟩

end QuantumNLS.RootGFullDomain

#print axioms QuantumNLS.RootGFullDomain.G_c1_full_domain
