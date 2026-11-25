import Mathlib
import QuantumNLS.PlaneWaveSymbol
import QuantumNLS.SemicircleStieltjes
import QuantumNLS.FreeLimit
import QuantumNLS.RootMeasureExistence

/-!
# R-28C650F0 `prop:root-free`, plane-wave clause: `μ_{κ,u}` is the shifted semicircle law

Source: `ROOT_spectral_measure.tex`, `prop:root-free`: for the normalized plane wave `u = L^{-1/2}e^{ipx}`, `p = 2πm/L`, the quantum-derived measure at positive coupling is
`dμ_{κ,u}(t) = √(4κ/L − (t−p)²)₊ /(2πκ/L) dt`.

Proof as printed: the product symbol is `s(z;u) = e^{ρ₁L} + e^{ρ₂L}` (`PlaneWaveSymbol.symbol_plane`); the Cauchy transform `h` of the semicircle law solves `(κ/L)h² − (z−p)h + 1 = 0`
(`SemicircleStieltjes.quadratic_hh`), hence `ρ₁ = i(κ/L)h(z−p)`, `ρ₂ = i(z−p) − ρ₁` satisfy `ρ₁ρ₂ = −κ/L` and `e^{iκh} + e^{izL}e^{−iκh} = s(z;u)`;
`|h| ≤ 1/Im z` and the injectivity estimate identify `h` with `g(z)` (`unique_fixed`) on the high half-plane; `CauchyUniqueness.cauchy_ext` finishes.

* `nuP a p`: the semicircle law of parameter `a` translated by `p`;
* `plane_wave_semicircle : muKappa u hu κ = nuP (κ/L) (2πm/L)` (as probability measures);
* `plane_wave_density`: the measure `μ_{κ,u}` equals `volume.withDensity (t ↦ √(4κ/L − (t−p)²)/(2πκ/L))`, the printed density (`Real.sqrt` of a negative number is `0`, which is the printed `(·)₊`).
No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

noncomputable section

open Classical

namespace QuantumNLS.PlaneWaveSemicircle

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (modeLp)
open QuantumNLS.CauchyUniqueness (cauchyTransform cauchy_ext)
open QuantumNLS.SemicircleODE (w bnd w_nonneg)
open QuantumNLS.SemicircleStieltjes (scMeasure isProb_sc hh norm_hh_le quadratic_hh cauchy_scMeasure sq_ne)
open QuantumNLS.RootMeasureComplex (fz HighHalf)
open QuantumNLS.RootMeasureConcentration (gStar gStar_spec unique_fixed)
open QuantumNLS.NormalizedTransfer (productSymbol)
open QuantumNLS.PlaneWaveSymbol (pm symbol_plane exp_p_L)
open QuantumNLS.FreeLimit (muKappa muKappa_spec)

variable {L : ℝ} [Fact (0 < L)]

/-- The semicircle law of parameter `a`, translated by `p`. -/
def nuP (a p : ℝ) : Measure ℝ := (scMeasure a).map (fun t => t + p)

theorem isProb_nuP {a : ℝ} (ha : 0 < a) (p : ℝ) : IsProbabilityMeasure (nuP a p) := by
  haveI := isProb_sc ha
  exact (Measure.isProbabilityMeasure_map_iff (measurable_add_const p).aemeasurable).2 (isProb_sc ha)

theorem cauchy_nuP {a : ℝ} (ha : 0 < a) (p : ℝ) {z : ℂ} (hz : 0 < z.im) :
    cauchyTransform (nuP a p) z = hh a (z - (p : ℂ)) := by
  have hz' : 0 < (z - (p : ℂ)).im := by simpa using hz
  unfold cauchyTransform nuP
  have hm : Measurable (fun t : ℝ => t + p) := measurable_add_const p
  have hc : Continuous (fun t : ℝ => (z - (t : ℂ))⁻¹) :=
    (continuous_const.sub Complex.continuous_ofReal).inv₀ (fun t h => by
      have := congrArg Complex.im h; simp at this; linarith)
  rw [integral_map hm.aemeasurable hc.aestronglyMeasurable]
  have : ∀ t : ℝ, (z - ((t + p : ℝ) : ℂ))⁻¹ = ((z - (p : ℂ)) - (t : ℂ))⁻¹ := fun t => by
    congr 1; push_cast; ring
  simp_rw [this]
  exact (cauchy_scMeasure ha hz').trans rfl

theorem gStar_eq_hh {κ : ℝ} (hκ : 0 < κ) (m : ℤ) (hu : ‖modeLp L m‖ = 1) {z : ℂ} (hz : HighHalf L κ z) :
    gStar L κ hκ (modeLp L m) hu z = hh (κ / L) (z - (pm L m : ℂ)) := by
  have hL : 0 < L := Fact.out
  have hη : 0 < z.im := by linarith [hz.1]
  have ha : 0 < κ / L := div_pos hκ hL
  set a : ℝ := κ / L with hadef
  set ww : ℂ := z - (pm L m : ℂ) with hww
  have hwim : 0 < ww.im := by simp [hww]; exact hη
  have hq := quadratic_hh ha hwim
  have hn := norm_hh_le ha hwim
  have hwimeq : ww.im = z.im := by simp [hww]
  rw [hwimeq] at hn
  set h : ℂ := hh a ww with hhdef
  set ρ1 : ℂ := Complex.I * (a : ℂ) * h with hρ1
  set ρ2 : ℂ := Complex.I * ww - ρ1 with hρ2
  have hsum : ρ1 + ρ2 = Complex.I * ww := by rw [hρ2]; ring
  have hprod : ρ1 * ρ2 = -((a : ℝ) : ℂ) := by
    rw [hρ2, hρ1]
    linear_combination (a : ℂ) * hq + ((a : ℂ) * h * ww - (a : ℂ) ^ 2 * h ^ 2) * Complex.I_sq
  have h12 : ρ1 ≠ ρ2 := by
    intro heq
    have h2 : (Complex.I * ww) ^ 2 = 4 * (ρ1 * ρ2) := by
      have : Complex.I * ww = 2 * ρ1 := by rw [← hsum, ← heq]; ring
      rw [this, ← heq]; ring
    rw [hprod] at h2
    apply sq_ne ha hwim
    have hI : (Complex.I * ww) ^ 2 = -ww ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
    rw [hI] at h2
    linear_combination -h2
  have hsymb := symbol_plane (L := L) hκ.ne' m hη hsum hprod h12
  -- `f_z(h) = s(z;u)`
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hκc : (κ : ℂ) = (a : ℂ) * (L : ℂ) := by rw [hadef]; push_cast; field_simp
  have e1 : Complex.exp (ρ1 * L) = Complex.exp (Complex.I * κ * h) := by
    congr 1; rw [hρ1, hκc]; ring
  have e2 : Complex.exp (ρ2 * L) = Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * h)) := by
    have := exp_p_L (L := L) m
    have e3 : ρ2 * (L : ℂ) = Complex.I * z * L + (-(Complex.I * ((pm L m * L : ℝ) : ℂ))) + (-(Complex.I * κ * h)) := by
      rw [hρ2, hρ1, hκc, hww]; push_cast; ring
    rw [e3, Complex.exp_add, Complex.exp_add, this, mul_one]
  have hfz : fz L κ z h = productSymbol L κ (modeLp L m) z := by
    unfold fz
    rw [hsymb, e1, e2]
  obtain ⟨hg1, hg2⟩ := gStar_spec hκ (modeLp L m) hu hz
  exact unique_fixed hκ hz hg1 hn (hg2.trans hfz.symm)


/-- **The plane-wave semicircle** (`prop:root-free`, second clause). -/
theorem plane_wave_semicircle {κ : ℝ} (hκ : 0 < κ) (m : ℤ) (hu : ‖modeLp L m‖ = 1) :
    (muKappa (modeLp L m) hu κ : Measure ℝ) = nuP (κ / L) (pm L m) := by
  have hL : 0 < L := Fact.out
  have ha : 0 < κ / L := div_pos hκ hL
  haveI := isProb_nuP ha (pm L m)
  set η₀ : ℝ := max (4 * κ) (Real.log 16 / L) with hη₀
  have hη0 : 0 < η₀ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine cauchy_ext _ _ hη0 (fun t => ?_)
  have hHigh : HighHalf L κ ((t : ℂ) + η₀ * Complex.I) := by
    have him : ((t : ℂ) + η₀ * Complex.I).im = η₀ := by simp
    refine ⟨by rw [him]; exact le_max_left _ _, ?_⟩
    rw [him]
    have : Real.log 16 / L ≤ η₀ := le_max_right _ _
    rwa [div_le_iff₀ hL, mul_comm] at this
  have hpos : 0 < ((t : ℂ) + η₀ * Complex.I).im := by simpa using hη0
  rw [QuantumNLS.RootMeasureExistence.cauchy_limiting_measure hκ _ hu (muKappa_spec _ hu hκ) hHigh,
    cauchy_nuP ha _ hpos, gStar_eq_hh hκ m hu hHigh]

#print axioms QuantumNLS.PlaneWaveSemicircle.cauchy_nuP
#print axioms QuantumNLS.PlaneWaveSemicircle.gStar_eq_hh
#print axioms QuantumNLS.PlaneWaveSemicircle.plane_wave_semicircle

/-! ### The printed density -/

theorem dens_zero_off {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : t ∉ Ioc (-bnd a) (bnd a)) :
    ENNReal.ofReal (w a t / (2 * π * a)) = 0 := by
  have hb2 := QuantumNLS.SemicircleODE.bnd_sq ha.le
  have hb := QuantumNLS.SemicircleStieltjes.bnd_pos ha
  have h0 : w a t = 0 := by
    unfold w
    apply Real.sqrt_eq_zero_of_nonpos
    have : bnd a < t ∨ t ≤ -bnd a := by
      by_contra hcon
      push_neg at hcon
      exact ht ⟨by linarith [hcon.2], hcon.1⟩
    rcases this with h | h <;> nlinarith
  rw [h0]; simp

theorem scMeasure_eq_volume {a : ℝ} (ha : 0 < a) :
    scMeasure a = volume.withDensity (fun t => ENNReal.ofReal (w a t / (2 * π * a))) := by
  unfold scMeasure
  rw [← withDensity_indicator measurableSet_Ioc]
  congr 1
  funext t
  by_cases h : t ∈ Ioc (-bnd a) (bnd a)
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, dens_zero_off ha h]

theorem map_withDensity_translate (f : ℝ → ℝ≥0∞) (p : ℝ) :
    (volume.withDensity f).map (fun t => t + p) = volume.withDensity (fun t => f (t - p)) := by
  ext A hA
  have hA' : MeasurableSet ((fun t : ℝ => t + p) ⁻¹' A) := measurable_add_const p hA
  rw [Measure.map_apply (measurable_add_const p) hA, withDensity_apply _ hA', withDensity_apply _ hA,
    ← lintegral_indicator hA', ← lintegral_indicator hA]
  have e : ∀ a : ℝ, ((fun t : ℝ => t + p) ⁻¹' A).indicator f a = A.indicator (fun s => f (s - p)) (a + p) := by
    intro a
    by_cases h : a + p ∈ A <;> simp [Set.indicator_apply, h]
  simp_rw [e]
  exact lintegral_add_right_eq_self (A.indicator fun s => f (s - p)) p

/-- **The printed density**: `dμ_{κ,u}(t) = √(4κ/L − (t−p)²)₊/(2πκ/L) dt`. -/
theorem plane_wave_density {κ : ℝ} (hκ : 0 < κ) (m : ℤ) (hu : ‖modeLp L m‖ = 1) :
    (muKappa (modeLp L m) hu κ : Measure ℝ) =
      volume.withDensity (fun t => ENNReal.ofReal
        (Real.sqrt (4 * (κ / L) - (t - pm L m) ^ 2) / (2 * π * (κ / L)))) := by
  have hL : 0 < L := Fact.out
  have ha : 0 < κ / L := div_pos hκ hL
  rw [plane_wave_semicircle hκ m hu, nuP, scMeasure_eq_volume ha, map_withDensity_translate]
  rfl

end QuantumNLS.PlaneWaveSemicircle

#print axioms QuantumNLS.PlaneWaveSemicircle.plane_wave_density
