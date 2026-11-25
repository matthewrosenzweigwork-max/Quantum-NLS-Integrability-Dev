import Mathlib
import QuantumNLS.RootIndexedMassesFull
import QuantumNLS.RootDensityIdentification
import QuantumNLS.RootMassInvolutionR8

/-!
# R-950BFB30 `thm:root-indexed-masses`: "vanishing spectral intervals contribute zero", proved from the density

Source: `source-text/chapters/foundations/ROOT_indexed_masses.tex`, Theorem `thm:root-indexed-masses` ("Vanishing spectral intervals contribute zero, with no choice of an angle or a division by their mass") and its proof:
"Inside the `n`th interval, the phase lies strictly between `(n−1/2)π` and `(n+1/2)π`. Wherever the density is positive, the real phase is an integer multiple of `π`; its value in this interval must therefore be `nπ`.
If there is no such open subinterval, the continuous density is zero and the corresponding mass vanishes."

`RootIndexedMassesFull` (sol_multi, `719cae99`, read-only) proves the sixth clause only in the form "if the physical measure of the separator cell is zero, then its indexed mass is zero" (Terra r14: not the printed link).
This module proves the printed link for the actual limiting measure `PhysicalQuantumMeasure.measure hκ u` (R-7E0532E7: continuous density `(πκ)⁻¹ arcosh(|Δ_u|/2)` on `{|Δ_u| > 2}`, `0` elsewhere; `RootDensityIdentification.root_density`)
and the phase-label statement, with `Δ_u(x) = Re L2SpatialTransfer.discriminant κ u x`, `cell n = (separator (n−1), separator n)`, `theta = Re boundary` (`RootIndexedPhase.theta`).
A *spectral interval of positive density in the `n`th cell* is an open interval `(a,b) ⊆ cell n`, `a < b`, with `|Δ_u| > 2` on it.

* `cell_phase`: on `cell n`, `(n−1/2)π < theta < (n+1/2)π`;
* `phase_label`: on every positive-density interval inside `cell n`, `theta = nπ` (gap constancy of the boundary phase, `PhysicalContinuousBoundary.gap_constancy`, plus the strip);
* `mass_zero_of_collapsed`: if `cell n` contains no positive-density interval, the physical measure of the cell, hence the indexed mass `I_n`, is zero. The geometric implication is sol_multi's `RootMassInvolutionR8.collapsed_cell_measure_zero`
  (read-only, not re-proved here; `PosInterval` is definitionally `HasOpenSpectralInterval`, `posInterval_iff`);
* `mass_zero_iff` (`u ≠ 0`): `I_n = 0` exactly when `cell n` contains no positive-density interval;
* `root_indexed_masses_collapsed`: all printed clauses of `thm:root-indexed-masses` (the eleven clauses of `RootIndexedMassesFull.root_indexed_masses`, the sixth replaced) with no measure-zero hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.RootIndexedMassesCollapsed

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.RootDensity (hfun)
open QuantumNLS.PhysicalQuantumMeasure (measure)

variable {L κ : ℝ} [Fact (0 < L)]

/-- `Δ_u(x) = Re` of the `L²` discriminant on the real line. -/
def Dre (κ : ℝ) (u : L2T L) (x : ℝ) : ℝ := (QuantumNLS.L2SpatialTransfer.discriminant κ u (x : ℂ)).re

theorem continuous_Dre (κ : ℝ) (u : L2T L) : Continuous (Dre κ u) := by
  have hd : Continuous fun t : ℝ => QuantumNLS.L2SpatialTransfer.discriminant κ u (t : ℂ) :=
    (QuantumNLS.PhysicalUpperTraceIdentity.entire_discriminant κ u).continuous.comp Complex.continuous_ofReal
  exact Complex.continuous_re.comp hd

/-- The `n`th separator cell. -/
def cell (hκ : 0 < κ) (u : L2T L) (n : ℤ) : Set ℝ :=
  Ioo (QuantumNLS.RootIndexedPhase.separator hκ u (n - 1)) (QuantumNLS.RootIndexedPhase.separator hκ u n)

/-- A spectral interval of positive density inside the `n`th cell. -/
def PosInterval (hκ : 0 < κ) (u : L2T L) (n : ℤ) : Prop :=
  ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ cell hκ u n ∧ ∀ x ∈ Ioo a b, 2 < |Dre κ u x|

theorem cell_phase (hκ : 0 < κ) (u : L2T L) (n : ℤ) {x : ℝ} (hx : x ∈ cell hκ u n) :
    ((n : ℝ) - 1 / 2) * Real.pi < QuantumNLS.RootIndexedPhase.theta hκ u x ∧
      QuantumNLS.RootIndexedPhase.theta hκ u x < ((n : ℝ) + 1 / 2) * Real.pi := by
  obtain ⟨h1, h2⟩ := hx
  have e1 : ((((n - 1 : ℤ) : ℝ)) + 1 / 2) * Real.pi < QuantumNLS.RootIndexedPhase.theta hκ u x :=
    ((QuantumNLS.PhysicalSourceFinal.sourceFacts hκ u).phase.separator_lt_iff x (n - 1)).1 h1
  have e2 : QuantumNLS.RootIndexedPhase.theta hκ u x < ((n : ℝ) + 1 / 2) * Real.pi :=
    ((QuantumNLS.PhysicalSourceFinal.sourceFacts hκ u).phase.lt_separator_iff x n).1 h2
  refine ⟨?_, e2⟩
  have : (((n - 1 : ℤ) : ℝ) + 1 / 2) * Real.pi = ((n : ℝ) - 1 / 2) * Real.pi := by push_cast; ring
  rw [← this]
  exact e1

theorem phase_label (hκ : 0 < κ) (u : L2T L) (n : ℤ) (h : PosInterval hκ u n) :
    ∀ a b : ℝ, a < b → Ioo a b ⊆ cell hκ u n → (∀ x ∈ Ioo a b, 2 < |Dre κ u x|) →
      ∀ x ∈ Ioo a b, QuantumNLS.RootIndexedPhase.theta hκ u x = n * Real.pi := by
  intro a b hab hsub hg
  obtain ⟨k, hk⟩ := QuantumNLS.PhysicalContinuousBoundary.gap_constancy hκ u hab hg
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  obtain ⟨hlo, hhi⟩ := cell_phase hκ u n (hsub hmid)
  have hkx := hk _ hmid
  have hth : QuantumNLS.RootIndexedPhase.theta hκ u ((a + b) / 2) = k * Real.pi := hkx
  rw [hth] at hlo hhi
  have hpi := Real.pi_pos
  have h1 : (n : ℝ) - 1 / 2 < k := by
    by_contra hc; push_neg at hc; nlinarith
  have h2 : (k : ℝ) < n + 1 / 2 := by
    by_contra hc; push_neg at hc; nlinarith
  have hkn : k = n := by
    have h3 : n - 1 < k := by exact_mod_cast (by linarith : (n : ℝ) - 1 < k)
    have h4 : k < n + 1 := by exact_mod_cast (by linarith : (k : ℝ) < n + 1)
    omega
  intro x hx
  have := hk x hx
  have e : QuantumNLS.RootIndexedPhase.theta hκ u x = k * Real.pi := this
  rw [e, hkn]

/-- `PosInterval` is sol_multi's `HasOpenSpectralInterval` (same definition). -/
theorem posInterval_iff (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    PosInterval hκ u n ↔ QuantumNLS.RootMassInvolutionR8.HasOpenSpectralInterval hκ u n :=
  Iff.rfl

/-- The geometric link missing from the r7 sixth conjunct is sol_multi's `collapsed_cell_measure_zero`
(`RootMassInvolutionR8`, read-only): no positive-density interval in the cell ⇒ the cell has zero physical measure. -/
theorem measure_cell_zero_of_collapsed (hκ : 0 < κ) (u : L2T L) (n : ℤ) (h : ¬ PosInterval hκ u n) :
    measure hκ u (cell hκ u n) = 0 :=
  QuantumNLS.RootMassInvolutionR8.collapsed_cell_measure_zero hκ u n h

/-- The indexed mass of a collapsed cell is zero. -/
theorem mass_zero_of_collapsed (hκ : 0 < κ) (u : L2T L) (n : ℤ) (h : ¬ PosInterval hκ u n) :
    (masses hκ u).1 n = 0 := by
  have hm : (masses hκ u).1 n = (measure hκ u (cell hκ u n)).toReal :=
    (QuantumNLS.RootIndexedMassesFull.root_indexed_masses hκ u).1 n
  rw [hm, measure_cell_zero_of_collapsed hκ u n h]
  simp

/-- For `u ≠ 0`: a positive-density interval inside the cell forces positive mass. -/
theorem mass_pos_of_posInterval (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (n : ℤ)
    (h : PosInterval hκ u n) : 0 < (masses hκ u).1 n := by
  obtain ⟨a, b, hab, hsub, hg⟩ := h
  have hm : (masses hκ u).1 n = (measure hκ u (cell hκ u n)).toReal :=
    (QuantumNLS.RootIndexedMassesFull.root_indexed_masses hκ u).1 n
  rw [hm]
  have hfin : measure hκ u (cell hκ u n) ≠ ⊤ := measure_ne_top _ _
  refine ENNReal.toReal_pos ?_ hfin
  intro hz
  have hJ : measure hκ u (Ioo a b) = 0 := measure_mono_null hsub hz
  rw [QuantumNLS.RootDensityIdentification.root_density hκ hu, withDensity_apply _ measurableSet_Ioo] at hJ
  have hmeas : Measurable fun x => ENNReal.ofReal (QuantumNLS.RootDensityIdentification.dens κ u x) :=
    ENNReal.measurable_ofReal.comp (QuantumNLS.RootDensityIdentification.continuous_dens κ u).measurable
  have hae := (lintegral_eq_zero_iff hmeas).1 (by simpa [Measure.restrict_apply] using hJ :
    ∫⁻ x in Ioo a b, ENNReal.ofReal (QuantumNLS.RootDensityIdentification.dens κ u x) = 0)
  have hall : ∀ᵐ x ∂volume, x ∈ Ioo a b → False := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo] at hae
    filter_upwards [hae] with x hx hxm
    have h0 := hx hxm
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h0
    have hpos : 0 < QuantumNLS.RootDensityIdentification.dens κ u x := by
      unfold QuantumNLS.RootDensityIdentification.dens
      have := hg x hxm
      have h2 : 0 < hfun |(QuantumNLS.L2SpatialTransfer.discriminant κ u (x : ℂ)).re| :=
        (QuantumNLS.RootDensity.hfun_pos_iff _).2 this
      exact mul_pos (inv_pos.2 (mul_pos Real.pi_pos hκ)) h2
    linarith
  have hv : volume (Ioo a b) = 0 := by
    have h1 := ae_iff.1 hall
    have e : {x : ℝ | ¬ (x ∈ Ioo a b → False)} = Ioo a b := by
      ext x; simp
    rwa [e] at h1
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hv
  linarith

theorem mass_zero_iff (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (n : ℤ) :
    (masses hκ u).1 n = 0 ↔ ¬ PosInterval hκ u n :=
  ⟨fun h hp => (mass_pos_of_posInterval hκ hu n hp).ne' h, mass_zero_of_collapsed hκ u n⟩

/-- **R-950BFB30, all printed clauses of `thm:root-indexed-masses`**, with the printed link
"vanishing spectral interval ⇒ zero mass" and the phase label, and no measure-zero hypothesis. -/
theorem root_indexed_masses_collapsed (hκ : 0 < κ) (u : L2T L) :
    (∀ n : ℤ, (masses hκ u).1 n =
      (measure hκ u (Ioo
        (QuantumNLS.RootIndexedPhase.separator hκ u (n-1)) (QuantumNLS.RootIndexedPhase.separator hκ u n))).toReal) ∧
    (∀ n : ℤ, 0 ≤ (masses hκ u).1 n) ∧
    Summable (fun n => (masses hκ u).1 n) ∧
    (∑' n, (masses hκ u).1 n) = ‖u‖^2 ∧
    Continuous (fun p : QuantumNLS.DEF014Phase.Param L => masses p.1.2 p.2) ∧
    (∀ n : ℤ, (¬ PosInterval hκ u n → (masses hκ u).1 n = 0) ∧
      (∀ a b : ℝ, a < b → Ioo a b ⊆ cell hκ u n → (∀ x ∈ Ioo a b, 2 < |Dre κ u x|) →
        ∀ x ∈ Ioo a b, QuantumNLS.RootIndexedPhase.theta hκ u x = n * Real.pi)) ∧
    (∀ c : ℂ, ‖c‖ = 1 → masses hκ (c • u) = masses hκ u) ∧
    (∀ a : ℝ, masses hκ (QuantumNLS.BornTranslation.trans a u) = masses hκ u) ∧
    Tendsto (fun k : QuantumNLS.RootMassFree.Coupling => masses k.2 u) QuantumNLS.RootMassFree.zeroCoupling
      (𝓝 (QuantumNLS.RootMassFreeLimit.intensities u)) ∧
    (∀ (a : ℂ) (k n : ℤ),
      (masses hκ (((Real.sqrt L : ℂ)*a) • QuantumNLS.Fourier.modeLp L k)).1 n =
        if n=k then L*‖a‖^2 else 0) ∧
    (∀ (k n : ℤ), (masses hκ (QuantumNLS.RootMassBoostSymbol.boost k u)).1 n = (masses hκ u).1 (n-k)) := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8, h9, h10, h11⟩ :=
    QuantumNLS.RootIndexedMassesFull.root_indexed_masses hκ u
  exact ⟨h1, h2, h3, h4, h5,
    fun n => ⟨mass_zero_of_collapsed hκ u n, fun a b hab hsub hg => phase_label hκ u n
      ⟨a, b, hab, hsub, hg⟩ a b hab hsub hg⟩, h7, h8, h9, h10, h11⟩

end QuantumNLS.RootIndexedMassesCollapsed

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RootIndexedMassesCollapsed.cell_phase
#print axioms QuantumNLS.RootIndexedMassesCollapsed.phase_label
#print axioms QuantumNLS.RootIndexedMassesCollapsed.mass_zero_of_collapsed
#print axioms QuantumNLS.RootIndexedMassesCollapsed.mass_zero_iff
#print axioms QuantumNLS.RootIndexedMassesCollapsed.root_indexed_masses_collapsed
