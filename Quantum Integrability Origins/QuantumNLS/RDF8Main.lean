import Mathlib
import QuantumNLS.RDF8Ibp
import QuantumNLS.RootH1Positive
import QuantumNLS.RootH1Ratio
import QuantumNLS.RootWeightedMassesR26
import QuantumNLS.RootEnergyMoment
import QuantumNLS.RootIndexedMassesCollapsed
import QuantumNLS.PhysicalL2Normalization

/-!
# R-DF8F25DD `thm:root-H1-characterization` (ROOT_H1_characterization.tex:9-36, proof :206-236)

"Let `κ, L > 0` and `u ∈ L²(𝕋_L)`. The following conditions are equivalent:
(1) `u ∈ H¹(𝕋_L)`; (2) `∫ t² dM_{κ,u}(t) < ∞`; (3) `Σₙ (2πn/L)² Iₙ^{(κ)}(u) < ∞`.
When they hold, the exact energy and weighted identities (eq:root-energy-identity) and
(eq:root-energy-actions) apply. In particular, writing `m = ‖u‖₂²`,
`m + ‖∂ₓu‖₂² ≤ m + Σₙ (2πn/L)² Iₙ + 2κm²/L`; for the Fourier norm of DEF-002,
`‖u‖²_{H¹} ≤ 2(m + ‖∂ₓu‖₂²) ≤ 2m + 2Σₙ(2πn/L)² Iₙ + 4κm²/L`.
For every nonzero `L²` input, all indexed mass lies at one index `k` iff `u(x) = a e^{2πikx/L}`
a.e. for some nonzero complex constant `a`."

Vocabulary (accepted, read-only): `H¹` is `ProductEnergyPreparation.OneH1` (Fourier `h¹`),
`∂ₓu` is `RootWeightedPhysicalR26.weakDerivative`, `M_{κ,u}` is `FullMass.Mmeas`, `Iₙ` is
`(RootIndexedMasses.masses hκ u).1 n`, `2πn/L` is `RootWeightedCellsR26.momentum L n`,
`D(u)` is `RootWeightedCellsR26.displacement`, the energy `‖u'‖² + κ‖u‖₄⁴` is
`ChargeEnergy.energyH1`, the DEF-002 squared norm is `Fourier.hsNormSq L 1` of the coefficients.

Route (source proof): (2) ⇒ (1) by the ratio `r` of R-D24009D4 and the positive identity of
R-F36DAC7F: for every finite index set the weighted coefficient squares of `Yr` are bounded by
`(1+δ_Y)² ∫ Y²t²/(Y²+t²) dM ≤ (1+δ_Y)² ∫ t² dM`, and pass to the limit `Yr → u`, `δ_Y → 0`
(stage `RDF8Ibp`); (1) ⇒ (2) by R-484B3F6D; (2) ⇔ (3) and the identities by R-A8F7B7B0; the
single-index assertion by the new equivalence, R-A8F7B7B0, and the plane-wave normalization of
R-950BFB30.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Fourier QuantumNLS.RootH1RatioConvergence

namespace QuantumNLS.RDF8Main
open QuantumNLS.ProductEnergyPreparation (OneH1)

variable {L : ℝ} [hLf : Fact (0 < L)]

lemma coeff_smul (c : ℂ) (f : L2T L) (n : ℤ) : fourierL2 L (c • f) n = c * fourierL2 L f n := by
  rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

lemma continuous_coeff (n : ℤ) : Continuous (fun f : L2T L => fourierL2 L f n) := by
  have hlip : LipschitzWith 1 (fun a : lp (fun _ : ℤ => ℂ) 2 => a n) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (a - b) n
    simpa using h
  exact hlip.continuous.comp (fourierL2 L).continuous

/-- **(2) ⇒ weighted coefficient bound**: every finite weighted coefficient sum is at most the
spectral second moment. -/
theorem coeff_bound {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0)
    (hI : Integrable (fun t : ℝ => t ^ 2) (FullMass.Mmeas κ u)) (F : Finset ℤ) :
    ∑ n ∈ F, freq L n ^ 2 * ‖fourierL2 L u n‖ ^ 2 ≤ ∫ t, t ^ 2 ∂(FullMass.Mmeas κ u) := by
  set I : ℝ := ∫ t, t ^ 2 ∂(FullMass.Mmeas κ u) with hIdef
  obtain ⟨hpos, hδ⟩ := RootH1Positive.root_H1_positive hκ u hu
  have hconv := (RootH1Ratio.root_H1_ratio hκ u hu).2
  set S : ℝ → ℝ := fun Y =>
    ∑ n ∈ F, freq L n ^ 2 * ‖fourierL2 L ((Y : ℂ) • ratioAt hκ.le u Y) n‖ ^ 2 with hSdef
  have hS : Tendsto S atTop (𝓝 (∑ n ∈ F, freq L n ^ 2 * ‖fourierL2 L u n‖ ^ 2)) := by
    apply tendsto_finset_sum
    intro n _
    exact ((((continuous_coeff n).tendsto u).comp hconv).norm.pow 2).const_mul _
  have hR : Tendsto (fun Y : ℝ => (1 + κ * ‖ratioInfAt hκ.le u Y‖ ^ 2) ^ 2 * I) atTop
      (𝓝 ((1 + 0) ^ 2 * I)) :=
    ((tendsto_const_nhds.add hδ).pow 2).mul_const I
  rw [show ((1 : ℝ) + 0) ^ 2 * I = I by ring] at hR
  refine le_of_tendsto_of_tendsto hS hR ?_
  filter_upwards [eventually_ge_atTop (max (threshold κ u) 1)] with Y hY
  have hYt : threshold κ u ≤ Y := le_trans (le_max_left _ _) hY
  have hY1 : 1 ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : 0 < Y := by linarith
  obtain ⟨g, d, hrep, hper, _, hrest⟩ := hpos Y hYt
  obtain ⟨_, _, hctrl⟩ := hrest
  have hw := RDF8Ibp.weighted_le hrep hper F
  have hSY : S Y = Y ^ 2 * ∑ n ∈ F, freq L n ^ 2 * ‖fourierL2 L (ratioAt hκ.le u Y) n‖ ^ 2 := by
    simp only [hSdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [coeff_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hint : (∫ t in (0 : ℝ)..L, ‖(Y : ℂ) * d t‖ ^ 2) = Y ^ 2 * ∫ t in (0 : ℝ)..L, ‖d t‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hbd : ∀ t : ℝ, Y ^ 2 * t ^ 2 / (Y ^ 2 + t ^ 2) ≤ t ^ 2 := by
    intro t
    have hp : 0 < Y ^ 2 + t ^ 2 := by positivity
    rw [div_le_iff₀ hp]
    nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]
  have hint1 : Integrable (fun t : ℝ => Y ^ 2 * t ^ 2 / (Y ^ 2 + t ^ 2)) (FullMass.Mmeas κ u) := by
    refine hI.mono' ?_ (Eventually.of_forall fun t => ?_)
    · exact (Continuous.div (by continuity) (by continuity)
        (fun t => by positivity)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbd t
  have hmono : (∫ t, Y ^ 2 * t ^ 2 / (Y ^ 2 + t ^ 2) ∂(FullMass.Mmeas κ u)) ≤ I :=
    integral_mono hint1 hI hbd
  calc S Y = Y ^ 2 * ∑ n ∈ F, freq L n ^ 2 * ‖fourierL2 L (ratioAt hκ.le u Y) n‖ ^ 2 := hSY
    _ ≤ Y ^ 2 * ∫ t in (0 : ℝ)..L, ‖d t‖ ^ 2 := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
    _ = ∫ t in (0 : ℝ)..L, ‖(Y : ℂ) * d t‖ ^ 2 := hint.symm
    _ ≤ (1 + κ * ‖ratioInfAt hκ.le u Y‖ ^ 2) ^ 2 *
          (∫ t, Y ^ 2 * t ^ 2 / (Y ^ 2 + t ^ 2) ∂(FullMass.Mmeas κ u)) := hctrl
    _ ≤ (1 + κ * ‖ratioInfAt hκ.le u Y‖ ^ 2) ^ 2 * I :=
          mul_le_mul_of_nonneg_left hmono (sq_nonneg _)

/-- **(2) ⇒ (1).** -/
theorem oneH1_of_moment {κ : ℝ} (hκ : 0 < κ) (u : L2T L)
    (hI : Integrable (fun t : ℝ => t ^ 2) (FullMass.Mmeas κ u)) : OneH1 u := by
  by_cases hu : u = 0
  · subst hu
    unfold OneH1 Mem04
    simp
  have hsum : Summable (fun n : ℤ => freq L n ^ 2 * ‖fourierL2 L u n‖ ^ 2) :=
    summable_of_sum_le (fun n => by positivity) (coeff_bound hκ u hu hI)
  have h0 : Summable (fun n : ℤ => ‖fourierL2 L u n‖ ^ 2) :=
    QuantumNLS.Energy.summable_sq (fourierL2 L u)
  unfold OneH1 Mem04
  refine (h0.add hsum).congr fun n => ?_
  rw [f04Weight_one]
  ring

/-- `‖u'‖² = Σ pₙ² |ûₙ|²`. -/
lemma norm_deriv_sq (u : L2T L) (hH : OneH1 u) :
    ‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2 =
      ∑' n : ℤ, freq L n ^ 2 * ‖fourierL2 L u n‖ ^ 2 := by
  rw [← norm_fourierL2, QuantumNLS.Energy.norm_sq_eq_tsum]
  congr 1
  funext n
  rw [RootWeightedPhysicalR26.derivative_coeff, WeakDerivatives.norm_ikn_mul_sq]

lemma norm_sq_coeff (u : L2T L) : ‖u‖ ^ 2 = ∑' n : ℤ, ‖fourierL2 L u n‖ ^ 2 := by
  rw [← norm_fourierL2, QuantumNLS.Energy.norm_sq_eq_tsum]

/-- DEF-002 norm versus `m + ‖u'‖²`, from `(1+|p|)² ≤ 2(1+p²)`. -/
theorem hsNorm_le (u : L2T L) (hH : OneH1 u) :
    hsNormSq L 1 (fun n => fourierL2 L u n) ≤
      2 * (‖u‖ ^ 2 + ‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2) := by
  have h0 : Summable (fun n : ℤ => ‖fourierL2 L u n‖ ^ 2) :=
    QuantumNLS.Energy.summable_sq (fourierL2 L u)
  have hH' : Summable (fun n : ℤ => (1 + freq L n ^ 2) * ‖fourierL2 L u n‖ ^ 2) := by
    have := hH
    unfold OneH1 Mem04 at this
    simpa only [f04Weight_one] using this
  have hp : Summable (fun n : ℤ => freq L n ^ 2 * ‖fourierL2 L u n‖ ^ 2) :=
    (hH'.sub h0).congr fun n => by ring
  have hw : ∀ n : ℤ, sobolevWeight L 1 n * ‖fourierL2 L u n‖ ^ 2 ≤
      2 * ((1 + freq L n ^ 2) * ‖fourierL2 L u n‖ ^ 2) := by
    intro n
    have he : sobolevWeight L 1 n = (1 + |freq L n|) ^ 2 := by
      unfold sobolevWeight freq
      rw [show (2 : ℝ) * 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [he]
    have hq : (1 + |freq L n|) ^ 2 ≤ 2 * (1 + freq L n ^ 2) := by
      nlinarith [sq_nonneg (|freq L n| - 1), sq_abs (freq L n)]
    nlinarith [sq_nonneg ‖fourierL2 L u n‖]
  have hls : Summable (fun n : ℤ => sobolevWeight L 1 n * ‖fourierL2 L u n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (sobolevWeight_pos L 1 n).le (sq_nonneg _)) hw
      (hH'.mul_left 2)
  unfold hsNormSq
  calc (∑' n : ℤ, sobolevWeight L 1 n * ‖fourierL2 L u n‖ ^ 2)
      ≤ ∑' n : ℤ, 2 * ((1 + freq L n ^ 2) * ‖fourierL2 L u n‖ ^ 2) :=
        Summable.tsum_le_tsum hw hls (hH'.mul_left 2)
    _ = 2 * ((∑' n : ℤ, ‖fourierL2 L u n‖ ^ 2) + ∑' n : ℤ, freq L n ^ 2 * ‖fourierL2 L u n‖ ^ 2) := by
        rw [tsum_mul_left, ← h0.tsum_add hp]
        congr 2
        funext n
        ring
    _ = 2 * (‖u‖ ^ 2 + ‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2) := by
        rw [norm_sq_coeff, norm_deriv_sq]

/-- A plane wave `a e^{2πikx/L}` is the vector `(√L a) eₖ`. -/
lemma plane_eq {u : L2T L} {a : ℂ} {k : ℤ}
    (h : (u : AddCircle L → ℂ) =ᵐ[volume] fun x => a * _root_.fourier k x) :
    u = (((Real.sqrt L : ℝ) : ℂ) * a) • modeLp L k := by
  have hs : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hLf.out).ne'
  apply Lp.ext
  filter_upwards [h, Lp.coeFn_smul (((Real.sqrt L : ℝ) : ℂ) * a) (modeLp L k), coeFn_modeLp L k]
    with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, mode, smul_eq_mul]
  push_cast
  field_simp

/-- **R-DF8F25DD `thm:root-H1-characterization`.** -/
theorem root_H1_characterization {κ : ℝ} (hκ : 0 < κ) (u : L2T L) :
    (OneH1 u ↔ Integrable (fun t : ℝ => t ^ 2) (FullMass.Mmeas κ u)) ∧
    (Integrable (fun t : ℝ => t ^ 2) (FullMass.Mmeas κ u) ↔
      Summable (fun n : ℤ =>
        RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n)) ∧
    (∀ hH : OneH1 u,
      ((∫ t : ℝ, t ^ 2 ∂FullMass.Mmeas κ u) = ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ)) ∧
      Summable (fun n : ℤ =>
        |RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n|) ∧
      (‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2 +
          κ * ChargeEnergy.quartic (u : AddCircle L → ℂ) =
        (∑' n : ℤ, RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n) +
          2 * κ * ‖u‖ ^ 4 / L - RootWeightedCellsR26.displacement hκ u) ∧
      (‖u‖ ^ 2 + ‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2 ≤
        ‖u‖ ^ 2 +
          (∑' n : ℤ, RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n) +
          2 * κ * (‖u‖ ^ 2) ^ 2 / L) ∧
      (hsNormSq L 1 (fun n => fourierL2 L u n) ≤
        2 * (‖u‖ ^ 2 + ‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2)) ∧
      (2 * (‖u‖ ^ 2 + ‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2) ≤
        2 * ‖u‖ ^ 2 +
          2 * (∑' n : ℤ, RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n) +
          4 * κ * (‖u‖ ^ 2) ^ 2 / L)) ∧
    (u ≠ 0 → ∀ k : ℤ,
      (∀ n : ℤ, n ≠ k → (RootIndexedMasses.masses hκ u).1 n = 0) ↔
        ∃ a : ℂ, a ≠ 0 ∧ (u : AddCircle L → ℂ) =ᵐ[volume] fun x => a * _root_.fourier k x) := by
  obtain ⟨_, hD0, _, hiff, hH1⟩ := RootWeightedMassesR26.root_weighted_masses hκ u
  have hmeas := PhysicalL2Normalization.measure_eq_Mmeas hκ u
  rw [hmeas] at hiff
  have iff1 : OneH1 u ↔ Integrable (fun t : ℝ => t ^ 2) (FullMass.Mmeas κ u) :=
    ⟨fun hH => (RootEnergyMoment.root_energy_moment hκ u hH).1, oneH1_of_moment hκ u⟩
  have hcol := RootIndexedMassesCollapsed.root_indexed_masses_collapsed hκ u
  refine ⟨iff1, hiff, fun hH => ?_, fun hu k => ?_⟩
  · obtain ⟨_, hs2, _, hen, _, _, _⟩ := hH1 hH
    have hq : 0 ≤ κ * ChargeEnergy.quartic (u : AddCircle L → ℂ) :=
      mul_nonneg hκ.le (integral_nonneg fun x => by positivity)
    have hb : ‖u‖ ^ 2 + ‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2 ≤
        ‖u‖ ^ 2 +
          (∑' n : ℤ, RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n) +
          2 * κ * (‖u‖ ^ 2) ^ 2 / L := by
      have e4 : (‖u‖ ^ 2) ^ 2 = ‖u‖ ^ 4 := by ring
      rw [e4]
      linarith
    exact ⟨(RootEnergyMoment.root_energy_moment hκ u hH).2.1, hs2, hen, hb, hsNorm_le u hH,
      le_of_le_of_eq (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)) (by ring)⟩
  · constructor
    · intro hconc
      have hsum : Summable (fun n : ℤ =>
          RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n) := by
        apply summable_of_ne_finset_zero (s := {k})
        intro n hn
        rw [Finset.mem_singleton] at hn
        rw [hconc n hn, mul_zero]
      have hH : OneH1 u := iff1.2 (hiff.2 hsum)
      obtain ⟨_, _, _, _, _, _, hplane⟩ := hH1 hH
      have htot : (∑' n : ℤ, (RootIndexedMasses.masses hκ u).1 n) = ‖u‖ ^ 2 := hcol.2.2.2.1
      rw [tsum_eq_single k (fun n hn => hconc n hn)] at htot
      have hif : ∀ n : ℤ, (RootIndexedMasses.masses hκ u).1 n = if n = k then ‖u‖ ^ 2 else 0 := by
        intro n
        by_cases hn : n = k
        · subst hn; rw [if_pos rfl, htot]
        · rw [if_neg hn, hconc n hn]
      obtain ⟨a, ha⟩ := (hplane hu k).1 hif
      refine ⟨a, ?_, ha⟩
      rintro rfl
      apply hu
      apply Lp.ext
      filter_upwards [ha, Lp.coeFn_zero ℂ 2 (volume : Measure (AddCircle L))] with x h1 h2
      rw [h1, h2, zero_mul]
      rfl
    · rintro ⟨a, _, ha⟩ n hn
      have he := plane_eq ha
      have hp := hcol.2.2.2.2.2.2.2.2.2.1 a k n
      rw [← he, if_neg hn] at hp
      exact hp

end QuantumNLS.RDF8Main

#print axioms QuantumNLS.RDF8Main.coeff_bound
#print axioms QuantumNLS.RDF8Main.oneH1_of_moment
#print axioms QuantumNLS.RDF8Main.root_H1_characterization
