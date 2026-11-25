import NlsGge.Birkhoff.S05FreeEnergy38
import NlsGge.Birkhoff.S05FreeEnergy38b
import NlsGge.Birkhoff.W05ChargeSeries38
import NlsGge.Birkhoff.S04Moments38e

/-! # S05 (v2 `A:eq:infiniteenergy`, l.476-486), part 3: the full unrenormalized energy is almost
surely infinite

Source: `paper/v2.tex` l.476-486, blueprint `S05.05`-`S05.07`.  Conditional on `B : BirkhoffTop38`
(and only on its field `action`, through `I_n(Φ⁻¹ z) = |z_n|²`, plus the finite-gap/continuity
consequences already proved in S03); no `O` and no flow input.

Chain of the source proof:
* S05.05 (`S05FreeEnergy38b`): under `γ_W` the `a_n|z_n|²` are independent exponential variables of
  mean one and `∑_n a_n|z_n|² = ⊤` a.s. (strong law);
* S05.06 (`spectralEnergyW38_cleanΦinv_eq_top_ae38`): for `z ∈ Ω₀` the series of differences
  `∑ [G_n - a_n I_n]` of `A:eq:remainder` converges absolutely (S03) and `∑ a_n I_n = ∑ a_n|z_n|² = ⊤`,
  hence `∑_n G_n = ⊤` where `G_n = (2/π)∫_{g_n} W(2λ) v dλ`; no subtraction of infinite sums
  occurs, only `a_n |z_n|² ≤ G_n + |R_n|` with `∑|R_n| < ∞`;
* S05.07 (`W05ChargeSeries38.spectralEnergyW38_eq_chargeSeries`, Φ-free): monotone convergence in the
  nonnegative power series of `W` and the trace identities show that `∑_n G_n = E_W(u)` equals the
  charge series `∑_j c_j/(j!)^4 Q_{2j}(U)` for every smooth representative `U` of `u`;
* equivalence `μ̂_W ~ γ_W` and the push-forward `μ_W = (Φ⁻¹)_# μ̂_W` (S03) transfer the almost sure
  statement to `μ_W`.

The statement for `μ_W` is conditional on `B` only through `Rbar38`, `cleanΦinv`, `muW38`.
-/

set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core Filter Topology
open scoped ENNReal ContDiff

/-! ### The gap sum diverges when `∑ a_n|z_n|² = ⊤` and the remainder series converges -/

/-- Deterministic step (S05.06), without subtraction of infinite sums: if `A_n ≥ 0`, `G_n = A_n + R_n`
and `∑ |R_n| < ∞`, then `∑ A_n = ⊤` implies `∑ G_n = ⊤` in `[0,∞]`. -/
theorem tsum_ofReal_eq_top_of_add_summable38 (A G R : ℤ → ℝ)
    (hGR : ∀ n, G n = R n + A n) (hR : Summable R)
    (hAtop : ∑' n : ℤ, ENNReal.ofReal (A n) = ⊤) :
    ∑' n : ℤ, ENNReal.ofReal (G n) = ⊤ := by
  by_contra hG
  have hRabs : ∑' n : ℤ, ENNReal.ofReal (|R n|) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => abs_nonneg _) hR.abs]
    exact ENNReal.ofReal_ne_top
  have hle : ∀ n, ENNReal.ofReal (A n) ≤ ENNReal.ofReal (G n) + ENNReal.ofReal (|R n|) := by
    intro n
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    have := neg_abs_le (R n)
    have h2 := hGR n
    linarith
  have := (ENNReal.tsum_le_tsum hle).trans_eq (ENNReal.tsum_add)
  rw [hAtop] at this
  exact (ENNReal.add_ne_top.2 ⟨hG, hRabs⟩) (top_le_iff.1 this)

namespace BirkhoffTop38

variable (B : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
  (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

/-- The weight class of S03/S04 as `BoundedCoefficients lower upper`. -/
def boundedCoef38 : BoundedCoefficients lower upper :=
  ⟨c, hlower, (hbound 0).trans (hupper 0), fun j => ⟨hbound j, hupper j⟩⟩

omit hlower hbound hupper in
theorem boundedCoef38_val (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) :
    (boundedCoef38 lower upper c hlower hbound hupper).val = c := rfl

/-- **S05.06 (Birkhoff variables).** For `γ_W`-almost every `z`, the spectral energy
`E_W(Φ⁻¹ z) = (2/π)∫ W(2λ) v(λ; Φ⁻¹ z) dλ ∈ [0,∞]` is `+∞`; equivalently the nonnegative gap
contributions `∑_n (2/π)∫_{g_n} W(2λ) v dλ` have infinite sum. -/
theorem gapSum_cleanΦinv_eq_top_ae38 :
    ∀ᵐ z ∂(fullWeightSequenceGaussian c),
      ∑' n : ℤ, ENNReal.ofReal (gapIntegral38 c (B.cleanΦinv z) n) = ⊤ := by
  filter_upwards [ae_mem_Omega038 lower upper c hlower hbound hupper,
    tsum_fullWeight_sqNorm_eq_top_ae38 lower upper c hlower hbound hupper] with z hz hinf
  have hz1 : z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := mem_seqSobolev38_of_Omega038 c hz 1
  obtain ⟨hsum, -⟩ := B.remainder_tendsto_pathwise38 lower upper c hlower hbound hupper z hz
    isExhaustion_stdExh38
  refine tsum_ofReal_eq_top_of_add_summable38 (fun n => fullWeightRate c n * ‖z n‖ ^ 2)
    (fun n => gapIntegral38 c (B.cleanΦinv z) n)
    (fun n => remainderSummand38 c (B.cleanΦinv z) n)
    (fun n => ?_) hsum hinf
  unfold remainderSummand38
  rw [B.action_cleanΦinv38 z hz1 n]
  ring

/-- **S05.06 + S05.07 for the spectral energy.** For `γ_W`-almost every `z`,
`spectralEnergyW38 c (Φ⁻¹ z) = +∞`. -/
theorem spectralEnergyW38_cleanΦinv_eq_top_ae38 :
    ∀ᵐ z ∂(fullWeightSequenceGaussian c),
      spectralEnergyW38 c (B.cleanΦinv z) = ⊤ := by
  filter_upwards [B.gapSum_cleanΦinv_eq_top_ae38 lower upper c hlower hbound hupper] with z hz
  exact (spectralEnergyW_eq_tsum38 (boundedCoef38 lower upper c hlower hbound hupper) _).trans hz

omit hlower hbound hupper in
/-- The gap integral is read on the `h¹` carrier through `physH38 1`. -/
theorem gapFn38_physH38 (c : ℕ → ℝ) (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    gapFn38 c n (physH38 1 u) = gapIntegral38 c u n := by
  have hm : fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    (fourierSeq38_mem_iff _ u).2 (by simpa using hu)
  rw [physH38_of_mem 1 u hm, gapIntegral38_eq_gapFn38 c u hu n]

end BirkhoffTop38

/-- The set of fields whose gap sum (read on `h¹`) is infinite. -/
def gapSumTop38 (c : ℕ → ℝ) : Set PhysicalL2 :=
  {u | ∑' n : ℤ, ENNReal.ofReal (gapFn38 c n (physH38 1 u)) = ⊤}

theorem measurableSet_gapSumTop38 (c : ℕ → ℝ) (hW : Continuous (weight c)) :
    MeasurableSet (gapSumTop38 c) := by
  let _ : MeasurableSpace (SobolevCarrier38 ((1 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 ((1 : ℕ) : ℝ)) := ⟨rfl⟩
  have hm : Measurable (fun u : PhysicalL2 => ∑' n : ℤ, ENNReal.ofReal (gapFn38 c n (physH38 1 u))) :=
    Measurable.tsum (fun n =>
      ((continuous_gapFn38 c hW n).measurable.comp (measurable_physH38 1)).ennreal_ofReal)
  exact hm (measurableSet_singleton ⊤)

namespace BirkhoffTop38

variable (B : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
  (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

/-- **S05.06, transfer to `μ_W`.** `μ_W`-almost every `u` has infinite gap sum
`∑_n (2/π)∫_{g_n(u)} W(2λ) v(λ;u) dλ = ⊤`, and lies in `H¹`. -/
theorem ae_muW38_gapSum_eq_top :
    ∀ᵐ u : PhysicalL2 ∂(B.muW38 c), SobolevSquareSummable 1 (physicalFourier u) ∧
      ∑' n : ℤ, ENNReal.ofReal (gapIntegral38 c u n) = ⊤ := by
  have hW := weight_continuous38 hlower hbound hupper
  have hA : ∀ᵐ u : PhysicalL2 ∂(B.muW38 c), u ∈ gapSumTop38 c :=
    (ae_map_iff B.measurable_cleanΦinv.aemeasurable (measurableSet_gapSumTop38 c hW)).2 (by
      have h1 := (B.muHatW38_equivalent lower upper c hlower hbound hupper).1.ae_le
        (B.gapSum_cleanΦinv_eq_top_ae38 lower upper c hlower hbound hupper)
      have h2 := (B.muHatW38_equivalent lower upper c hlower hbound hupper).1.ae_le
        (ae_mem_Omega038 lower upper c hlower hbound hupper)
      filter_upwards [h1, h2] with z hz hzΩ
      have hz1 : z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := mem_seqSobolev38_of_Omega038 c hzΩ 1
      have hs : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv z)) := by
        simpa using B.sobolev_cleanΦinv38 1 z hz1
      show ∑' n : ℤ, ENNReal.ofReal (gapFn38 c n (physH38 1 (B.cleanΦinv z))) = ⊤
      simp_rw [gapFn38_physH38 c _ hs]
      exact hz)
  filter_upwards [hA, B.ae_muW38_allSobolev lower upper c hlower hbound hupper] with u hu hall
  have hs : SobolevSquareSummable 1 (physicalFourier u) := by simpa using hall 1
  refine ⟨hs, ?_⟩
  have : ∑' n : ℤ, ENNReal.ofReal (gapFn38 c n (physH38 1 u)) = ⊤ := hu
  simp_rw [gapFn38_physH38 c u hs] at this
  exact this

/-- **S05.06 + S05.07 for the spectral energy, under `μ_W`.** `μ_W`-a.e. `u` has
`E_W(u) = (2/π)∫ W(2λ) v(λ;u) dλ = +∞`. -/
theorem ae_muW38_spectralEnergy_eq_top :
    ∀ᵐ u : PhysicalL2 ∂(B.muW38 c), spectralEnergyW38 c u = ⊤ := by
  filter_upwards [B.ae_muW38_gapSum_eq_top lower upper c hlower hbound hupper] with u hu
  exact (spectralEnergyW_eq_tsum38 (boundedCoef38 lower upper c hlower hbound hupper) _).trans hu.2

/-- **S05.07.** For `μ_W`-almost every `u`: `u` has a smooth period-one representative `U`, and for
every such representative the full unrenormalized local-charge energy
`∑_j c_j/(j!)^4 Q_{2j}(U)` (nonnegative terms) diverges: its extended sum is `+∞`, it is not
summable, and its partial sums tend to `+∞` (v2 `A:eq:infiniteenergy`). -/
theorem S05_infiniteEnergy_38 :
    ∀ᵐ u : PhysicalL2 ∂(B.muW38 c),
      (∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        smoothL2_38 U hU hper = u) ∧
      ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        smoothL2_38 U hU hper = u →
        (∀ j : ℕ, 0 ≤ NlsGge.coefficient c j * localCharge38 U j) ∧
        spectralEnergyW38 c u = ⊤ ∧
        chargeSeriesW38 c U = ⊤ ∧
        ¬ Summable (fun j : ℕ => NlsGge.coefficient c j * localCharge38 U j) ∧
        Tendsto (fun J : ℕ => ∑ j ∈ Finset.range J, NlsGge.coefficient c j * localCharge38 U j)
          atTop atTop := by
  filter_upwards [B.ae_muW38_spectralEnergy_eq_top lower upper c hlower hbound hupper,
    B.ae_muW38_smooth lower upper c hlower hbound hupper] with u hE hsm
  refine ⟨hsm, fun U hU hper hUu => ?_⟩
  set cc := boundedCoef38 lower upper c hlower hbound hupper with hcc
  have hcoef : ∀ j, 0 ≤ NlsGge.coefficient c j := fun j =>
    div_nonneg (hlower.le.trans (hbound j)) (by positivity)
  have hnn : ∀ j : ℕ, 0 ≤ NlsGge.coefficient c j * localCharge38 U j := by
    intro j
    have hu1 : SobolevSquareSummable 1 (physicalFourier (smoothL2_38 U hU hper)) :=
      smoothL2_38_sobolev U hU hper
    have h := (actualTraceFormula_E02_38 _ hu1 U hU hper (smoothL2_38_cover_ae U hU hper) j).2
    have hch : localCharge38 U j =
        (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 (smoothL2_38 U hU hper) t :=
      h
    refine mul_nonneg (hcoef j) ?_
    rw [hch]
    refine mul_nonneg (by positivity) (integral_nonneg (fun t => ?_))
    exact mul_nonneg (Even.pow_nonneg (even_two_mul j) _)
      (actualGapHeightE02_38_nonneg _ t)
  have hser : chargeSeriesW38 c U = ⊤ := by
    have e := spectralEnergyW38_eq_chargeSeries cc U hU hper
    rw [hUu] at e
    exact e.symm.trans hE
  have hns : ¬ Summable (fun j : ℕ => NlsGge.coefficient c j * localCharge38 U j) := by
    intro hs
    have := ENNReal.ofReal_tsum_of_nonneg hnn hs
    have h2 : chargeSeriesW38 c U = ENNReal.ofReal (∑' j : ℕ, NlsGge.coefficient c j * localCharge38 U j) :=
      this.symm
    rw [hser] at h2
    exact ENNReal.ofReal_ne_top h2.symm
  exact ⟨hnn, hE, hser, hns,
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).1 hns⟩

end BirkhoffTop38

end NlsGge.Birkhoff
