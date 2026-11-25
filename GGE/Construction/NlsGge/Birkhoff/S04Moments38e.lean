import NlsGge.Birkhoff.S04Moments38b
import NlsGge.Birkhoff.S04Moments38d
import NlsGge.Birkhoff.S01Equivariance38b

/-! # S04: smooth representatives and identification of the charge functional

For `μ_W`-a.e. field `u` (which lies in every `H^m`, `S04Moments38b`) there is a `C^∞` period-one
function `U` with `smoothL2_38 U = u` (`exists_smooth_rep38`, from `S01Equivariance38b`), and on it
the charge functional `chargeFn38 m j` equals the local charge `∫₀¹ (-1)^{j+1} U p_{2j+1}` and the
spectral charge `(2/π)∫ (2t)^{2j} v(t;u) dt`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38 Filter Topology
  NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
open scoped ENNReal BoundedContinuousFunction ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- **v2 `A:eq:localidentification`** for a smooth field `u = smoothL2 U` with finitely many open
gaps (monotone convergence and the trace formula `A:eq:trace`):
`𝓔_W(u) = ∑_j c_j/(j!)^4 Q_{2j}(u)`, the series being summable (`Q_{2j}` the local charge of the
smooth representative `U`). -/
theorem energyW38_eq_charge_series (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (U : ℝ → ℂ)
    (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (hfin : {n : ℤ | actualGapLowerAllE02_38 (smoothL2_38 U hU hper) n <
      actualGapUpperAllE02_38 (smoothL2_38 U hU hper) n}.Finite) :
    Summable (fun j : ℕ => NlsGge.coefficient c j * localCharge38 U j) ∧
    energyW38 c (smoothL2_38 U hU hper) = ∑' j : ℕ, NlsGge.coefficient c j * localCharge38 U j := by
  set u := smoothL2_38 U hU hper with hu
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := smoothL2_38_sobolev U hU hper
  have hae := smoothL2_38_cover_ae U hU hper
  have htr := fun j => actualTraceFormula_E02_38 u hu1 U hU hper hae j
  have hv0 := actualGapHeightE02_38_nonneg u
  have hcoef : ∀ j, 0 ≤ NlsGge.coefficient c j := fun j =>
    div_nonneg ((hlower.le.trans (hbound j))) (by positivity)
  set F : ℕ → ℝ → ℝ := fun j t => NlsGge.coefficient c j * ((2 * t) ^ (2 * j) * actualGapHeightE02_38 u t)
    with hF
  have hF0 : ∀ j t, 0 ≤ F j t := fun j t =>
    mul_nonneg (hcoef j) (mul_nonneg (by rw [pow_mul]; positivity) (hv0 t))
  have hFint : ∀ j, Integrable (F j) := fun j => (htr j).1.const_mul _
  have hIj : ∀ j, ∫ t, F j t = (Real.pi / 2) * (NlsGge.coefficient c j * localCharge38 U j) := by
    intro j
    simp only [hF]
    rw [integral_const_mul]
    have h := (htr j).2
    have : localCharge38 U j = (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t := h
    rw [this]
    field_simp
  have hW := weight_continuous38 hlower hbound hupper
  have hpt : ∀ t, HasSum (fun j => F j t) (weight c (2 * t) * actualGapHeightE02_38 u t) := by
    intro t
    have hs := (weightTerm_summable lower upper c hlower hbound hupper (2 * t)).hasSum
    have := hs.mul_right (actualGapHeightE02_38 u t)
    have e : (fun j => F j t) = fun j => weightTerm c (2 * t) j * actualGapHeightE02_38 u t := by
      funext j
      simp only [hF, NlsGge.weightTerm]
      ring
    rw [e]
    exact this
  have hf : Integrable (fun t : ℝ => weight c (2 * t) * actualGapHeightE02_38 u t) :=
    integrable_energyIntegrand38 c hW u hfin
  have hf0 : ∀ t, 0 ≤ weight c (2 * t) * actualGapHeightE02_38 u t := fun t =>
    (hpt t).nonneg (fun j => hF0 j t)
  -- monotone convergence in the extended reals
  have hL : ∫⁻ t, ENNReal.ofReal (weight c (2 * t) * actualGapHeightE02_38 u t) =
      ∑' j, ∫⁻ t, ENNReal.ofReal (F j t) := by
    rw [← lintegral_tsum (fun j => (hFint j).1.aemeasurable.ennreal_ofReal)]
    refine lintegral_congr (fun t => ?_)
    rw [← (hpt t).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => hF0 j t) (hpt t).summable]
  have hLfin : ∫⁻ t, ENNReal.ofReal (weight c (2 * t) * actualGapHeightE02_38 u t) ≠ ⊤ :=
    (hf.lintegral_lt_top).ne
  have hIe : ∀ j, ∫⁻ t, ENNReal.ofReal (F j t) = ENNReal.ofReal (∫ t, F j t) := fun j =>
    (ofReal_integral_eq_lintegral_ofReal (hFint j) (Filter.Eventually.of_forall (hF0 j))).symm
  have hI0 : ∀ j, 0 ≤ ∫ t, F j t := fun j => integral_nonneg (hF0 j)
  have hL' : ∫⁻ t, ENNReal.ofReal (weight c (2 * t) * actualGapHeightE02_38 u t) =
      ∑' j, ENNReal.ofReal (∫ t, F j t) := hL.trans (tsum_congr hIe)
  have hsumI : Summable (fun j => ∫ t, F j t) := by
    have h1 : ∑' j, ENNReal.ofReal (∫ t, F j t) ≠ ⊤ := hL' ▸ hLfin
    refine (ENNReal.summable_toReal h1).congr (fun j => ?_)
    exact ENNReal.toReal_ofReal (hI0 j)
  have hval : ∫ t, weight c (2 * t) * actualGapHeightE02_38 u t = ∑' j, ∫ t, F j t := by
    have h2 := ENNReal.ofReal_tsum_of_nonneg hI0 hsumI
    rw [← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0)] at hL'
    have h3 : (0 : ℝ) ≤ ∑' j, ∫ t, F j t := tsum_nonneg hI0
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hf0) h3).1 (hL'.trans h2.symm)
  have hQ : ∀ j, NlsGge.coefficient c j * localCharge38 U j = (2 / Real.pi) * ∫ t, F j t := by
    intro j; rw [hIj j]; field_simp
  refine ⟨?_, ?_⟩
  · simp_rw [hQ]; exact hsumI.mul_left _
  · simp_rw [hQ]
    rw [tsum_mul_left, ← hval]
    rfl

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

section Smooth

variable (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
  (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

/-- **S04.05 (smooth support).** `μ_W`-a.e. field has a `C^∞` period-one representative. -/
theorem ae_muW38_smooth :
    ∀ᵐ u : PhysicalL2 ∂(B.muW38 c), ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
      (hper : Function.Periodic U 1), smoothL2_38 U hU hper = u := by
  filter_upwards [B.ae_muW38_allSobolev lower upper c hlower hbound hupper] with u hu
  exact exists_smooth_rep38 u hu

/-- **S04.06 (identification of the charge functional).** `μ_W`-a.e. field `u` has a smooth
representative `U` with `smoothL2_38 U = u`, and for `2 ≤ m`, `j ≤ m`:
`chargeFn38 m j u = Q_{2j}^{loc}(U)` (local charge) `= (2/π) ∫ (2t)^{2j} v(t;u) dt` (spectral). -/
theorem ae_muW38_chargeFn_eq (m j : ℕ) (hm : 2 ≤ m) (hjm : j ≤ m) :
    ∀ᵐ u : PhysicalL2 ∂(B.muW38 c), ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
      (hper : Function.Periodic U 1), smoothL2_38 U hU hper = u ∧
      chargeFn38 m j u = localCharge38 U j ∧
      chargeFn38 m j u = (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t := by
  filter_upwards [B.ae_muW38_allSobolev lower upper c hlower hbound hupper] with u hu
  obtain ⟨U, hU, hper, hUu⟩ := exists_smooth_rep38 u hu
  have hmem : (fun n => physicalFourier u n) ∈ seqSobolev38 (((m - 1 : ℕ) : ℝ)) :=
    (mem_seqSobolev38_iff _ _).2 (hu (m - 1))
  set x : SobolevHilbert ((m - 1 : ℕ) : ℝ) := ofCarrier38 ((m - 1 : ℕ) : ℝ) (physC38 (m - 1) u)
    with hx
  have hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper)) n := by
    intro n
    have e : (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper) : PhysicalL2) = u :=
      hUu
    rw [e]
    have : x = carrierMk38 ((m - 1 : ℕ) : ℝ) _ hmem := by
      rw [hx]; exact physC38_of_mem (m - 1) u hmem
    rw [this]
    rfl
  have h1 := chargeSobolev38_smooth m j hm hjm U hU hper x hsource
  have h2 := chargeSobolev38_smooth_spectral m j hm hjm U hU hper x hsource
  refine ⟨U, hU, hper, hUu, h1, ?_⟩
  rw [show chargeFn38 m j u = chargeSobolev38 m j x from rfl, h2]
  unfold spectralCharge38
  rw [hUu]

/-- **v2 `A:eq:localidentification` for the finite-gap fields `Φ⁻¹(P_Λ z)`:** the energy
`𝓔_W` defining `ν̂_Λ` is the local-charge series `∑ c_j/(j!)^4 Q_{2j}`. -/
theorem energy_finiteGap_charge_series38 (Λ : Finset ℤ) (z : ℤ → ℂ) :
    ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = B.cleanΦinv (projFin38 Λ z) ∧
      Summable (fun j : ℕ => NlsGge.coefficient c j * localCharge38 U j) ∧
      energyW38 c (B.cleanΦinv (projFin38 Λ z)) =
        ∑' j : ℕ, NlsGge.coefficient c j * localCharge38 U j := by
  have hall : ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier (B.cleanΦinv (projFin38 Λ z))) :=
    fun m => B.sobolev_cleanΦinv38 m _ (finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 Λ z))
  obtain ⟨U, hU, hper, hUu⟩ := exists_smooth_rep38 _ hall
  have hfin := B.finiteGapStructure_fin38 Λ z
  rw [← hUu] at hfin
  obtain ⟨h1, h2⟩ := energyW38_eq_charge_series lower upper c hlower hbound hupper U hU hper hfin
  rw [hUu] at h2
  exact ⟨U, hU, hper, hUu, h1, h2⟩

end Smooth

end BirkhoffTop38

end NlsGge.Birkhoff
