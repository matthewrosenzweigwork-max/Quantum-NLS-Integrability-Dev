import Mathlib
import NlsGge.Birkhoff.F05Identity38f
import NlsGge.Atomic.F.F014
import NlsGge.Atomic.F.F010Host
import NlsGge.Atomic.F.F010Meas

/- F015 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/F/F015.lean,
   namespace NlsGge.ThirdConsultation.F. PACKET F-015. STAGED AFTER F-014 (NlsGge/Atomic/F/F014.lean, proof development,
   F014_MAINPROBE01 q326): uses its `actual_TinvC_eq_finiteTInv`.
   Head VERBATIM from followup13 definitions_design_20261027/STATEMENTS/F.md §F-015 (R14_AUDIT_F2 HOSTABLE;
   BINDING_INDEX_FP80_17 retain_head_unchanged); preamble = F.lean.md block opens + `open NlsGge.GKDefinitionDesign`.
   Route (printed: v2 B:eq:fourieridentity; existing conditional Birkhoff/F05Identity38f `F05_identity38`, not
   re-proved), at the ACTUAL inputs B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38:
   (a) inverseOnSequence m = FinvH38 ∘ finiteTInv m ∘ gaussianRealization38 agrees γ_m-a.e. with B.PhiInvX38 m
       (ae_summable38 gives z ∈ h^{m-1}; seqRealization_apply38 + carrierExt38 identify the realization with
       carrierMk38; cleanTinvC_of_mem; B.TinvC = finiteTInv by F014.actual_TinvC_eq_finiteTInv);
   (b) hence finiteNormalizer = ZM38 B (integral_congr_ae) and finiteGapLaw = muM38 B: the density identity
       (withDensity_smul with explicit measurability, withDensity_congr_ae, ofReal_div_of_pos AFTER 0 < Z_m from
       F05_identity38) and Measure.map_congr under the absolute continuity c • γ.withDensity f ≪ γ (measurability
       of the map is not needed by map_congr; inverseOnSequence is measurable, F010Meas);
   then F05_identity38 gives 0 < Z ≤ 1, integrability of e^{-V_m} (a conclusion), ∫ e^{-V_m} dγ^F = Z and
   μ_m = Z⁻¹e^{-V_m}γ^F. No hypothesis added. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
open NlsGge.GKDefinitionDesign

/-- **(a)** For any inverse map `fTinv` that is `B.TinvC (m-1)` in carrier form, the sequence-side inverse
`FinvH38 ∘ fTinv ∘ gaussianRealization38` agrees `γ_m`-a.e. with `B.PhiInvX38 m`. -/
theorem f015_ae_inverse (B : BirkhoffInput38) {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)
    (fTinv : Hm1 m → Hm1 m)
    (hfTinv : ∀ y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ),
      B.TinvC (m - 1) y = toCarrier38 _ (fTinv (ofCarrier38 _ y))) :
    ∀ᵐ z ∂gammaM38 m β, FinvH38 m (fTinv (gaussianRealization38 m z)) = B.PhiInvX38 m z := by
  filter_upwards [ae_summable38 (m := m) (β := β) hm (fun j hj => (hβ j hj).le) (hβ 0 (Nat.zero_le _))
    (hβ m le_rfl)] with z hz
  have hz' : z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) := (mem_seqSobolev38_iff _ _).2 hz
  have hreal : toCarrier38 _ (gaussianRealization38 m z) = carrierMk38 _ z hz' := by
    apply carrierExt38
    funext n
    rw [carrierCoe38_mk]
    exact seqRealization_apply38 _ z hz n
  unfold BirkhoffInput38.PhiInvX38 FinvH38
  rw [B.cleanTinvC_of_mem _ z hz', ← hreal, hfTinv]
  rfl

/-- **(b)** For any measurable sequence-side inverse `g` agreeing `γ_m`-a.e. with `B.PhiInvX38 m`, the
normalized law built from `g` and its normalizer are the F05 objects, so the conditional F05 identity applies.
Positivity of the normalizer is established before any division. -/
theorem f015_of_inputs (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m)
    (hβ : ∀ j ≤ m, 0 < β j) (g : (ℤ → ℂ) → Hm1 m) (hgm : Measurable g)
    (hg : ∀ᵐ z ∂gammaM38 m β, g z = B.PhiInvX38 m z) :
    ((ENNReal.ofReal (∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β))⁻¹ •
        (gammaM38 m β).withDensity (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (g z))))).map g =
      (gammaFM38 m β).withDensity (fun u => ENNReal.ofReal (Real.exp (-Vm38 m β u) /
        ∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β)) ∧
    Integrable (fun u => Real.exp (-Vm38 m β u)) (gammaFM38 m β) ∧
    (∫ u, Real.exp (-Vm38 m β u) ∂gammaFM38 m β) = ∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β ∧
    0 < ∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β ∧
    ∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β ≤ 1 := by
  obtain ⟨hZ, hint, hI, hmu⟩ := F05_identity38 B O hm hβ
  have hN : ∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β = ZM38 B m β := by
    unfold ZM38
    exact integral_congr_ae (hg.mono fun z hz => by simp only [hz])
  rw [hN]
  have hZpos : 0 < ZM38 B m β := hZ.1
  have hfm : Measurable (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (g z)))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((continuous_Rm38 hm hβ).measurable.comp hgm).neg)
  -- the density side
  have hdens : (ENNReal.ofReal (ZM38 B m β))⁻¹ •
      (gammaM38 m β).withDensity (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (g z)))) =
      muHatM38 B m β := by
    rw [← withDensity_smul _ hfm]
    unfold muHatM38
    refine withDensity_congr_ae (hg.mono fun z hz => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hz, ENNReal.ofReal_div_of_pos hZpos, ENNReal.div_eq_inv_mul]
  -- the map side (`Measure.map_congr` under absolute continuity)
  have hac : (ENNReal.ofReal (ZM38 B m β))⁻¹ •
      (gammaM38 m β).withDensity (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (g z)))) ≪ gammaM38 m β :=
    Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hlaw : ((ENNReal.ofReal (ZM38 B m β))⁻¹ •
      (gammaM38 m β).withDensity (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (g z))))).map g =
      muM38 B m β := by
    rw [Measure.map_congr (hac.ae_le hg), hdens]
    rfl
  refine ⟨?_, hint, hI, hZ.1, hZ.2⟩
  rw [hlaw, hmu]
  congr 1
  funext u
  rw [div_eq_inv_mul]

/-- **F-015** (head verbatim). -/
theorem f015 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    finiteGapLaw m β = (gammaFM38 m β).withDensity
      (fun u => ENNReal.ofReal (Real.exp (-Vm38 m β u) / finiteNormalizer m β)) ∧
    Integrable (fun u => Real.exp (-Vm38 m β u)) (gammaFM38 m β) ∧
    (∫ u, Real.exp (-Vm38 m β u) ∂gammaFM38 m β) = finiteNormalizer m β ∧
    0 < finiteNormalizer m β ∧ finiteNormalizer m β ≤ 1 := by
  have h := f015_of_inputs NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
    NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 hm hβ (inverseOnSequence m)
    (NlsGge.ThirdConsultation.F010Aux.measurable_inverseOnSequence m hm)
    (f015_ae_inverse NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38 hm hβ (finiteTInv m)
      (actual_TinvC_eq_finiteTInv m))
  unfold finiteGapLaw finiteNormalizer finiteDensity
  exact h

end NlsGge.ThirdConsultation.F
