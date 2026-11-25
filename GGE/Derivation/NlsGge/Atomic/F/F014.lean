import Mathlib
import NlsGge.Birkhoff.F05Identity38e
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.ThirdConsultation.PDE.BirkhoffCarrierCore
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Atomic.F.F010Host
import NlsGge.Atomic.F.F012Host

/- F014 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/F/F014.lean,
   namespace NlsGge.ThirdConsultation.F. PACKET F-014 (REUSE/EXTRACT). Head VERBATIM from followup13
   definitions_design_20261027/STATEMENTS/F.md §F-014 (round-14 R14_AUDIT_F2 HOSTABLE; round-17 BINDING_INDEX_FP80_17
   "retain_head_unchanged"); preamble = DEFINITIONS/F.lean.md block opens + `open NlsGge.GKDefinitionDesign`
   (as in the landed F010Host/F012Host).
   Route (printed: v2 B:cor:identity; existing conditional Birkhoff/F05Identity38e `ramer_density05`, not re-proved):
   instantiate the F05 chain at the ACTUAL inputs B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38
   (landed realizations of E01/E04, so no conditional premise remains). Same witnesses:
   T = T05 B, K = K05 B O, K' = K05' B O, δK from the single ramer_F05_instance call (KEEP-RAMER-GENERAL, landed
   production anchor RamerInstancesB). a.s. identification J = e^{-D_m} = uniqueness of the γ-limit of the finite
   Ramer densities (ramer_F05_instance conv. in measure + tendsto_finiteRamerDensity05 pointwise), exactly the
   ramer_density05 argument; the pointwise clause is tendsto_finiteRamerDensity05 at z = coordE x (R_coordE).
   Actual maps: T05_apply / T05_symm_apply give B.TC / B.TinvC; ofParts makes actualBirkhoffInput38.TC =
   actualBirkhoffTop38.TC = actualTC38 = birkhoffSobolev ∘ F⁻¹ (actualBirkhoffTop38_TC), and TinvC = F ∘
   inverseBirkhoffSobolev (actualBirkhoffTop38_TinvC): definitionally finiteT / finiteTInv (F012Host / F010Host).
   Integrability (Integrable J), positivity and ∫ J = 1 are conclusions of the instance, proved there before the
   pushforward identity; no integral identity is used here. No hypothesis added. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
open NlsGge.GKDefinitionDesign

/-- **F-014 core.** The F-014 conclusion for the F05 chain at inputs `B, O`, with the forward/inverse maps
identified through `hfT`/`hfTinv` (the carrier forms of `B.TC (m-1)` / `B.TinvC (m-1)`).  Same witnesses:
`T = T05 B`, `K = K05 B O`, `K' = K05' B O`, and `δK` from the single `ramer_F05_instance` call. -/
theorem f014_of_inputs (B : BirkhoffInput38) (O : OneSmoothingInput38 B) (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) (fT fTinv : Hm1 m → Hm1 m)
    (hfT : ∀ y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ), B.TC (m - 1) y = toCarrier38 _ (fT (ofCarrier38 _ y)))
    (hfTinv : ∀ y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ),
      B.TinvC (m - 1) y = toCarrier38 _ (fTinv (ofCarrier38 _ y))) :
    let S := NlsGge.Birkhoff.S05 m β hm hβ
    let e := NlsGge.Birkhoff.Eq05 m β hm hβ
    ∃ T : S.E ≃ₜ S.E, ∃ K K' : S.E → S.H,
      (∀ x : S.E,
        T x = e (toCarrier38 _ (fT (ofCarrier38 _ (e.symm x)))) ∧
        T.symm x = e (toCarrier38 _ (fTinv (ofCarrier38 _ (e.symm x))))) ∧
      (∀ x : S.E, T x = x + S.incl (K x) ∧
        T.symm x = x + S.incl (K' x)) ∧
      ContDiff ℝ 2 K ∧ ContDiff ℝ 2 K' ∧
      ∃ δK : (ℤ → ℂ) → ℝ,
        (∀ x₀ : S.E, ∃ r : ℝ, 0 < r ∧
          ∃ (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
            Set.EqOn G K (Metric.ball x₀ r) ∧
            S.IsClosedDiv (fun z => G (S.R z)) η) ∧
        (∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (Metric.ball x₀ r) →
          S.IsClosedDiv (fun z => G (S.R z)) η →
          ∀ᵐ z ∂S.γ, S.R z ∈ Metric.ball x₀ r → δK z = η z) ∧
        let J : S.E → ℝ := fun x =>
          |NlsGge.Analysis.RegularizedDeterminant.det2 (S.hsDerivH K x)| *
            Real.exp (-δK (S.coordE x) - ‖K x‖ ^ 2 / 2)
        (∀ᵐ x ∂S.γE, J x = Real.exp (-NlsGge.Birkhoff.D05 hm hβ x)) ∧
        S.γE.map T.symm = S.γE.withDensity (fun x => ENNReal.ofReal (J x)) ∧
        S.γE.map T.symm = S.γE.withDensity
          (fun x => ENNReal.ofReal (Real.exp (-NlsGge.Birkhoff.D05 hm hβ x))) ∧
        (∀ x : S.E, 0 < J x) ∧ Integrable J S.γE ∧
        (∫ x, J x ∂S.γE) = 1 ∧
        TendstoInMeasure S.γ
          (fun N z => NlsGge.Ramer.finiteRamerDensity
            (fun v => v + S.truncField K N v) (S.headPt N z))
          atTop (fun z => J (S.R z)) ∧
        (∀ x : S.E,
          Tendsto (fun N => NlsGge.Ramer.finiteRamerDensity
            (fun v => v + S.truncField K N v) (S.headPt N (S.coordE x)))
            atTop (nhds (Real.exp (-NlsGge.Birkhoff.D05 hm hβ x)))) := by
  dsimp only
  obtain ⟨δK, hloc, huniq, hrest⟩ := NlsGge.Ramer.General.ramer_F05_instance (m := m) (β := β) hm
    (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) (T05 B hm hβ)
    (K05 B O hm hβ) (K05' B O hm hβ) (hT05 B O hm hβ) (hTs05 B O hm hβ)
    ((analytic_K05 B O hm hβ).contDiff) ((analytic_K05' B O hm hβ).contDiff)
  obtain ⟨hmap, hpos, hint, hone, hconv⟩ := hrest
  -- almost-sure identification `J = e^{-D_m}` (route of `ramer_density05`, same δK)
  obtain ⟨ns, hns, hae⟩ := hconv.exists_seq_tendsto_ae
  have hlim : ∀ᵐ z ∂(S05 m β hm hβ).γ, ∀ n, (S05 m β hm hβ).coord n ((S05 m β hm hβ).R z) = z n :=
    (S05 m β hm hβ).coord_R_ae
  have hJ : ∀ᵐ z ∂(S05 m β hm hβ).γ, (fun x => |NlsGge.Analysis.RegularizedDeterminant.det2
        ((S05 m β hm hβ).hsDerivH (K05 B O hm hβ) x)| *
        Real.exp (-(δK ((S05 m β hm hβ).coordE x)) - ‖K05 B O hm hβ x‖ ^ 2 / 2))
        ((S05 m β hm hβ).R z) = Real.exp (-(D05 hm hβ ((S05 m β hm hβ).R z))) := by
    filter_upwards [hae, hlim] with z hz1 hz2
    have h2 := tendsto_finiteRamerDensity05 B O hm hβ z hz2
    exact tendsto_nhds_unique hz1 (h2.comp hns.tendsto_atTop)
  have hJ' : ∀ᵐ x ∂(S05 m β hm hβ).γE, |NlsGge.Analysis.RegularizedDeterminant.det2
        ((S05 m β hm hβ).hsDerivH (K05 B O hm hβ) x)| *
        Real.exp (-(δK ((S05 m β hm hβ).coordE x)) - ‖K05 B O hm hβ x‖ ^ 2 / 2) =
      Real.exp (-(D05 hm hβ x)) := by
    filter_upwards [(S05 m β hm hβ).ae_of_ae_coordE hJ] with x hx
    simpa only [(S05 m β hm hβ).R_coordE] using hx
  have hmap2 : (S05 m β hm hβ).γE.map (T05 B hm hβ).symm =
      (S05 m β hm hβ).γE.withDensity (fun x => ENNReal.ofReal (Real.exp (-(D05 hm hβ x)))) :=
    hmap.trans (withDensity_congr_ae (by filter_upwards [hJ'] with x hx; exact congrArg ENNReal.ofReal hx))
  refine ⟨T05 B hm hβ, K05 B O hm hβ, K05' B O hm hβ, fun x => ⟨?_, ?_⟩,
    fun x => ⟨hT05 B O hm hβ x, hTs05 B O hm hβ x⟩,
    (analytic_K05 B O hm hβ).contDiff, (analytic_K05' B O hm hβ).contDiff,
    δK, hloc, huniq, hJ', hmap, hmap2, hpos, hint, hone, hconv, fun x => ?_⟩
  · obtain ⟨y, rfl⟩ := (Eq05 m β hm hβ).surjective x
    rw [T05_apply, LinearIsometryEquiv.symm_apply_apply, hfT]
  · obtain ⟨y, rfl⟩ := (Eq05 m β hm hβ).surjective x
    rw [T05_symm_apply, LinearIsometryEquiv.symm_apply_apply, hfTinv]
  · have h := tendsto_finiteRamerDensity05 B O hm hβ ((S05 m β hm hβ).coordE x)
      (fun n => by rw [(S05 m β hm hβ).R_coordE]; rfl)
    rwa [(S05 m β hm hβ).R_coordE] at h


/-- `actualBirkhoffInput38.TC` is the finite forward map `finiteT` in carrier form. -/
theorem actual_TC_eq_finiteT (m : ℕ) (y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) :
    NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.TC (m - 1) y =
      toCarrier38 _ (finiteT m (ofCarrier38 _ y)) := by
  show NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.TC (m - 1) y = _
  rw [NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_TC]
  rfl

/-- `actualBirkhoffInput38.TinvC` is the finite inverse map `finiteTInv` in carrier form. -/
theorem actual_TinvC_eq_finiteTInv (m : ℕ) (y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) :
    NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.TinvC (m - 1) y =
      toCarrier38 _ (finiteTInv m (ofCarrier38 _ y)) := by
  show NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.TinvC (m - 1) y = _
  rw [NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_TinvC]
  rfl

/-- **F-014** (head verbatim). -/
theorem f014 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    let S := NlsGge.Birkhoff.S05 m β hm hβ
    let e := NlsGge.Birkhoff.Eq05 m β hm hβ
    ∃ T : S.E ≃ₜ S.E, ∃ K K' : S.E → S.H,
      (∀ x : S.E,
        T x = e (toCarrier38 _ (finiteT m (ofCarrier38 _ (e.symm x)))) ∧
        T.symm x = e (toCarrier38 _ (finiteTInv m (ofCarrier38 _ (e.symm x))))) ∧
      (∀ x : S.E, T x = x + S.incl (K x) ∧
        T.symm x = x + S.incl (K' x)) ∧
      ContDiff ℝ 2 K ∧ ContDiff ℝ 2 K' ∧
      ∃ δK : (ℤ → ℂ) → ℝ,
        (∀ x₀ : S.E, ∃ r : ℝ, 0 < r ∧
          ∃ (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
            Set.EqOn G K (Metric.ball x₀ r) ∧
            S.IsClosedDiv (fun z => G (S.R z)) η) ∧
        (∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (Metric.ball x₀ r) →
          S.IsClosedDiv (fun z => G (S.R z)) η →
          ∀ᵐ z ∂S.γ, S.R z ∈ Metric.ball x₀ r → δK z = η z) ∧
        let J : S.E → ℝ := fun x =>
          |NlsGge.Analysis.RegularizedDeterminant.det2 (S.hsDerivH K x)| *
            Real.exp (-δK (S.coordE x) - ‖K x‖ ^ 2 / 2)
        (∀ᵐ x ∂S.γE, J x = Real.exp (-NlsGge.Birkhoff.D05 hm hβ x)) ∧
        S.γE.map T.symm = S.γE.withDensity (fun x => ENNReal.ofReal (J x)) ∧
        S.γE.map T.symm = S.γE.withDensity
          (fun x => ENNReal.ofReal (Real.exp (-NlsGge.Birkhoff.D05 hm hβ x))) ∧
        (∀ x : S.E, 0 < J x) ∧ Integrable J S.γE ∧
        (∫ x, J x ∂S.γE) = 1 ∧
        TendstoInMeasure S.γ
          (fun N z => NlsGge.Ramer.finiteRamerDensity
            (fun v => v + S.truncField K N v) (S.headPt N z))
          atTop (fun z => J (S.R z)) ∧
        (∀ x : S.E,
          Tendsto (fun N => NlsGge.Ramer.finiteRamerDensity
            (fun v => v + S.truncField K N v) (S.headPt N (S.coordE x)))
            atTop (nhds (Real.exp (-NlsGge.Birkhoff.D05 hm hβ x)))) :=
  f014_of_inputs NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
    NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 m hm β hβ (finiteT m) (finiteTInv m)
    (actual_TC_eq_finiteT m) (actual_TinvC_eq_finiteTInv m)

end NlsGge.ThirdConsultation.F
