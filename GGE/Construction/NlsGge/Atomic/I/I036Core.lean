import Mathlib
import NlsGge.Atomic.I.IEnsembleCore
import NlsGge.Atomic.I.I038Charge
import NlsGge.ThirdConsultation.I.Basic
import NlsGge.Birkhoff.S05FreeEnergy38c
import NlsGge.Birkhoff.S04FiniteGapInvariance38
import NlsGge.Birkhoff.S03Measure38c
import NlsGge.Birkhoff.S03Measure38d
import NlsGge.Birkhoff.H02Hierarchy38b
import NlsGge.Birkhoff.F11Claim38d

                                                                                                     
                                                                                                      
                                                                                                       
                                                                                                           
                                                                                                  
                                                                                                     
                                                                                         
                                                                                                                       
                                                                                                          
                                                                                                    
                                                                                                           
                                                                                            
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I
open NlsGge.HierarchyRiccati.Core (localCharge38)

namespace NlsGge.ThirdConsultation.I036C

/-- `Φ` is measurable for any topological Birkhoff input (same proof as the landed
`BirkhoffInput38.measurable_Phi38`, which only uses the `BirkhoffTop38` part). -/
theorem measurable_Phi (Bk : BirkhoffTop38) : Measurable Bk.Φ := by
  have : Bk.Φ = fun u => Bk.cleanT0 (fourierSeq38 u) :=
    funext fun u => (Bk.cleanT0_of_mem _ (fourierSeq38_mem_zero u)).symm
  rw [this]
  exact Bk.measurable_cleanT0.comp measurable_fourierSeq38

/-- `Φ u ∈ Ω₀(c)` for `μ_W`-a.e. `u` (same proof as the landed `BirkhoffInput38.ae_muW38_Phi_mem_Omega038`). -/
theorem ae_muW_Phi_mem_Omega0 (Bk : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hl : 0 < lower)
    (hb : ∀ j : ℕ, lower ≤ c j) (hu : ∀ j : ℕ, c j ≤ upper) :
    ∀ᵐ u ∂(Bk.muW38 c), Bk.Φ u ∈ Omega038 c := by
  have hmeas : MeasurableSet {u : PhysicalL2 | Bk.Φ u ∈ Omega038 c} :=
    (measurableSet_Omega038 lower upper c hl hb hu).preimage (measurable_Phi Bk)
  refine (ae_map_iff Bk.measurable_cleanΦinv.aemeasurable hmeas).2 ?_
  have h0 : ∀ᵐ z ∂(fullWeightSequenceGaussian c), z ∈ Omega038 c ∧ Bk.Φ (Bk.cleanΦinv z) = z := by
    filter_upwards [ae_mem_Omega038 lower upper c hl hb hu] with z hz
    exact ⟨hz, Bk.Φ_cleanΦinv z (seqSobolev38_natCast_mono (BirkhoffTop38.mem_seqSobolev38_of_Omega038 _ hz 1))⟩
  have h1 := (Bk.muHatW38_equivalent lower upper c hl hb hu).1.ae_le h0
  filter_upwards [h1] with z hz
  show Bk.Φ (Bk.cleanΦinv z) ∈ Omega038 c
  rw [hz.2]; exact hz.1

theorem i036_of (Bk : BirkhoffTop38) (hBk : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ∀ᵐ u ∂physicalLaw (weight c.val),
      (∀ j : ℕ, 0 ≤ chargeFn38 (j + 2) j u) ∧
      Summable (fun n : ℤ => |gapRemainderTermE02_38 (weight c.val) u n|) ∧
      (∀ S : Finset ℤ,
        (∑ n ∈ S, gapIntW38 (weight c.val) u n) =
          (∑ n ∈ S, fullWeightRate c.val n * actualGapActionAllE02_38 u n) +
            (∑ n ∈ S, gapRemainderTermE02_38 (weight c.val) u n)) ∧
      (∑' n : ℤ, ENNReal.ofReal
        (fullWeightRate c.val n * actualGapActionAllE02_38 u n)) = ⊤ ∧
      (∑' n : ℤ, ENNReal.ofReal (gapIntW38 (weight c.val) u n)) = ⊤ ∧
      spectralEnergyENN (weight c.val) u = ⊤ ∧
      (∑' j : ℕ, ENNReal.ofReal (coefficient c.val j * chargeFn38 (j + 2) j u)) = ⊤ ∧
      Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + 1),
        coefficient c.val j * chargeFn38 (j + 2) j u) atTop atTop := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hW : Continuous (weight c.val) := weight_continuous38 hl hb' hu'
  rw [← NlsGge.ThirdConsultation.IEnsC.muW_eq_of Bk hBk lower upper c]
  filter_upwards [ae_muW_Phi_mem_Omega0 Bk lower upper c.val hl hb' hu',
    Bk.ae_muW38_gapSum_eq_top lower upper c.val hl hb' hu',
    Bk.S05_infiniteEnergy_38 lower upper c.val hl hb' hu',
    Bk.ae_muW38_allSobolev lower upper c.val hl hb' hu'] with u hz hgap hS hall
  -- the convergent remainder series at `u = Φ⁻¹(Φ u)`
  have hRs : Summable (fun n : ℤ => remainderSummand38 c.val u n) := by
    have h := (Bk.remainder_tendsto_pathwise38 lower upper c.val hl hb' hu' (Bk.Φ u) hz
      isExhaustion_stdExh38).1
    rwa [Bk.cleanΦinv_Φ38 u] at h
  have hterm : ∀ n : ℤ, gapRemainderTermE02_38 (weight c.val) u n = remainderSummand38 c.val u n :=
    fun n => (remainderSummand38_eq_gapRemainderTerm c.val hW u n).symm
  have hRsum : Summable (fun n : ℤ => gapRemainderTermE02_38 (weight c.val) u n) := by
    simpa only [hterm] using hRs
  have habs : Summable (fun n : ℤ => |gapRemainderTermE02_38 (weight c.val) u n|) :=
    summable_abs_iff.2 hRsum
  have hid : ∀ n : ℤ, gapIntW38 (weight c.val) u n =
      fullWeightRate c.val n * actualGapActionAllE02_38 u n +
        gapRemainderTermE02_38 (weight c.val) u n := by
    intro n
    rw [hterm n, remainderSummand38, ← gapIntegral38_eq_gapIntW38]
    ring
  have hG : (∑' n : ℤ, ENNReal.ofReal (gapIntW38 (weight c.val) u n)) = ⊤ := hgap.2
  have hA : (∑' n : ℤ, ENNReal.ofReal
      (fullWeightRate c.val n * actualGapActionAllE02_38 u n)) = ⊤ :=
    tsum_ofReal_eq_top_of_add_summable38 (fun n => gapIntW38 (weight c.val) u n)
      (fun n => fullWeightRate c.val n * actualGapActionAllE02_38 u n)
      (fun n => -gapRemainderTermE02_38 (weight c.val) u n)
      (fun n => by rw [hid n]; ring) hRsum.neg hG
  obtain ⟨U, hU, hper, hUu⟩ := hS.1
  obtain ⟨_hnn, hE, hser, _hns, htend⟩ := hS.2 U hU hper hUu
  have hloc : ∀ j : ℕ, chargeFn38 (j + 2) j u = localCharge38 U j := fun j =>
    NlsGge.ThirdConsultation.I038C.chargeFn_eq_local u hall U hU hper hUu (j + 2) j
      (by omega) (by omega)
  refine ⟨fun j => chargeFn38_nonneg (j + 2) j (by omega) (by omega) u, habs,
    fun S => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun n _ => hid n,
    hA, hG, hE, ?_, ?_⟩
  · simp only [hloc]
    exact hser
  · simp only [hloc]
    exact htend.comp (tendsto_add_atTop_nat 1)

end NlsGge.ThirdConsultation.I036C
