import NlsGge.Atomic.F.F027
import NlsGge.Birkhoff.F08Bare38b
import NlsGge.Birkhoff.F05Identity38g
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38

                                                                                                          
                                                                                                
                                                                                                       
                                                                                                      
                                                                                              
                             
                                                                                                          
                                                                                             
                                                                                                             
                                                                                                           
                                                                                                          
                                          
                                                                                                         
                                                                                                             
                                                                                     

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core NlsGge.Measure

namespace NlsGge.ThirdConsultation.F

/-- The window map on the physical Fourier carrier (its lowModeSigma is the comap of this map). -/
def f026Window (m N : ℕ) (u : Hm1 m) : FourierPlane N :=
  NlsGge.Ramer.windowProj N (sobolevCoe _ u)

/-- The plane function `z ↦ V_m(z) + C_{m,N}(z)` of the target conditional expectation. -/
def f026K (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (z : FourierPlane N) : ℝ :=
  vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z) + contractionCorrection38 m β N z

theorem f026_trunc_eq_PN (m N : ℕ) (u : Hm1 m) :
    truncSobolev38 _ N u = PN38 m N (sobolevCoe _ u) := by
  apply Subtype.ext
  funext n
  change (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from truncSobolev38 _ N u) n =
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from PN38 m N (sobolevCoe _ u)) n
  rw [truncSobolev38_apply, PN38_coeff]
  rfl

theorem f026_vm_trunc (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (u : Hm1 m) :
    Vm38 m β (truncSobolev38 _ N u) = vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N (f026Window m N u)) := by
  rw [f026_trunc_eq_PN]
  rfl

theorem f026_measurable_vPlane (m : ℕ) (β : ℕ → ℝ) (N : ℕ) :
    Measurable (fun z : FourierPlane N => vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z)) :=
  (continuous_vSobolev38 m β).measurable.comp
    (measurable_finiteElement38 ((m - 1 : ℕ) : ℝ) (modeIndex N))

theorem f026_measurable_cc (m : ℕ) (β : ℕ → ℝ) (N : ℕ) [IsProbabilityMeasure (gammaM38 m β)] :
    Measurable (contractionCorrection38 m β N) := by
  have hF : Measurable (Function.uncurry fun (z : FourierPlane N) (s : ℤ → ℂ) =>
      vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z + tailRealization38 m N s)) := by
    refine (continuous_vSobolev38 m β).measurable.comp ?_
    exact Measurable.add ((measurable_finiteElement38 ((m - 1 : ℕ) : ℝ) (modeIndex N)).comp measurable_fst)
      ((measurable_tailRealization38 N).comp measurable_snd)
  have hI : StronglyMeasurable (fun z : FourierPlane N =>
      ∫ s, vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z + tailRealization38 m N s)
        ∂gammaM38 m β) :=
    StronglyMeasurable.integral_prod_right (ν := gammaM38 m β)
      (f := fun (z : FourierPlane N) (s : ℤ → ℂ) =>
        vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z + tailRealization38 m N s))
      hF.stronglyMeasurable
  have hC : contractionCorrection38 m β N = fun z : FourierPlane N =>
      (∫ s, vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z + tailRealization38 m N s)
        ∂gammaM38 m β) - vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z) := rfl
  rw [hC]
  exact (hI.sub (f026_measurable_vPlane m β N).stronglyMeasurable).measurable

theorem f026 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    Integrable (Vm38 m β) (gammaFM38 m β) ∧
    ∀ N : ℕ,
      lowModeSigma m N ≤ (inferInstance : MeasurableSpace (Hm1 m)) ∧
      (gammaFM38 m β)[Vm38 m β | lowModeSigma m N] =ᵐ[gammaFM38 m β]
        (fun u => Vm38 m β (truncSobolev38 _ N u) +
          contractionCorrection38 m β N (NlsGge.Ramer.windowProj N (sobolevCoe _ u))) := by
  have : IsProbabilityMeasure (gammaM38 m β) := NlsGge.Measure.countableComplexGaussian_probability _
  have hμ : gammaFM38 m β = (gammaM38 m β).map (gaussianRealization38 m) :=
    gammaFM38_eq_realization m β
  have hR : Measurable (gaussianRealization38 m) := measurable_gaussianRealization38
  have hVc : Measurable (Vm38 m β) := (continuous_vSobolev38 m β).measurable
  have hVint : Integrable (Vm38 m β) (Measure.map (gaussianRealization38 m) (gammaM38 m β)) :=
    (integrable_map_measure hVc.aestronglyMeasurable hR.aemeasurable).2 (integrable_Vgr38 hm hβ)
  refine ⟨by rw [hμ]; exact hVint, fun N => ⟨lowModeSigma_le m N, ?_⟩⟩
  have hHeq : (fun u => Vm38 m β (truncSobolev38 _ N u) +
      contractionCorrection38 m β N (NlsGge.Ramer.windowProj N (sobolevCoe _ u))) =
      fun u => f026K m β N (f026Window m N u) := by
    funext u
    rw [f026_vm_trunc]
    rfl
  have hKm : StronglyMeasurable (f026K m β N) :=
    ((f026_measurable_vPlane m β N).add (f026_measurable_cc m β N)).stronglyMeasurable
  have hgM : Measurable[lowModeSigma m N] (f026Window m N) := by
    unfold lowModeSigma f026Window
    exact comap_measurable _
  have hgm : Measurable (f026Window m N) := hgM.mono (lowModeSigma_le m N) le_rfl
  have hHM : StronglyMeasurable[lowModeSigma m N] (fun u => f026K m β N (f026Window m N u)) :=
    hKm.comp_measurable hgM
  have hHm : Measurable (fun u => f026K m β N (f026Window m N u)) :=
    hKm.measurable.comp hgm
  -- Almost sure identification of the window coordinates.
  have hA1 := ae_gaussianRealization_apply38 hm (fun i (hi : i ≤ m) => (hβ i hi).le)
    (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)
  have hG : ∀ᵐ ω ∂(gammaM38 m β), f026Window m N (gaussianRealization38 m ω) =
      NlsGge.Ramer.windowProj N ω := by
    filter_upwards [hA1] with ω hω
    funext i
    exact hω (modeIndex N i)
  have hHR : ∀ᵐ ω ∂(gammaM38 m β), f026K m β N (f026Window m N (gaussianRealization38 m ω)) =
      vSobolev38 m β (PN38 m N ω) + contractionCorrection38 m β N (NlsGge.Ramer.windowProj N ω) := by
    filter_upwards [hG] with ω h2
    rw [h2]
    rfl
  -- Integrability of the target function under the realized Gaussian.
  have hseqInt : Integrable (fun ω => vSobolev38 m β (PN38 m N ω) +
      contractionCorrection38 m β N (NlsGge.Ramer.windowProj N ω)) (gammaM38 m β) :=
    Integrable.congr integrable_condExp (condExp_V_gr38 hm hβ N)
  have hHint : Integrable (fun u => f026K m β N (f026Window m N u))
      (Measure.map (gaussianRealization38 m) (gammaM38 m β)) := by
    refine (integrable_map_measure hHm.aestronglyMeasurable hR.aemeasurable).2 ?_
    refine Integrable.congr hseqInt ?_
    filter_upwards [hHR] with ω h
    exact h.symm
  rw [hμ, hHeq]
  refine Filter.EventuallyEq.symm ?_
  have hVint' : Integrable (Vm38 m β) (Measure.map (gaussianRealization38 m) (gammaM38 m β)) := hVint
  refine ae_eq_condExp_of_forall_setIntegral_eq (lowModeSigma_le m N) hVint' (fun s _ _ => hHint.integrableOn)
    ?_ hHM.aestronglyMeasurable
  intro s hs _
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  have hS : MeasurableSet (NlsGge.Ramer.windowProj N ⁻¹' B) := (NlsGge.Ramer.measurable_windowProj N) hB
  have hS' : MeasurableSet[NlsGge.Ramer.windowSigma N] (NlsGge.Ramer.windowProj N ⁻¹' B) :=
    MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩
  have hset : (gaussianRealization38 m) ⁻¹' (f026Window m N ⁻¹' B) =ᵐ[gammaM38 m β]
      (NlsGge.Ramer.windowProj N ⁻¹' B) := by
    apply Filter.eventuallyEqSet_iff.2
    filter_upwards [hG] with ω hω
    show f026Window m N (gaussianRealization38 m ω) ∈ B ↔ NlsGge.Ramer.windowProj N ω ∈ B
    rw [hω]
  have hL : ∫ y in f026Window m N ⁻¹' B, f026K m β N (f026Window m N y)
      ∂(Measure.map (gaussianRealization38 m) (gammaM38 m β)) =
      ∫ x in (gaussianRealization38 m) ⁻¹' (f026Window m N ⁻¹' B),
        f026K m β N (f026Window m N (gaussianRealization38 m x)) ∂(gammaM38 m β) :=
    setIntegral_map (hgm hB) hHm.aestronglyMeasurable hR.aemeasurable
  have hV : ∫ y in f026Window m N ⁻¹' B, Vm38 m β y
      ∂(Measure.map (gaussianRealization38 m) (gammaM38 m β)) =
      ∫ x in (gaussianRealization38 m) ⁻¹' (f026Window m N ⁻¹' B), Vm38 m β (gaussianRealization38 m x)
        ∂(gammaM38 m β) :=
    setIntegral_map (hgm hB) hVc.aestronglyMeasurable hR.aemeasurable
  have hI1 : ∫ x in (gaussianRealization38 m) ⁻¹' (f026Window m N ⁻¹' B),
      f026K m β N (f026Window m N (gaussianRealization38 m x)) ∂(gammaM38 m β) =
      ∫ x in NlsGge.Ramer.windowProj N ⁻¹' B,
        f026K m β N (f026Window m N (gaussianRealization38 m x)) ∂(gammaM38 m β) :=
    setIntegral_congr_set hset
  have hI2 : ∫ x in NlsGge.Ramer.windowProj N ⁻¹' B,
      f026K m β N (f026Window m N (gaussianRealization38 m x)) ∂(gammaM38 m β) =
      ∫ x in NlsGge.Ramer.windowProj N ⁻¹' B,
        (vSobolev38 m β (PN38 m N x) + contractionCorrection38 m β N (NlsGge.Ramer.windowProj N x))
          ∂(gammaM38 m β) :=
    setIntegral_congr_ae hS (hHR.mono fun ω h _ => h)
  have hI3 : ∫ x in NlsGge.Ramer.windowProj N ⁻¹' B,
      (vSobolev38 m β (PN38 m N x) + contractionCorrection38 m β N (NlsGge.Ramer.windowProj N x))
        ∂(gammaM38 m β) =
      ∫ x in NlsGge.Ramer.windowProj N ⁻¹' B,
        (gammaM38 m β)[fun ω => vSobolev38 m β (gaussianRealization38 m ω) |
          NlsGge.Ramer.windowSigma N] x ∂(gammaM38 m β) :=
    setIntegral_congr_ae hS ((condExp_V_gr38 hm hβ N).mono fun ω h _ => h.symm)
  have hI4 : ∫ x in NlsGge.Ramer.windowProj N ⁻¹' B,
      (gammaM38 m β)[fun ω => vSobolev38 m β (gaussianRealization38 m ω) |
        NlsGge.Ramer.windowSigma N] x ∂(gammaM38 m β) =
      ∫ x in NlsGge.Ramer.windowProj N ⁻¹' B,
        vSobolev38 m β (gaussianRealization38 m x) ∂(gammaM38 m β) :=
    setIntegral_condExp (NlsGge.Ramer.windowSigma_le_pi N) (integrable_Vgr38 hm hβ) hS'
  have hI5 : ∫ x in NlsGge.Ramer.windowProj N ⁻¹' B,
      vSobolev38 m β (gaussianRealization38 m x) ∂(gammaM38 m β) =
      ∫ x in (gaussianRealization38 m) ⁻¹' (f026Window m N ⁻¹' B),
        Vm38 m β (gaussianRealization38 m x) ∂(gammaM38 m β) :=
    setIntegral_congr_set hset.symm
  have key : ∫ x in f026Window m N ⁻¹' B,
      f026K m β N (f026Window m N x) ∂(Measure.map (gaussianRealization38 m) (gammaM38 m β)) =
      ∫ x in f026Window m N ⁻¹' B, Vm38 m β x ∂(Measure.map (gaussianRealization38 m) (gammaM38 m β)) := by
    rw [hL, hV]
    exact hI1.trans (hI2.trans (hI3.trans (hI4.trans hI5)))
  exact key

end NlsGge.ThirdConsultation.F

end
