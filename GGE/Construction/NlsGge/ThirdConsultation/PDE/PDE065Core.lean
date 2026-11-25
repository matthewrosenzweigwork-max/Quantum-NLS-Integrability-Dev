import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Field
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.NLS38.PhysicalFlow38
import NlsGge.NLS38.NonlinCarrier38
import NlsGge.NLS38.SolutionNotion38
import NlsGge.Birkhoff.S01Equivariance38
import NlsGge.Birkhoff.S04Moments38

                                                                                          
                                                                                                                       
                                                                                                                  
                                                                                                                         
                                                                                                                        
                                                                                                     
                                                                                                                
                                                                      
                                                                                                                          
                      
                                                                                                                        
                                                                                                              
                                                                                       
                                                                                                         
                                                                                                                           
                                                                                                                       
                                                                                                              
                                                                                                                             
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.NLS38 NlsGge.GKDefinitionDesign NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.PDE
namespace PDE065Aux
noncomputable section

theorem exists_cast_clm (r s : ℝ) (h : r = s) :
    ∃ L : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 s,
      ∀ y, L y = Eq.mp (congrArg SobolevCarrier38 h) y := by
  subst h
  exact ⟨ContinuousLinearMap.id ℝ _, fun _ => rfl⟩

theorem physicalCoreBase_clm :
    ∃ L : PhysicalSobolev38 ((3 : ℕ) : ℝ) →L[ℝ] PhysicalSobolev38 ((1 : ℕ) : ℝ),
      ∀ u, L u = physicalCoreBase u := by
  obtain ⟨C, hC⟩ := exists_cast_clm _ _ (show ((3 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) + 2 by norm_num)
  refine ⟨(physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((carrierIncl38 (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)).comp
      (C.comp (physicalSobolevFourierEquiv38 ((3 : ℕ) : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap)),
    fun u => ?_⟩
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, hC]
  rfl

theorem hasDerivAt_physicalCoreBase {w : ℝ → PhysicalSobolev38 ((3 : ℕ) : ℝ)}
    {w' : PhysicalSobolev38 ((3 : ℕ) : ℝ)} {t : ℝ} (h : HasDerivAt w w' t) :
    HasDerivAt (fun s => physicalCoreBase (w s)) (physicalCoreBase w') t := by
  obtain ⟨L, hL⟩ := physicalCoreBase_clm
  have e : (fun s => physicalCoreBase (w s)) = fun s => L (w s) := funext fun s => (hL _).symm
  rw [e, ← hL]
  exact L.hasFDerivAt.comp_hasDerivAt t h

theorem sequenceSobolevEmbed_incl (z : SobolevCarrier38 ((3 : ℕ) : ℝ)) :
    sequenceSobolevEmbed 1
        (carrierIncl38 (r := ((1 : ℕ) : ℝ)) (s := ((3 : ℕ) : ℝ)) (by norm_num) z) =
      sequenceSobolevEmbed 3 z := by
  apply lp.ext
  rw [sequenceSobolevEmbed_coe, sequenceSobolevEmbed_coe, carrierCoe38_incl38]

theorem base_inverse
    (hc1 : ∀ z : SobolevCarrier38 ((1 : ℕ) : ℝ),
      physicalSobolevEmbed 1 (inverseBirkhoffSobolev 1 z) =
        physicalInverseBirkhoff (sequenceSobolevEmbed 1 z))
    (hc3 : ∀ z : SobolevCarrier38 ((3 : ℕ) : ℝ),
      physicalSobolevEmbed 3 (inverseBirkhoffSobolev 3 z) =
        physicalInverseBirkhoff (sequenceSobolevEmbed 3 z))
    (z : SobolevCarrier38 ((3 : ℕ) : ℝ)) :
    physicalCoreBase (inverseBirkhoffSobolev 3 z) =
      inverseBirkhoffSobolev 1
        (carrierIncl38 (r := ((1 : ℕ) : ℝ)) (s := ((3 : ℕ) : ℝ)) (by norm_num) z) := by
  apply physicalSobolevEmbed_injective 1
  rw [physicalCoreBase_embed, hc3, hc1, sequenceSobolevEmbed_incl]

/-- Pro's printed support head `DPhiinv_three_one_compatible`, with `DPhiinv m z = fderiv ℝ (inverseBirkhoffSobolev m) z`
unfolded; proved by differentiating the commuting diagram `base_inverse`. -/
theorem fderiv_inverse_three_one
    (hΨa1 : AnalyticOnNhd ℝ (inverseBirkhoffSobolev 1) Set.univ)
    (hΨa3 : AnalyticOnNhd ℝ (inverseBirkhoffSobolev 3) Set.univ)
    (hc1 : ∀ z : SobolevCarrier38 ((1 : ℕ) : ℝ),
      physicalSobolevEmbed 1 (inverseBirkhoffSobolev 1 z) =
        physicalInverseBirkhoff (sequenceSobolevEmbed 1 z))
    (hc3 : ∀ z : SobolevCarrier38 ((3 : ℕ) : ℝ),
      physicalSobolevEmbed 3 (inverseBirkhoffSobolev 3 z) =
        physicalInverseBirkhoff (sequenceSobolevEmbed 3 z))
    (z v : SobolevCarrier38 ((3 : ℕ) : ℝ)) :
    physicalCoreBase (fderiv ℝ (inverseBirkhoffSobolev 3) z v) =
      fderiv ℝ (inverseBirkhoffSobolev 1)
        (carrierIncl38 (r := ((1 : ℕ) : ℝ)) (s := ((3 : ℕ) : ℝ)) (by norm_num) z)
        (carrierIncl38 (r := ((1 : ℕ) : ℝ)) (s := ((3 : ℕ) : ℝ)) (by norm_num) v) := by
  obtain ⟨L, hL⟩ := physicalCoreBase_clm
  set I := carrierIncl38 (r := ((1 : ℕ) : ℝ)) (s := ((3 : ℕ) : ℝ)) (by norm_num) with hI
  have h3 := (hΨa3 z (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have h1 := (hΨa1 (I z) (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hA : HasFDerivAt (fun y => L (inverseBirkhoffSobolev 3 y)) (L.comp (fderiv ℝ (inverseBirkhoffSobolev 3) z)) z :=
    L.hasFDerivAt.comp z h3
  have hB : HasFDerivAt (fun y => inverseBirkhoffSobolev 1 (I y))
      ((fderiv ℝ (inverseBirkhoffSobolev 1) (I z)).comp I) z :=
    h1.comp z I.hasFDerivAt
  have hfun : (fun y => L (inverseBirkhoffSobolev 3 y)) = fun y => inverseBirkhoffSobolev 1 (I y) := by
    funext y
    rw [hL]
    exact base_inverse hc1 hc3 y
  rw [hfun] at hA
  have := congrArg (fun T : SobolevCarrier38 ((3 : ℕ) : ℝ) →L[ℝ] PhysicalSobolev38 ((1 : ℕ) : ℝ) => T v)
    (hA.unique hB)
  simp only [ContinuousLinearMap.comp_apply] at this
  rw [← hL]
  exact this

/-- Inverse differential identity at level one: `DΨ₁(Φ₁ p)(DΦ₁ p X) = X`. -/
theorem fderiv_inverse_apply_fderiv
    (hΦa1 : AnalyticOnNhd ℝ (birkhoffSobolev 1) Set.univ)
    (hΨa1 : AnalyticOnNhd ℝ (inverseBirkhoffSobolev 1) Set.univ)
    (hL1 : Function.LeftInverse (inverseBirkhoffSobolev 1) (birkhoffSobolev 1))
    (p X : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    fderiv ℝ (inverseBirkhoffSobolev 1) (birkhoffSobolev 1 p) (fderiv ℝ (birkhoffSobolev 1) p X) = X := by
  have hΦ := (hΦa1 p (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hΨ := (hΨa1 (birkhoffSobolev 1 p) (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hc := hΨ.comp p hΦ
  have hid : (fun q => inverseBirkhoffSobolev 1 (birkhoffSobolev 1 q)) = id := funext hL1
  rw [show (inverseBirkhoffSobolev 1 ∘ birkhoffSobolev 1) = id from hid] at hc
  have := congrArg (fun T : PhysicalSobolev38 ((1 : ℕ) : ℝ) →L[ℝ] PhysicalSobolev38 ((1 : ℕ) : ℝ) => T X)
    (hc.unique (hasFDerivAt_id p))
  simpa using this

theorem rotation_nls_core
    (Ω : ℤ → (ℤ → ℝ) → ℝ) (a : ℤ → ℝ)
    (c3 c3' : ℝ → SobolevCarrier38 ((3 : ℕ) : ℝ))
    (hΦa1 : AnalyticOnNhd ℝ (birkhoffSobolev 1) Set.univ)
    (hΨa1 : AnalyticOnNhd ℝ (inverseBirkhoffSobolev 1) Set.univ)
    (hL1 : Function.LeftInverse (inverseBirkhoffSobolev 1) (birkhoffSobolev 1))
    (hR1 : Function.RightInverse (inverseBirkhoffSobolev 1) (birkhoffSobolev 1))
    (hc1 : ∀ z : SobolevCarrier38 ((1 : ℕ) : ℝ),
      physicalSobolevEmbed 1 (inverseBirkhoffSobolev 1 z) =
        physicalInverseBirkhoff (sequenceSobolevEmbed 1 z))
    (hΨa3 : AnalyticOnNhd ℝ (inverseBirkhoffSobolev 3) Set.univ)
    (hc3 : ∀ z : SobolevCarrier38 ((3 : ℕ) : ℝ),
      physicalSobolevEmbed 3 (inverseBirkhoffSobolev 3 z) =
        physicalInverseBirkhoff (sequenceSobolevEmbed 3 z))
    (h62 : ∀ (u : PhysicalSobolev38 ((3 : ℕ) : ℝ)) (n : ℤ),
      let z : SobolevCarrier38 ((1 : ℕ) : ℝ) := birkhoffSobolev 1 (physicalCoreBase u)
      carrierCoe38 ((1 : ℕ) : ℝ)
        (fderiv ℝ (birkhoffSobolev 1) (physicalCoreBase u) (nlsVectorField u)) n =
          -Complex.I *
            (Ω n (fun k : ℤ => ‖carrierCoe38 ((1 : ℕ) : ℝ) z k‖^2) : ℂ) *
            carrierCoe38 ((1 : ℕ) : ℝ) z n)
    (hmod : ∀ (t : ℝ) (n : ℤ), ‖carrierCoe38 ((3 : ℕ) : ℝ) (c3 t) n‖^2 = a n)
    (hder : ∀ (t : ℝ) (n : ℤ), carrierCoe38 ((3 : ℕ) : ℝ) (c3' t) n =
      -Complex.I * (Ω n a : ℂ) * carrierCoe38 ((3 : ℕ) : ℝ) (c3 t) n)
    (h64 : ∀ t0 : ℝ, HasDerivAt (fun t => inverseBirkhoffSobolev 3 (c3 t))
      (fderiv ℝ (inverseBirkhoffSobolev 3) (c3 t0) (c3' t0)) t0) :
    (∀ t0 : ℝ,
      HasDerivAt (fun t : ℝ => physicalCoreBase (inverseBirkhoffSobolev 3 (c3 t)))
        (nlsVectorField (inverseBirkhoffSobolev 3 (c3 t0))) t0) ∧
    IsPhysicalNLSSolution (fun t => physicalSobolevEmbed 3 (inverseBirkhoffSobolev 3 (c3 t))) := by
  set I := carrierIncl38 (r := ((1 : ℕ) : ℝ)) (s := ((3 : ℕ) : ℝ)) (by norm_num) with hI
  have hi : ∀ t0 : ℝ,
      HasDerivAt (fun t : ℝ => physicalCoreBase (inverseBirkhoffSobolev 3 (c3 t)))
        (nlsVectorField (inverseBirkhoffSobolev 3 (c3 t0))) t0 := by
    intro t0
    have hd := hasDerivAt_physicalCoreBase (h64 t0)
    convert hd using 1
    symm
    rw [fderiv_inverse_three_one hΨa1 hΨa3 hc1 hc3]
    set u := inverseBirkhoffSobolev 3 (c3 t0) with hu
    have hΦp : birkhoffSobolev 1 (physicalCoreBase u) = I (c3 t0) := by
      rw [hu, base_inverse hc1 hc3, hR1]
    have ha : (fun k : ℤ => ‖carrierCoe38 ((1 : ℕ) : ℝ) (I (c3 t0)) k‖^2) = a :=
      funext fun k => by rw [hI, carrierCoe38_incl38, hmod]
    have hDX : fderiv ℝ (birkhoffSobolev 1) (physicalCoreBase u) (nlsVectorField u) = I (c3' t0) := by
      apply carrierCoe38_injective
      funext n
      have h := h62 u n
      simp only at h
      rw [h, hΦp, ha, hI, carrierCoe38_incl38, carrierCoe38_incl38, hder]
    rw [← hΦp, ← hDX]
    exact fderiv_inverse_apply_fderiv hΦa1 hΨa1 hL1 _ _
  refine ⟨hi, ?_⟩
  set q : ℝ → PhysicalSobolev38 ((1 : ℕ) : ℝ) :=
    fun t => physicalCoreBase (inverseBirkhoffSobolev 3 (c3 t)) with hq
  have hU : ∀ t, physicalSobolevEmbed 3 (inverseBirkhoffSobolev 3 (c3 t)) = physicalSobolevEmbed 1 (q t) :=
    fun t => (physicalCoreBase_embed _).symm
  have hmem1 : ∀ p : PhysicalSobolev38 ((1 : ℕ) : ℝ),
      SobolevSquareSummable 1 (physicalFourier (physicalSobolevEmbed 1 p)) := by
    intro p
    have h := (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) (physicalSobolevEmbed 1 p)).1 (physicalSobolevEmbed_mem 1 p)
    simpa using h
  have hqc : Continuous q := continuous_iff_continuousAt.2 fun t => (hi t).continuousAt
  have hcoef : ∀ (p : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (n : ℤ),
      physicalFourier (physicalSobolevEmbed 1 p) n =
        -(coordC38 ((1 : ℕ) : ℝ) (-n)
          ((physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap p)) := by
    intro p n
    rw [coordC38_apply]
    have h := fourierSeq38_apply (physicalSobolevEmbed 1 p) (-n)
    rw [neg_neg, physicalSobolevEmbed_fourier] at h
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [h, neg_neg]
  refine ⟨fun t => by rw [hU]; exact hmem1 _, ?_, ?_⟩
  · have e : (fun t => physH38 1 (physicalSobolevEmbed 3 (inverseBirkhoffSobolev 3 (c3 t)))) =
        fun t => physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) (q t) := by
      funext t
      rw [hU, physH38_of_mem 1 _ (physicalSobolevEmbed_mem 1 _)]
      apply carrierCoe38_injective
      rw [carrierCoe38_mk]
      funext n
      exact physicalSobolevEmbed_fourier 1 _ n
    rw [e]
    exact (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).continuous.comp hqc
  · intro t n
    set E := (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
    have hfun : (fun s => physicalFourier (physicalSobolevEmbed 3 (inverseBirkhoffSobolev 3 (c3 s))) n) =
        fun s => -((coordC38 ((1 : ℕ) : ℝ) (-n)).comp E (q s)) := by
      funext s
      rw [hU, hcoef]
      rfl
    rw [hfun]
    set u := inverseBirkhoffSobolev 3 (c3 t) with hu
    have hD : HasDerivAt (fun s => -((coordC38 ((1 : ℕ) : ℝ) (-n)).comp E (q s)))
        (-((coordC38 ((1 : ℕ) : ℝ) (-n)).comp E (nlsVectorField u))) t :=
      (((coordC38 ((1 : ℕ) : ℝ) (-n)).comp E).hasFDerivAt.comp_hasDerivAt t (hi t)).neg
    have hX : ((coordC38 ((1 : ℕ) : ℝ) (-n)).comp E) (nlsVectorField u) =
        fourierSeq38 (physicalSobolevEmbed 1 (nlsVectorField u)) (-n) := by
      rw [ContinuousLinearMap.comp_apply, coordC38_apply, physicalSobolevEmbed_fourier]
      rfl
    have hval : -((coordC38 ((1 : ℕ) : ℝ) (-n)).comp E (nlsVectorField u)) =
        -Complex.I * (((disp n : ℝ) : ℂ) * physicalFourier (physicalSobolevEmbed 3 u) n +
          nonlin (physicalFourier (physicalSobolevEmbed 3 u)) n) := by
      rw [hX, nlsVectorField_coefficient, fourierSeq38_eq_refl38, nonlin_refl, disp_neg38]
      unfold NlsGge.NLS38.refl
      simp only [neg_neg]
      ring
    rw [hval] at hD
    exact hD

end
end PDE065Aux
end NlsGge.ThirdConsultation.PDE
