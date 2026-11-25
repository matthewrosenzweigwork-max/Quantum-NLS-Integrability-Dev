import Mathlib
import NlsGge.Atomic.G6.G6025SupCore
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.Atomic.LIB.LIB018
import NlsGge.GK38.Lib.CompactOps

                                                                                      
                                                                                        
                                                                                                                       
                                                                                                                         
                                                                                                                    
                                                                                                                  
                         
                                                                                                                         
                                                                                                                              
                                                                                               
                                                                                                                                
                                                                                        
                                                                                                                           
                                                                                
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSN

namespace NlsGge.ThirdConsultation.G6024S
noncomputable section

/-- sequenceSobolevEmbed m as a real continuous linear map (norm ≤ 1). -/
def seqEmb (m : ℕ) : SobolevCarrier38 (m : ℝ) →L[ℝ] lp (fun _ : ℤ => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun z => sequenceSobolevEmbed m z
      map_add' := fun x y => by
        ext n
        rw [lp.coeFn_add, Pi.add_apply]
        simp only [sequenceSobolevEmbed_coe, carrierCoe38_add]
      map_smul' := fun c x => by
        ext n
        rw [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        simp only [sequenceSobolevEmbed_coe, carrierCoe38_smul, Complex.real_smul] }
    1 (fun z => by
      rw [one_mul]
      have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      refine lp.norm_le_of_forall_sum_le hp (norm_nonneg _) (fun s => ?_)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
      have hz := carrier_hasSum m z
      have h1 : ∀ n, ‖(sequenceSobolevEmbed m z : ℤ → ℂ) n‖ ^ 2 ≤
          sobolevModeWeight (m : ℝ) n * ‖carrierCoe38 (m : ℝ) z n‖ ^ 2 := by
        intro n
        rw [sequenceSobolevEmbed_coe]
        have hw : 1 ≤ sobolevModeWeight (m : ℝ) n := by
          rw [smw_eq]; exact one_le_pow₀ (by nlinarith [sq_nonneg (n : ℝ)])
        nlinarith [sq_nonneg ‖carrierCoe38 (m : ℝ) z n‖]
      calc ∑ n ∈ s, ‖(sequenceSobolevEmbed m z : ℤ → ℂ) n‖ ^ 2
          ≤ ∑ n ∈ s, sobolevModeWeight (m : ℝ) n * ‖carrierCoe38 (m : ℝ) z n‖ ^ 2 :=
            Finset.sum_le_sum (fun n _ => h1 n)
        _ ≤ ‖z‖ ^ 2 := by
            rw [← hz.tsum_eq]
            exact hz.summable.sum_le_tsum s (fun n _ => mul_nonneg (sobolevModeWeight_pos _ _).le (sq_nonneg _)))

theorem seqEmb_apply (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) : seqEmb m z = sequenceSobolevEmbed m z := rfl

/-- physicalSobolevEmbed m as a real continuous linear map. -/
def physEmb (m : ℕ) : PhysicalSobolev38 (m : ℝ) →L[ℝ] PhysicalL2 :=
  ((reflectedFourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (seqEmb m)).comp (physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap

theorem physEmb_apply (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) : physEmb m u = physicalSobolevEmbed m u := rfl

/-- The derivative of birkhoffSobolev m (exact form). -/
theorem birkhoffSobolev_hasFDerivAt (m : ℕ)
    (hmemB : ∀ u : PhysicalSobolev38 (m : ℝ),
      (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hA : AnalyticOnNhd ℂ (complexSmoothing m) (complexDomain (m : ℝ) (Nat.cast_nonneg m)))
    (hmem : ∀ x ∈ complexDomain (m : ℝ) (Nat.cast_nonneg m),
      Memℓp (storedSequence ((m : ℝ) + 1) (smoothingCoefficient m x)) 2)
    (u : PhysicalSobolev38 (m : ℝ)) :
    HasFDerivAt (birkhoffSobolev m)
      ((physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap +
        (fromPair m).comp ((fderiv ℝ (complexSmoothing m)
          (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u))).comp
          ((toPair m).comp (physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap))) u := by
  set F : PhysicalSobolev38 (m : ℝ) →L[ℝ] SobolevCarrier38 (m : ℝ) :=
    (physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap with hF
  set T : PhysicalSobolev38 (m : ℝ) →L[ℝ] PairScale (m : ℝ) := (toPair m).comp F with hT
  have hC : AnalyticAt ℝ (complexSmoothing m) (T u) :=
    (hA _ (toPair_mem_complexDomain m u)).restrictScalars
  have heq : birkhoffSobolev m = fun v => F v + fromPair m (complexSmoothing m (T v)) :=
    funext (birkhoffSobolev_eq m hmemB hSR hmem)
  rw [heq]
  have h1 : HasFDerivAt (fun v => complexSmoothing m (T v)) ((fderiv ℝ (complexSmoothing m) (T u)).comp T) u :=
    hC.differentiableAt.hasFDerivAt.comp u T.hasFDerivAt
  exact F.hasFDerivAt.add ((fromPair m).hasFDerivAt.comp u h1)

/-- G6-026 from the G6-024 inputs plus the commuting identity and the L² facts. -/
theorem G6026_of (m : ℕ)
    (hmemB : ∀ u : PhysicalSobolev38 (m : ℝ),
      (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hA : AnalyticOnNhd ℂ (complexSmoothing m) (complexDomain (m : ℝ) (Nat.cast_nonneg m)))
    (hmem : ∀ x ∈ complexDomain (m : ℝ) (Nat.cast_nonneg m),
      Memℓp (storedSequence ((m : ℝ) + 1) (smoothingCoefficient m x)) 2)
    (hcoe : ∀ u : PhysicalSobolev38 (m : ℝ),
      sequenceSobolevEmbed m (birkhoffSobolev m u) = physicalBirkhoff (physicalSobolevEmbed m u))
    (hΦ : AnalyticOnNhd ℝ physicalBirkhoff Set.univ)
    (hL2 : ∀ v : PhysicalL2, ∃ e : PhysicalL2 ≃L[ℝ] Lib.L2Z, e.toContinuousLinearMap = fderiv ℝ physicalBirkhoff v)
    (u : PhysicalSobolev38 (m : ℝ)) :
  (∃ e : PhysicalSobolev38 (m : ℝ) ≃L[ℝ] SobolevCarrier38 (m : ℝ),
    e.toContinuousLinearMap = fderiv ℝ (birkhoffSobolev m) u) ∧
  ∃ (U : Set (PhysicalSobolev38 (m : ℝ))) (V : Set (SobolevCarrier38 (m : ℝ)))
    (g : SobolevCarrier38 (m : ℝ) → PhysicalSobolev38 (m : ℝ)),
    IsOpen U ∧ u ∈ U ∧ IsOpen V ∧ birkhoffSobolev m u ∈ V ∧
    AnalyticOnNhd ℝ (birkhoffSobolev m) U ∧ AnalyticOnNhd ℝ g V ∧
    Set.MapsTo (birkhoffSobolev m) U V ∧ Set.MapsTo g V U ∧
    (∀ v ∈ U, g (birkhoffSobolev m v) = v) ∧
    (∀ z ∈ V, birkhoffSobolev m (g z) = z) := by
  have hglob := birkhoffSobolev_analytic_of m hmemB hSR hA hmem
  set B := (physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv with hB
  set K : PhysicalSobolev38 (m : ℝ) →L[ℝ] SobolevCarrier38 (m : ℝ) :=
    (fromPair m).comp ((fderiv ℝ (complexSmoothing m)
      (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u))).comp
      ((toPair m).comp (physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap)) with hK
  have hder := birkhoffSobolev_hasFDerivAt m hmemB hSR hA hmem u
  have hJ : fderiv ℝ (birkhoffSobolev m) u = (B : PhysicalSobolev38 (m : ℝ) →L[ℝ] SobolevCarrier38 (m : ℝ)) + K :=
    hder.fderiv
  have hKc : IsCompactOperator K := by
    change IsCompactOperator (⇑(fromPair m) ∘ ⇑((fderiv ℝ (complexSmoothing m)
      (toPair m (physicalSobolevFourierEquiv38 (m : ℝ) u))).comp
      ((toPair m).comp (physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap)))
    exact (fromPair_compact m).comp_clm _
  -- injectivity through the commuting identity
  have hcomm : (fun v => seqEmb m (birkhoffSobolev m v)) = fun v => physicalBirkhoff (physEmb m v) := by
    funext v; rw [seqEmb_apply, physEmb_apply, hcoe]
  have hd1 : HasFDerivAt (fun v => seqEmb m (birkhoffSobolev m v)) ((seqEmb m).comp ((B : _ →L[ℝ] _) + K)) u :=
    (seqEmb m).hasFDerivAt.comp u (hJ ▸ hder)
  have hd2 : HasFDerivAt (fun v => physicalBirkhoff (physEmb m v))
      ((fderiv ℝ physicalBirkhoff (physEmb m u)).comp (physEmb m)) u :=
    (hΦ _ (Set.mem_univ _)).differentiableAt.hasFDerivAt.comp u (physEmb m).hasFDerivAt
  rw [hcomm] at hd1
  have hdeq := hd1.unique hd2
  obtain ⟨eL, heL⟩ := hL2 (physEmb m u)
  have hinj : Function.Injective ((B : PhysicalSobolev38 (m : ℝ) →L[ℝ] SobolevCarrier38 (m : ℝ)) + K) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : (fderiv ℝ physicalBirkhoff (physEmb m u)) (physEmb m v) = 0 := by
      have := congrArg (fun L : PhysicalSobolev38 (m : ℝ) →L[ℝ] lp (fun _ : ℤ => ℂ) 2 => L v) hdeq
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [← this, hv, map_zero]
    rw [← heL] at h1
    have h2 : physEmb m v = 0 := by
      have := eL.injective (h1.trans (map_zero eL).symm)
      exact this
    rw [physEmb_apply] at h2
    apply physicalSobolevEmbed_injective m
    rw [h2]
    have := (physEmb m).map_zero
    rw [physEmb_apply] at this
    exact this.symm
  obtain ⟨e, he⟩ := NlsGge.GK38.Lib.bijective_of_one_add_compact B K hKc hinj
  have heJ : e.toContinuousLinearMap = fderiv ℝ (birkhoffSobolev m) u := by
    rw [hJ]; ext v; exact congrFun he v
  refine ⟨⟨e, heJ⟩, ?_⟩
  -- local analytic charts
  have hf : AnalyticAt ℝ (birkhoffSobolev m) u := hglob u (Set.mem_univ u)
  have hL : fderiv ℝ (birkhoffSobolev m) u = (e : PhysicalSobolev38 (m : ℝ) →L[ℝ] SobolevCarrier38 (m : ℝ)) :=
    heJ.symm
  set ch := NlsGge.Atomic.LIB018.analyticLocalInverseChart hf hL with hch
  obtain ⟨V, hVo, huV, hVt, hgV⟩ := NlsGge.Atomic.LIB018.localInverseChart_analyticOnNhd_target hf hL
  have hcont : Continuous (birkhoffSobolev m) :=
    continuous_iff_continuousAt.2 (fun x => (hglob x (Set.mem_univ x)).continuousAt)
  have hcoe' : (ch : PhysicalSobolev38 (m : ℝ) → SobolevCarrier38 (m : ℝ)) = birkhoffSobolev m := rfl
  have husrc : u ∈ ch.source := NlsGge.Atomic.LIB017.mem_localInverseChart_source _
  refine ⟨ch.source ∩ birkhoffSobolev m ⁻¹' V, V, ch.symm, ch.open_source.inter (hVo.preimage hcont),
    ⟨husrc, huV⟩, hVo, huV, fun x _ => hglob x (Set.mem_univ x), hgV, fun x hx => hx.2, ?_, ?_, ?_⟩
  · intro z hz
    have ht := hVt hz
    refine ⟨ch.map_target ht, ?_⟩
    show birkhoffSobolev m (ch.symm z) ∈ V
    rw [← hcoe', ch.right_inv ht]; exact hz
  · intro v hv
    have := ch.left_inv hv.1
    rw [hcoe'] at this
    exact this
  · intro z hz
    have := ch.right_inv (hVt hz)
    rw [hcoe'] at this
    exact this

/-- G6-027's analytic inverse from G6-026 and the landed inverse equations. -/
theorem inverse_analytic_of (m : ℕ)
    (hmemB : ∀ u : PhysicalSobolev38 (m : ℝ),
      (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hA : AnalyticOnNhd ℂ (complexSmoothing m) (complexDomain (m : ℝ) (Nat.cast_nonneg m)))
    (hmem : ∀ x ∈ complexDomain (m : ℝ) (Nat.cast_nonneg m),
      Memℓp (storedSequence ((m : ℝ) + 1) (smoothingCoefficient m x)) 2)
    (hcoe : ∀ u : PhysicalSobolev38 (m : ℝ),
      sequenceSobolevEmbed m (birkhoffSobolev m u) = physicalBirkhoff (physicalSobolevEmbed m u))
    (hΦ : AnalyticOnNhd ℝ physicalBirkhoff Set.univ)
    (hL2 : ∀ v : PhysicalL2, ∃ e : PhysicalL2 ≃L[ℝ] Lib.L2Z, e.toContinuousLinearMap = fderiv ℝ physicalBirkhoff v)
    (hleft : Function.LeftInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m))
    (hright : Function.RightInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m)) :
    AnalyticOnNhd ℝ (inverseBirkhoffSobolev m) Set.univ := by
  intro z _
  set u := inverseBirkhoffSobolev m z with hu
  have hz : birkhoffSobolev m u = z := hright z
  obtain ⟨-, U, V, g, -, -, hVo, hzV, -, hgV, -, -, -, hfg⟩ :=
    G6026_of m hmemB hSR hA hmem hcoe hΦ hL2 u
  rw [hz] at hzV
  have heq : ∀ w ∈ V, inverseBirkhoffSobolev m w = g w := by
    intro w hw
    have := hfg w hw
    calc inverseBirkhoffSobolev m w = inverseBirkhoffSobolev m (birkhoffSobolev m (g w)) := by rw [this]
      _ = g w := hleft (g w)
  exact (hgV z hzV).congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hzV) (fun w hw => (heq w hw).symm))

end
end NlsGge.ThirdConsultation.G6024S
