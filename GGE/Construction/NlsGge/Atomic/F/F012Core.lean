import Mathlib
import NlsGge.Atomic.F.F009Core
import NlsGge.Atomic.F.F009Host
import NlsGge.Atomic.F.F012Host

                                                                                                 
                                                                                           
                                                                                                                    
                                                                                                                    
                                                                                                                
                                                                                                                 
                                                                                                       
                                                                                                                    
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F012Aux
open NlsGge.ThirdConsultation.F (lowerSobolev sobolevCoe finiteA finiteD)

/-- `a_{m,n}` is even in `n`. -/
theorem rate_neg (m : ℕ) (β : ℕ → ℝ) (n : ℤ) :
    finiteHierarchyRate38 m β (-n) = finiteHierarchyRate38 m β n := by
  unfold finiteHierarchyRate38 finiteHierarchyW38
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Int.cast_neg, mul_neg, Even.neg_pow ⟨j, two_mul j⟩]

theorem coe_lower (m : ℕ) (h : SobolevHilbert (m : ℝ)) (n : ℤ) :
    sobolevCoe _ (lowerSobolev m h) n =
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from h) n :=
  NlsGge.ThirdConsultation.F009Aux.lower_coeff m h n

theorem coe_refl (m : ℕ) (h : SobolevHilbert (m : ℝ)) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from
      ofCarrier38 _ (reflC38 (m : ℝ) (toCarrier38 _ h))) n =
      -(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from h) (-n) :=
  carrierCoe38_reflC38 _ _ n

theorem coe_FinvH (m : ℕ) (x : Hm1 m) (n : ℤ) :
    sobolevCoe _ (FinvH38 m x) n = -sobolevCoe _ x (-n) :=
  coeff_FinvH38 m x n

/-- The true inclusion commutes with the reflection `𝓕⁻¹`. -/
theorem lower_refl (m : ℕ) (h : SobolevHilbert (m : ℝ)) :
    lowerSobolev m (ofCarrier38 _ (reflC38 (m : ℝ) (toCarrier38 _ h))) =
      FinvH38 m (lowerSobolev m h) := by
  refine carrierExt38 (r := ((m - 1 : ℕ) : ℝ)) (funext fun n => ?_)
  change sobolevCoe _ (lowerSobolev m (ofCarrier38 _ (reflC38 (m : ℝ) (toCarrier38 _ h)))) n =
    sobolevCoe _ (FinvH38 m (lowerSobolev m h)) n
  rw [coe_lower, coe_refl, coe_FinvH, coe_lower]

/-- F-012 for any coordinate map `Φ` with the action identity and any `T` whose coefficients are the
`Φ`-coordinates of the reflected field (realized by `finiteT` in F012.lean via F012Sup1 and G6028). -/
theorem core (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (Φ : PhysicalL2 → ℤ → ℂ)
    (hact : ∀ (u : PhysicalL2) (n : ℤ), actualGapActionAllE02_38 u n = ‖Φ u n‖ ^ 2)
    (T : Hm1 m → Hm1 m)
    (hT : ∀ (x : Hm1 m) (n : ℤ),
      sobolevCoe _ (T x) n = Φ (sobolevToL2_38 (m - 1) (FinvH38 m x)) n) :
    Continuous (finiteD m β) ∧
    ∀ h : SobolevHilbert (m : ℝ),
      Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
        ‖sobolevCoe _ (lowerSobolev m h) n‖ ^ 2) ∧
      Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
        ‖sobolevCoe _ (T (lowerSobolev m h)) n‖ ^ 2) ∧
      finiteD m β (lowerSobolev m h) =
        finiteA m β (T (lowerSobolev m h)) - finiteA m β (lowerSobolev m h) := by
  refine ⟨((continuous_Vm38 hm hβ).comp (continuous_FinvH38 m)).sub
      ((continuous_Rm38 hm hβ).comp (continuous_FinvH38 m)), fun h => ?_⟩
  have hlr := lower_refl m h
  obtain ⟨-, hS2h, -, -, -⟩ := NlsGge.ThirdConsultation.F009Aux.core m hm β hβ Φ hact h
    (lowerSobolev m h) (fun n => (coe_lower m h n).symm)
  obtain ⟨hS1r, -, -, hE1r, hE2r⟩ := NlsGge.ThirdConsultation.F009Aux.core m hm β hβ Φ hact
    (ofCarrier38 _ (reflC38 (m : ℝ) (toCarrier38 _ h)))
    (lowerSobolev m (ofCarrier38 _ (reflC38 (m : ℝ) (toCarrier38 _ h))))
    (fun n => (coe_lower m _ n).symm)
  have hL2 : sobolevToL2_38 m (ofCarrier38 _ (reflC38 (m : ℝ) (toCarrier38 _ h))) =
      sobolevToL2_38 (m - 1) (FinvH38 m (lowerSobolev m h)) := by
    rw [← hlr]
    exact (NlsGge.ThirdConsultation.F009Aux.sobolevToL2_eq m _ _
      (fun n => (coe_lower m _ n).symm)).symm
  have hTc : ∀ n : ℤ, ‖sobolevCoe _ (T (lowerSobolev m h)) n‖ =
      ‖Φ (sobolevToL2_38 m (ofCarrier38 _ (reflC38 (m : ℝ) (toCarrier38 _ h)))) n‖ :=
    fun n => by rw [hT, hL2]
  refine ⟨hS2h.congr fun n => by rw [coe_lower], hS1r.congr fun n => by rw [hTc n], ?_⟩
  have hAQ : (∑' n : ℤ, finiteHierarchyRate38 m β n *
      ‖Φ (sobolevToL2_38 m (ofCarrier38 _ (reflC38 (m : ℝ) (toCarrier38 _ h)))) n‖ ^ 2) =
      finiteA m β (T (lowerSobolev m h)) := by
    unfold finiteA
    exact tsum_congr fun n => by rw [hTc n]
  have hFQ : (∑' n : ℤ, finiteHierarchyRate38 m β n *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from
        ofCarrier38 _ (reflC38 (m : ℝ) (toCarrier38 _ h))) n‖ ^ 2) =
      finiteA m β (lowerSobolev m h) := by
    unfold finiteA
    have hre := (Equiv.neg ℤ).tsum_eq
      (fun n => finiteHierarchyRate38 m β n * ‖sobolevCoe _ (lowerSobolev m h) n‖ ^ 2)
    refine Eq.trans ?_ hre
    refine tsum_congr fun n => ?_
    simp only [Equiv.neg_apply]
    rw [coe_refl, norm_neg, rate_neg, coe_lower]
  rw [hAQ] at hE1r
  rw [hFQ] at hE2r
  show Vm38 m β (FinvH38 m (lowerSobolev m h)) - Rm38 m β (FinvH38 m (lowerSobolev m h)) = _
  rw [← hlr]
  linarith

end NlsGge.ThirdConsultation.F012Aux
