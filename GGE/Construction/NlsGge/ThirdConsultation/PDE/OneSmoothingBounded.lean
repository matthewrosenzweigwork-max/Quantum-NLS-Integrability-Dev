import NlsGge.ThirdConsultation.PDE.OneSmoothing

/-! Bounded-set consequences of the existing quantitative smoothing estimates.
Candidate only: root must compile this exact file and run the receiving probe.
No production interface or accepted source is modified by this text artifact. -/

set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common
open NlsGge.ThirdConsultation.G6024S

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

/-- The actual forward correction is the real component of complex smoothing. -/
theorem actualT38_smoothing_carrier_eq (r : ℕ) (hr : 1 ≤ r)
    (x : SobolevCarrier38 (r : ℝ)) :
    carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun y => actualBirkhoffInput38.T y - y) (actualT38_smooth r hr) x =
      fromPairEq (r + 1) (NlsGge.ThirdConsultation.KSN.complexSmoothing r (toPair r x)) := by
  apply carrierExt38
  funext n
  rw [carrierMap38_coe]
  show actualT38 (carrierCoe38 (r : ℝ) x) n - carrierCoe38 (r : ℝ) x n =
    fromSeqEq (r + 1) (NlsGge.ThirdConsultation.KSN.complexSmoothing r (toPair r x)) n
  have hx : carrierMk38 (r : ℝ) (carrierCoe38 (r : ℝ) x)
      (carrierCoe38_mem (r : ℝ) x) = x := carrierExt38 rfl
  have h := smooth_coord r hr (carrierCoe38 (r : ℝ) x)
    (carrierCoe38_mem (r : ℝ) x) n
  rw [hx] at h
  exact h

/-- Each real Sobolev ball has a uniform gain-one forward-correction bound. -/
theorem actualT38_smoothing_ball_bound (r : ℕ) (hr : 1 ≤ r)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : SobolevCarrier38 (r : ℝ), ‖x‖ ≤ B →
      ‖carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun y => actualBirkhoffInput38.T y - y) (actualT38_smooth r hr) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := (KSN019_main r hr).2.2.2 (‖toPair r‖ * B)
    (mul_nonneg (norm_nonneg _) hB)
  refine ⟨‖fromPairEq (r + 1)‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro x hx
  rw [actualT38_smoothing_carrier_eq r hr x]
  have hpair : ‖toPair r x‖ ≤ ‖toPair r‖ * B :=
    ((toPair r).le_opNorm x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hcs := hbound (toPair r x)
    (NlsGge.ThirdConsultation.KSN022S.toPair_isReal r x) hpair
  exact ((fromPairEq (r + 1)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left hcs (norm_nonneg _))

private theorem e04_carrier_cast_norm {a b : ℝ} (h : a = b)
    (y : SobolevCarrier38 a) :
    ‖carrierMk38 b (carrierCoe38 a y) (CarrierCastAux.carrier_cast_mem h y)‖ = ‖y‖ := by
  subst h
  have heq : carrierMk38 a (carrierCoe38 a y)
      (CarrierCastAux.carrier_cast_mem rfl y) = y := carrierExt38 rfl
  rw [heq]

/-- The actual inverse correction has exactly the physical smoothing norm. -/
theorem actualTinv38_smoothing_norm_eq (r : ℕ) (hr : 1 ≤ r)
    (z : SobolevCarrier38 (r : ℝ)) :
    ‖carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun y => actualBirkhoffInput38.Tinv y - y) (actualTinv38_smooth r hr) z‖ =
      ‖inverseSmoothing r z‖ := by
  have hcast : (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) := by push_cast; ring
  have heq : carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun y => actualBirkhoffInput38.Tinv y - y) (actualTinv38_smooth r hr) z =
      carrierMk38 ((r + 1 : ℕ) : ℝ)
        (carrierCoe38 ((r : ℝ) + 1)
          (NlsGge.Atomic.Common.physicalSobolevFourierEquiv38 ((r : ℝ) + 1) (inverseSmoothing r z)))
        (CarrierCastAux.carrier_cast_mem hcast _) := by
    apply carrierExt38
    rw [carrierMap38_coe, carrierCoe38_mk,
      coe_equiv_real ((r : ℝ) + 1) (by positivity), ((KSN021_main r hr).2.1 z).2]
    have hz : carrierMk38 (r : ℝ) (carrierCoe38 (r : ℝ) z)
        (carrierCoe38_mem (r : ℝ) z) = z := carrierExt38 rfl
    change actualBirkhoffTop38.Tinv (carrierCoe38 (r : ℝ) z) -
      carrierCoe38 (r : ℝ) z = _
    rw [tinv_sub_eq r _ (carrierCoe38_mem (r : ℝ) z), hz]
  rw [heq, e04_carrier_cast_norm hcast, LinearIsometryEquiv.norm_map]

/-- Each real Sobolev ball has a uniform gain-one inverse-correction bound. -/
theorem actualTinv38_smoothing_ball_bound (r : ℕ) (hr : 1 ≤ r)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SobolevCarrier38 (r : ℝ), ‖z‖ ≤ B →
      ‖carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun y => actualBirkhoffInput38.Tinv y - y) (actualTinv38_smooth r hr) z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := (KSN021_main r hr).2.2 B hB
  refine ⟨C, hC, fun z hz => ?_⟩
  rw [actualTinv38_smoothing_norm_eq r hr z]
  exact hbound z hz

/-- The gain-one forward correction sends every bounded real set to a bounded set. -/
theorem actualT38_smoothing_isBounded_image (r : ℕ) (hr : 1 ≤ r)
    (S : Set (SobolevCarrier38 (r : ℝ))) (hS : Bornology.IsBounded S) :
    Bornology.IsBounded
      ((carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun x => actualBirkhoffInput38.T x - x) (actualT38_smooth r hr)) '' S) := by
  obtain ⟨B, hB, hnorm⟩ := hS.exists_pos_norm_le
  obtain ⟨C, _hC, hbound⟩ := actualT38_smoothing_ball_bound r hr B hB.le
  apply isBounded_iff_forall_norm_le.2
  refine ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hbound x (hnorm x hx)

/-- The gain-one inverse correction sends every bounded real set to a bounded set. -/
theorem actualTinv38_smoothing_isBounded_image (r : ℕ) (hr : 1 ≤ r)
    (S : Set (SobolevCarrier38 (r : ℝ))) (hS : Bornology.IsBounded S) :
    Bornology.IsBounded
      ((carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun z => actualBirkhoffInput38.Tinv z - z) (actualTinv38_smooth r hr)) '' S) := by
  obtain ⟨B, hB, hnorm⟩ := hS.exists_pos_norm_le
  obtain ⟨C, _hC, hbound⟩ := actualTinv38_smoothing_ball_bound r hr B hB.le
  apply isBounded_iff_forall_norm_le.2
  refine ⟨C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hbound z (hnorm z hz)


                                                                                                   
                                                                                                    
                                                                                      
                                                                                          
theorem actualBirkhoffTop38_canonical_all_levels
    (m : ℕ) (x ξ η : SobolevCarrier38 (m : ℝ)) :
    stdSymplectic38
      (carrierCoe38 (m : ℝ)
        (fderiv ℝ (actualBirkhoffTop38.TC m) x ξ))
      (carrierCoe38 (m : ℝ)
        (fderiv ℝ (actualBirkhoffTop38.TC m) x η)) =
    stdSymplectic38
      (carrierCoe38 (m : ℝ) ξ) (carrierCoe38 (m : ℝ) η) := by
  rw [← actualBirkhoffAnalytic38.fderiv_TC_compat_coe 0 m trivial trivial
      (Nat.zero_le m) x ξ,
    ← actualBirkhoffAnalytic38.fderiv_TC_compat_coe 0 m trivial trivial
      (Nat.zero_le m) x η,
    actualBirkhoffTop38_canonical, carrierCoe38_incl38, carrierCoe38_incl38]

end
end NlsGge.ThirdConsultation.PDE
