import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurElimination38V1
import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30
import NlsGge.Schur.ActualSchurEffectiveDerivativeSupportV1_32

                                                                                                           
                                                                                                                     
                                                                                             
                                                                                                               
                                                                                                                     
                                                                                                           
                                                                                                                        
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

/-- Coordinate identity: for a Dirac-kernel coordinate vector `u`, `Q u = D S (V P u)`. -/
private theorem s022_hq3 (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (Vt St : SectorSquare n →L[ℂ] SectorSquare n)
    (hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))).comp St = 1)
    (hS2 : St.comp ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))) = 1)
    (u : SectorSquare n) (hq : complementarySquare n u = freeResolventSquare n z hz (Vt u)) :
    complementarySquare n u = freeResolventSquare n z hz (St (Vt (resonantSquare n u))) := by
  have hxyq : u = resonantSquare n u + complementarySquare n u :=
    (resonantSquare_add_complementarySquare38 n u).symm
  have hq2 : complementarySquare n u = freeResolventSquare n z hz (Vt (resonantSquare n u)) +
      freeResolventSquare n z hz (Vt (complementarySquare n u)) := by
    calc complementarySquare n u = freeResolventSquare n z hz (Vt u) := hq
      _ = freeResolventSquare n z hz (Vt (resonantSquare n u + complementarySquare n u)) := by
          rw [← hxyq]
      _ = _ := by rw [map_add, map_add]
  have hd : complementarySquare n u - freeResolventSquare n z hz (St (Vt (resonantSquare n u))) =
      freeResolventSquare n z hz (Vt (complementarySquare n u -
        freeResolventSquare n z hz (St (Vt (resonantSquare n u))))) := by
    have e := schurCore_hDSw38 n z hz Vt St hS1 (Vt (resonantSquare n u))
    simp only [map_sub]
    calc complementarySquare n u - freeResolventSquare n z hz (St (Vt (resonantSquare n u)))
        = (freeResolventSquare n z hz (Vt (resonantSquare n u)) +
            freeResolventSquare n z hz (Vt (complementarySquare n u))) -
          (freeResolventSquare n z hz (Vt (resonantSquare n u)) +
            freeResolventSquare n z hz (Vt (freeResolventSquare n z hz
              (St (Vt (resonantSquare n u)))))) := by
          rw [← hq2, ← e]
      _ = _ := by abel
  exact sub_eq_zero.mp (schurCore_inj38 n z hz Vt St hS2 _ hd)

/-- Elimination identity for an arbitrary Dirac-kernel coordinate vector `u`. -/
private theorem s022_core (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (Vt St : SectorSquare n →L[ℂ] SectorSquare n)
    (hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))).comp St = 1)
    (hS2 : St.comp ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))) = 1)
    (u : SectorSquare n) (hq : complementarySquare n u = freeResolventSquare n z hz (Vt u)) :
    resonantSquare n (Vt u) = schurEffectiveSquare38 n z hz Vt St (resonantSquare n u) := by
  have hq3 := s022_hq3 n z hz Vt St hS1 hS2 u hq
  have hVu : Vt u = Vt (resonantSquare n u) + Vt (complementarySquare n u) := by
    rw [← map_add, resonantSquare_add_complementarySquare38]
  unfold schurEffectiveSquare38
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, resonantSquare_idem38]
  rw [hVu, map_add, hq3]

/-- Forward identity on the Dirac kernel: `(z - nπ) P x = effective(P x)`. -/
private theorem s022_fwd (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (Vt St : SectorSquare n →L[ℂ] SectorSquare n)
    (hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))).comp St = 1)
    (hS2 : St.comp ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))) = 1)
    (x : freeWeightedDomainPointwise n)
    (hsh : freeShiftedCoordinateDirac n z x = Vt x.val) :
    (z - spectralCenter n) • resonantSquare n x.val =
      schurEffectiveSquare38 n z hz Vt St (resonantSquare n x.val) := by
  have hq : complementarySquare n x.val = freeResolventSquare n z hz (Vt x.val) := by
    rw [← hsh]
    exact (freeShiftedCoordinateDirac_left_inverse_complement n z hz x).symm
  have hP := resonantSquare_shifted38 n z x
  rw [hsh] at hP
  rw [← hP]
  exact s022_core n z hz Vt St hS1 hS2 x.val hq

/-- Injectivity: a Dirac-kernel vector with zero resonant part is zero. -/
private theorem s022_inj (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (Vt St : SectorSquare n →L[ℂ] SectorSquare n)
    (hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))).comp St = 1)
    (hS2 : St.comp ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))) = 1)
    (x : freeWeightedDomainPointwise n)
    (hsh : freeShiftedCoordinateDirac n z x = Vt x.val)
    (hP0 : resonantSquare n x.val = 0) : x.val = 0 := by
  have hq : complementarySquare n x.val = freeResolventSquare n z hz (Vt x.val) := by
    rw [← hsh]
    exact (freeShiftedCoordinateDirac_left_inverse_complement n z hz x).symm
  have hq3 := s022_hq3 n z hz Vt St hS1 hS2 x.val hq
  simp only [hP0, map_zero] at hq3
  have hu := resonantSquare_add_complementarySquare38 n x.val
  rw [hP0, hq3, zero_add] at hu
  exact hu.symm

/-- Backward identity: the explicit preimage `y + D S V y` of an effective-kernel vector lies in the Dirac kernel. -/
private theorem s022_bwd (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (Vt St : SectorSquare n →L[ℂ] SectorSquare n)
    (hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))).comp St = 1)
    (hS2 : St.comp ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))) = 1)
    (y : SectorSquare n) (hPy : resonantSquare n y = y)
    (hker : (z - spectralCenter n) • y = schurEffectiveSquare38 n z hz Vt St y) :
    ∃ x : freeWeightedDomainPointwise n,
      x.val = y + freeResolventSquare n z hz (St (Vt y)) ∧
      freeShiftedCoordinateDirac n z x = Vt x.val := by
  have hyd := freeWeightedDomain_of_resonant38 n y hPy
  have hDd := freeResolventSquare_mem_freeWeightedDomain n z hz (St (Vt y))
  refine ⟨⟨y, hyd⟩ + ⟨freeResolventSquare n z hz (St (Vt y)), hDd⟩, rfl, ?_⟩
  show freeShiftedCoordinateDirac n z (⟨y, hyd⟩ + ⟨freeResolventSquare n z hz (St (Vt y)), hDd⟩) =
    Vt (y + freeResolventSquare n z hz (St (Vt y)))
  have hshx : freeShiftedCoordinateDirac n z (⟨y, hyd⟩ + ⟨freeResolventSquare n z hz (St (Vt y)), hDd⟩) =
      (z - spectralCenter n) • y + complementarySquare n (St (Vt y)) := by
    have h1 : freeShiftedCoordinateDirac n z (⟨y, hyd⟩ + ⟨freeResolventSquare n z hz (St (Vt y)), hDd⟩) =
        freeShiftedCoordinateDirac n z ⟨y, hyd⟩ +
          freeShiftedCoordinateDirac n z ⟨freeResolventSquare n z hz (St (Vt y)), hDd⟩ := map_add _ _ _
    rw [h1, freeShiftedCoordinateDirac_right_inverse_complement]
    congr 1
    have hQy : complementarySquare n y = 0 := by
      conv_lhs => rw [← hPy]
      exact complementarySquare_resonantSquare38 n y
    have hP := resonantSquare_shifted38 n z ⟨y, hyd⟩
    have hQ : complementarySquare n (freeShiftedCoordinateDirac n z ⟨y, hyd⟩) = 0 := by
      apply lp.ext; funext i
      by_cases h : i.2 = resonantIndex n
      · simp [h]
      · have hyi : y i = 0 := by
          have := congrArg (fun f : SectorSquare n => f i) hPy
          simpa [h] using this.symm
        have e : (freeShiftedCoordinateDirac n z ⟨y, hyd⟩) i =
            z * y i - spectralCenter i.2.val * y i := rfl
        simp [h, e, hyi]
    have hsum := resonantSquare_add_complementarySquare38 n
      (freeShiftedCoordinateDirac n z ⟨y, hyd⟩)
    rw [hP, hQ, add_zero] at hsum
    rw [← hsum]
    simp only [hPy]
  have hSw := schurCore_hSw38 n z hz Vt St hS1 (Vt y)
  have hQg : complementarySquare n (St (Vt y)) = complementarySquare n (Vt y) +
      complementarySquare n (Vt (freeResolventSquare n z hz (St (Vt y)))) := by
    have := congrArg (complementarySquare n) hSw
    rwa [map_add, complementarySquare_idem38] at this
  have hker' : (z - spectralCenter n) • y = resonantSquare n (Vt y) +
      resonantSquare n (Vt (freeResolventSquare n z hz (St (Vt y)))) := by
    rw [hker]
    unfold schurEffectiveSquare38
    simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, hPy]
    try rfl
  rw [hshx, map_add, hQg, hker', add_add_add_comm, resonantSquare_add_complementarySquare38,
    resonantSquare_add_complementarySquare38]

theorem dirac_schur_kernel_equiv :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair),
      schurParameterDomain K R n z p →
      ∃ e : (diracKernelAt n z p) ≃ₗ[ℂ] (effectiveKernelAt n z p),
        (∀ x : diracKernelAt n z p,
          (e x).val.val = resonantSquare n x.val.val) ∧
        (∀ y : effectiveKernelAt n z p,
          (e.symm y).val.val = y.val.val +
            actualSchurEndomorphismToSquareV5_30 n (greenColumn n z p) y.val.val) := by
  refine ⟨|4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant| + 1, by positivity, ?_⟩
  intro R n z p hdom
  unfold schurParameterDomain at hdom
  obtain ⟨hR, hn0, hK, hz, hp₁, hp₂⟩ := hdom
  have hn : 1 ≤ |(n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast h1
  have hlarge : 4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant * R ^ 2 ≤
      |(n : ℝ)| := by
    have hle := le_abs_self (4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant)
    have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
    have h2 : 4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant * R ^ 2 ≤
        (|4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant| + 1) * R ^ 2 := by
      nlinarith
    linarith
  have htwo := actualComplementaryQVDJointInverseV5_30_twoSided R hR n hn hlarge z p hz hp₁ hp₂
  obtain ⟨Vt, hVt⟩ : ∃ V : SectorSquare n →L[ℂ] SectorSquare n,
      V = actualSchurCoordinatePotential38 n p := ⟨_, rfl⟩
  obtain ⟨St, hSt⟩ : ∃ S : SectorSquare n →L[ℂ] SectorSquare n,
      S = actualSchurEndomorphismToSquareV5_30 n (actualComplementaryQVDJointInverseV5_30 n (z, p)) :=
    ⟨_, rfl⟩
  have hKt : actualSchurEndomorphismToSquareV5_30 n (actualComplementaryQVDJointParameterV5_30 n (z, p)) =
      (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz)) := by
    rw [hVt]
    unfold actualComplementaryQVDJointParameterV5_30 actualSchurCoordinatePotential38
    simp only [toSq_comp38, toSq_complementary38, toSq_freeResolvent38,
      actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]
  have hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
      (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))).comp St = 1 := by
    have h := congrArg (actualSchurEndomorphismToSquareV5_30 n) htwo.2
    rw [toSq_comp38, toSq_sub38, toSq_one38, hKt, ← hSt] at h
    exact h
  have hS2 : St.comp ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
      (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))) = 1 := by
    have h := congrArg (actualSchurEndomorphismToSquareV5_30 n) htwo.1
    rw [toSq_comp38, toSq_sub38, toSq_one38, hKt, ← hSt] at h
    exact h
  have hEff : actualSchurEndomorphismToSquareV5_30 n (effectiveAt n z p) =
      schurEffectiveSquare38 n z hz Vt St := by
    rw [hVt, hSt]
    unfold effectiveAt actualSchurEffectiveOperatorAfterDextV3_30 actualComplementaryQVDJointInverseV5_30
    simp only [toSq_add38, toSq_comp38, toSq_resonant38, toSq_freeResolvent38,
      actualFreeResolventCenterExtension_eq_actualV1_30 n z hz, actualSchurCoordinatePotential38,
      schurEffectiveSquare38]
  have hG : actualSchurEndomorphismToSquareV5_30 n (greenColumn n z p) =
      (freeResolventSquare n z hz).comp (St.comp (Vt.comp (resonantSquare n))) := by
    rw [hVt, hSt]
    unfold greenColumn resolventFamily actualSchurResolventFamilyAfterDextV3_32 potentialAt
    simp only [toSq_comp38, toSq_freeResolvent38, toSq_resonant38, actualSchurCoordinatePotential38,
      actualFreeResolventCenterExtension_eq_actualV1_30 n z hz, ContinuousLinearMap.comp_assoc]
  have hsh : ∀ x : diracKernelAt n z p, freeShiftedCoordinateDirac n z x.val = Vt x.val.val := by
    intro x
    rw [hVt]
    have h : (freeShiftedCoordinateDirac n z - (actualSchurCoordinatePotential38 n p).toLinearMap.comp
        (freeWeightedDomainPointwise n).subtype) x.val = 0 := x.2
    rw [LinearMap.sub_apply, sub_eq_zero] at h
    exact h
  have hmemD : ∀ x : freeWeightedDomainPointwise n, freeShiftedCoordinateDirac n z x = Vt x.val →
      x ∈ diracKernelAt n z p := by
    intro x hx
    rw [hVt] at hx
    unfold diracKernelAt
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact hx
  have hPy : ∀ y : effectiveKernelAt n z p, resonantSquare n y.val.val = y.val.val := by
    intro y
    have hr : y.val.val ∈ LinearMap.range (resonantSquare n).toLinearMap := y.val.2
    obtain ⟨w, hw⟩ := hr
    rw [← hw]
    exact resonantSquare_idem38 n w
  have hker : ∀ y : effectiveKernelAt n z p,
      (z - spectralCenter n) • y.val.val = schurEffectiveSquare38 n z hz Vt St y.val.val := by
    intro y
    have h : ((((z - spectralCenter n) • LinearMap.id) -
        (actualSchurEndomorphismToSquareV5_30 n (effectiveAt n z p)).toLinearMap).comp
          (resonantSpaceAt n).subtype) y.val = 0 := y.2
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe, sub_eq_zero] at h
    rw [hEff] at h
    exact h
  have hEffMem : ∀ u : SectorSquare n, (hu : u ∈ resonantSpaceAt n) →
      (z - spectralCenter n) • u = schurEffectiveSquare38 n z hz Vt St u →
      (⟨u, hu⟩ : resonantSpaceAt n) ∈ effectiveKernelAt n z p := by
    intro u hu h
    unfold effectiveKernelAt
    rw [LinearMap.mem_ker]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe, sub_eq_zero]
    rw [hEff]
    exact h
  -- forward map: Dirac kernel -> resonant range -> effective kernel
  let P0 : SectorSquare n →ₗ[ℂ] SectorSquare n := (resonantSquare n).toLinearMap
  let A : diracKernelAt n z p →ₗ[ℂ] resonantSpaceAt n :=
    LinearMap.codRestrict (resonantSpaceAt n)
      (P0.comp ((freeWeightedDomainPointwise n).subtype.comp (diracKernelAt n z p).subtype))
      (fun x => LinearMap.mem_range_self (resonantSquare n).toLinearMap _)
  let f : diracKernelAt n z p →ₗ[ℂ] effectiveKernelAt n z p :=
    LinearMap.codRestrict (effectiveKernelAt n z p) A
      (fun x => hEffMem (resonantSquare n x.val.val)
        (LinearMap.mem_range_self (resonantSquare n).toLinearMap x.val.val)
        (s022_fwd n z hz Vt St hS1 hS2 x.val (hsh x)))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : resonantSquare n x.val.val = 0 :=
      congrArg (fun w : effectiveKernelAt n z p => (w.val.val : SectorSquare n)) hx
    apply Subtype.ext
    apply Subtype.ext
    exact s022_inj n z hz Vt St hS1 hS2 x.val (hsh x) h0
  have hsurj' : ∀ y : effectiveKernelAt n z p, ∃ x : diracKernelAt n z p,
      x.val.val = y.val.val + freeResolventSquare n z hz (St (Vt y.val.val)) ∧ f x = y := by
    intro y
    obtain ⟨x, hx1, hx2⟩ := s022_bwd n z hz Vt St hS1 hS2 y.val.val (hPy y) (hker y)
    refine ⟨⟨x, hmemD x hx2⟩, hx1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show resonantSquare n x.val = y.val.val
    rw [hx1, map_add, freeResolventSquare_resonant38, add_zero]
    exact hPy y
  have hsurj : Function.Surjective f := fun y => by
    obtain ⟨x, _, hx⟩ := hsurj' y
    exact ⟨x, hx⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro x
    rfl
  · intro y
    obtain ⟨x1, hx1, hfx1⟩ := hsurj' y
    have hsymm : (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm y = x1 := by
      rw [LinearEquiv.symm_apply_eq]
      exact hfx1.symm
    rw [hsymm, hx1, hG]
    simp only [ContinuousLinearMap.comp_apply, hPy y]

end NlsGge.ThirdConsultation.S
