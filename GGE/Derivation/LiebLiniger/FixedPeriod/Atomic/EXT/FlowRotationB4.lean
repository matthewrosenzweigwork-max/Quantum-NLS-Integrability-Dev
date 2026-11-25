import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationB3

/-! # The actual finite-gap Hamiltonian pairing

The first variation is computed on h¹, transported using the actual h⁰
canonicity through its Sobolev derivative compatibility, and restricted to the
finite tangent plane using conservation of actual Birkhoff support.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
local notation "B0" =>
  NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38
local notation "B" => NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
local notation "H1" => SobolevCarrier38 ((1 : ℕ) : ℝ)

set_option maxHeartbeats 1600000 in
/-- The actual finite-plane NLS velocity represents the first differential of
the literal physical Hamiltonian, with precisely twice the standard real
symplectic pairing and the conjugate velocity in the first argument. -/
theorem finiteGap_actualHamiltonian_pairing38 :
    ∀ (Λ : Finset ℤ) (w : Λ → ℂ) (t : ℝ) (η : Λ → ℂ),
      HasDerivAt (fun s : ℝ => HΛ Λ (fun i => ZΛ Λ w t i + (s : ℂ) * η i))
        (2 * ∑ i : Λ, (starRingEnd ℂ ((deriv (ZΛ Λ w) t) i) * η i).im) 0 := by
  intro Λ w t η
  let u := (B0).finiteGapField38 Λ w
  have hu3 := finiteSupport_physicalSobolev_all38 u
    ((B0).finite_support_Φ_finiteGapField38 Λ w) 3
  have hu1 := finiteSupport_physicalSobolev_all38 u
    ((B0).finite_support_Φ_finiteGapField38 Λ w) 1
  obtain ⟨γ, D, hγ, hD, hDc⟩ := nlsFlowSeq_hasDerivAt_H1_38 (physicalFourier u)
    ((mem_seqSobolev38_iff _ _).2 hu3)
  have hu1' : SobolevSquareSummable 1 (physicalFourier u) := by
    simpa only [Nat.cast_one] using hu1
  let R : H1 →L[ℝ] H1 := (reflIso38 ((1 : ℕ) : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  let x := R (γ t)
  let z := finitePlaneInsert38 Λ (ZΛ Λ w t)
  let v := fderiv ℝ ((B0).TinvC 1) z (finitePlaneInsert38 Λ η)
  have hγF : ∀ s, carrierCoe38 _ (R (γ s)) = fourierSeq38 (nlsFlowL2 s u) := by
    intro s
    funext n
    change -carrierCoe38 _ (γ s) (-n) = fourierSeq38 (nlsFlowL2 s u) n
    rw [fourierSeq38_apply]
    have hp := physicalFourier_nlsFlowL2 hu1' s
    rw [hγ s, hp]
  have hRx : HasDerivAt (fun s => R (γ s)) (R (D t)) t :=
    R.hasFDerivAt.comp_hasDerivAt t (hD t)
  have htan := actualPhi_finitePlane_tangent38 Λ w (fun s => R (γ s))
    (R (D t)) t hγF hRx
  have hTx : (B0).TC 1 x = z := by
    apply carrierExt38
    rw [BirkhoffTop38.TC_coe, hγF t, finitePlaneInsert38_coe]
    exact actualPhi_eq_extZero_ZΛ38 Λ w t
  have hix : (B0).TinvC 1 z = x := by
    rw [← hTx, (B0).TinvC_TC]
  have hiv : fderiv ℝ ((B0).TC 1) x v = finitePlaneInsert38 Λ η := by
    rw [← hix]
    exact actual_TC1_TinvC1_fderiv38 z (finitePlaneInsert38 Λ η)
  have hcan := actual_TC1_symplectic38 x (R (D t)) v
  rw [htan, hiv, finitePlaneInsert38_coe, finitePlaneInsert38_coe,
    stdSymplectic38_finitePlane38] at hcan
  have hsym : stdSymplectic38 (carrierCoe38 _ (D t)) (carrierCoe38 _ (R v)) =
      ∑ i : Λ, (starRingEnd ℂ ((deriv (ZΛ Λ w) t) i) * η i).im := by
    exact (stdSymplectic38_reflection38 (D t) v).symm.trans hcan.symm
  have hline := finitePlane_line_hasDerivAt38 Λ (ZΛ Λ w t) η 0
  have hJ := (finitePlaneInsert38 Λ).hasFDerivAt.comp_hasDerivAt 0 hline
  have hFi : HasFDerivAt ((B0).TinvC 1) (fderiv ℝ ((B0).TinvC 1) z)
      (finitePlaneInsert38 Λ (fun i => ZΛ Λ w t i + (0 : ℂ) * η i)) := by
    simpa only [zero_mul, add_zero] using
      ((B).analyticOnNhd_TinvC 1 z (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hI := hFi.comp_hasDerivAt 0 hJ
  have hδ := R.hasFDerivAt.comp_hasDerivAt 0 hI
  have hH := hasDerivAt_ham_curve38 _ _ 0 hδ
  have hbase : R ((B0).TinvC 1 z) = γ t := by
    rw [hix]
    change R (R (γ t)) = γ t
    have hRcoe (y : H1) : R y = reflC38 ((1 : ℕ) : ℝ) y := rfl
    rw [hRcoe, hRcoe]
    exact reflC38_reflC38 ((1 : ℕ) : ℝ) (γ t)
  simp only [Function.comp_apply, Complex.ofReal_zero, zero_mul, add_zero] at hH
  rw [hbase, ham_variation_rhs38] at hH
  have hrhs : rhsSeq (carrierCoe38 _ (γ t)) = carrierCoe38 _ (D t) := by
    rw [hγ t, hDc t]
  rw [hrhs, hsym] at hH
  have hf : (fun s : ℝ => ham (carrierCoe38 _
      (R ((B0).TinvC 1 (finitePlaneInsert38 Λ (fun i => ZΛ Λ w t i + (s : ℂ) * η i)))))) =
      fun s : ℝ => HΛ Λ (fun i => ZΛ Λ w t i + (s : ℂ) * η i) := by
    funext s
    exact (HΛ_eq_inverseCarrier38 Λ (fun i => ZΛ Λ w t i + (s : ℂ) * η i)).symm
  rw [hf] at hH
  exact hH

end LiebLiniger.FixedPeriod.EXT
