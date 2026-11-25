import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationA2

/-! # Finite-plane maps and symplectic transport for the actual NLS flow

The finite trajectory and vector field use the literal actual Birkhoff map and
Hamiltonian. The auxiliary carrier maps expose the Sobolev chain rules needed
for finite Hamiltonian transport; no flow-rotation input is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

local notation "B0" =>
  NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38
local notation "B" => NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38

/-- The scope definition of the actual finite-plane trajectory is
`Z_Λ Λ w t i = B0.Φ (nlsFlowL2 t (B0.finiteGapField38 Λ w)) i.1`:
the Λ-coordinates of the actual Birkhoff image of the actual PDE trajectory. -/
def ZΛ (Λ : Finset ℤ) (w : Λ → ℂ) (t : ℝ) (i : Λ) : ℂ :=
  (B0).Φ (nlsFlowL2 t ((B0).finiteGapField38 Λ w)) i.1

/-- The scope definition of the finite Hamiltonian vector field is
`Y_Λ Λ w i = -I / 2 * (dHΛ(w)[e_i] + I * dHΛ(w)[I e_i])`.
Both differentials are real Fréchet differentials of the literal physical
Hamiltonian HΛ. Thus this is exactly minus I/2 times its real coordinate
gradient, including zero coordinates. -/
def YΛ (Λ : Finset ℤ) (w : Λ → ℂ) (i : Λ) : ℂ :=
  -Complex.I / 2 *
    ((fderiv ℝ (HΛ Λ) w (Pi.single i (1 : ℂ)) : ℂ) +
      Complex.I * (fderiv ℝ (HΛ Λ) w (Pi.single i Complex.I) : ℂ))

/-- Zero insertion of a finite complex vector into the real h¹ carrier. -/
def finitePlaneInsert38 (Λ : Finset ℤ) : (Λ → ℂ) →L[ℝ] SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => carrierMk38 _ (extZero38 Λ w)
        (finiteSupport_mem_seqSobolev38 _ _ (finite_support_extZero38 Λ w))
      map_add' := by
        intro w v
        apply carrierExt38
        funext n
        change extZero38 Λ (w + v) n = extZero38 Λ w n + extZero38 Λ v n
        by_cases hn : n ∈ Λ
        · rw [extZero38_apply_of_mem _ hn, extZero38_apply_of_mem _ hn,
            extZero38_apply_of_mem _ hn]
          rfl
        · rw [extZero38_apply_of_not_mem _ hn, extZero38_apply_of_not_mem _ hn,
            extZero38_apply_of_not_mem _ hn, add_zero]
      map_smul' := by
        intro c w
        apply carrierExt38
        funext n
        change extZero38 Λ (c • w) n = c • extZero38 Λ w n
        by_cases hn : n ∈ Λ
        · rw [extZero38_apply_of_mem _ hn, extZero38_apply_of_mem _ hn]
          rfl
        · rw [extZero38_apply_of_not_mem _ hn, extZero38_apply_of_not_mem _ hn,
            smul_zero] }

/-- The underlying sequence of finite-plane insertion is literal zero extension. -/
theorem finitePlaneInsert38_coe (Λ : Finset ℤ) (w : Λ → ℂ) :
    carrierCoe38 ((1 : ℕ) : ℝ) (finitePlaneInsert38 Λ w) = extZero38 Λ w := rfl

/-- The full actual Birkhoff trajectory is the zero extension of ZΛ. -/
theorem actualPhi_eq_extZero_ZΛ38 (Λ : Finset ℤ) (w : Λ → ℂ) (t : ℝ) :
    (B0).Φ (nlsFlowL2 t ((B0).finiteGapField38 Λ w)) = extZero38 Λ (ZΛ Λ w t) := by
  funext n
  by_cases hn : n ∈ Λ
  · rw [extZero38_apply_of_mem _ hn]
    rfl
  · rw [extZero38_apply_of_not_mem _ hn]
    have hs := actualPhi_support_nlsFlow38 ((B0).finiteGapField38 Λ w)
      ((B0).finite_support_Φ_finiteGapField38 Λ w) t
    have hz : (B0).Φ ((B0).finiteGapField38 Λ w) n = 0 := by
      rw [(B0).Φ_finiteGapField38, extZero38_apply_of_not_mem _ hn]
    by_contra h
    have hm : n ∈ {k | (B0).Φ (nlsFlowL2 t ((B0).finiteGapField38 Λ w)) k ≠ 0} := h
    rw [hs] at hm
    exact hm hz

/-- At time zero the actual finite-plane trajectory has its prescribed datum. -/
theorem ZΛ_zero38 (Λ : Finset ℤ) (w : Λ → ℂ) : ZΛ Λ w 0 = w := by
  funext i
  simp only [ZΛ, nlsFlowL2_zero, (B0).Φ_finiteGapField38,
    extZero38_apply_of_mem _ i.2]

/-- The actual finite-plane trajectory is differentiable at every real time. -/
theorem differentiable_ZΛ38 (Λ : Finset ℤ) (w : Λ → ℂ) :
    Differentiable ℝ (ZΛ Λ w) := by
  have hu := finiteSupport_physicalSobolev_all38 ((B0).finiteGapField38 Λ w)
    ((B0).finite_support_Φ_finiteGapField38 Λ w) 3
  obtain ⟨z, hz, hd⟩ := actualPhi_nlsFlow_differentiable_H1_38 _ hu
  intro t
  apply differentiableAt_pi.2
  intro i
  have hc := (coordC38 ((1 : ℕ) : ℝ) i.1).differentiableAt.comp t (hd t)
  have he : (fun s => (coordC38 ((1 : ℕ) : ℝ) i.1) (z s)) =
      fun s => ZΛ Λ w s i := by
    funext s
    change carrierCoe38 ((1 : ℕ) : ℝ) (z s) i.1 = _
    rw [hz s]
    rfl
  change DifferentiableAt ℝ (fun s => (coordC38 ((1 : ℕ) : ℝ) i.1) (z s)) t at hc
  rw [he] at hc
  exact hc

/-- On h¹ tangents, actual canonicity follows from the h⁰ theorem and the
existing compatibility of the derivatives of the same actual map. -/
theorem actual_TC1_symplectic38 (x ξ η : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    stdSymplectic38 (carrierCoe38 ((1 : ℕ) : ℝ) (fderiv ℝ ((B0).TC 1) x ξ))
      (carrierCoe38 ((1 : ℕ) : ℝ) (fderiv ℝ ((B0).TC 1) x η)) =
    stdSymplectic38 (carrierCoe38 ((1 : ℕ) : ℝ) ξ) (carrierCoe38 ((1 : ℕ) : ℝ) η) := by
  let j := carrierIncl38 (show ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
  have h := (B).canonical (j x) (j ξ) (j η)
  have hξ := (B).fderiv_TC_compat_coe 0 1 (by omega) x ξ
  have hη := (B).fderiv_TC_compat_coe 0 1 (by omega) x η
  change stdSymplectic38
      (carrierCoe38 ((0 : ℕ) : ℝ) (fderiv ℝ ((B0).TC 0) (j x) (j ξ)))
      (carrierCoe38 ((0 : ℕ) : ℝ) (fderiv ℝ ((B0).TC 0) (j x) (j η))) = _ at h
  rw [hξ, hη] at h
  simpa only [j, carrierCoe38_incl38] using h

/-- Differentiating the actual inverse identity at h¹ gives the precise
inverse tangent used in finite Hamiltonian transport. -/
theorem actual_TC1_TinvC1_fderiv38 (z e : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    fderiv ℝ ((B0).TC 1) ((B0).TinvC 1 z)
      (fderiv ℝ ((B0).TinvC 1) z e) = e := by
  have hi := ((B).analyticOnNhd_TinvC 1 z (Set.mem_univ z)).differentiableAt.hasFDerivAt
  have hf := ((B).analyticOnNhd_TC 1 ((B0).TinvC 1 z)
    (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hh := hf.comp z hi
  have he : (B0).TC 1 ∘ (B0).TinvC 1 = id := funext ((B0).TC_TinvC 1)
  rw [he] at hh
  exact congrArg (fun L => L e) (hh.unique (hasFDerivAt_id z))

/-- The literal physical energy HΛ agrees with the reflected actual inverse
h¹-carrier expression, for every finite-plane point. -/
theorem HΛ_eq_inverseCarrier38 (Λ : Finset ℤ) (w : Λ → ℂ) :
    HΛ Λ w = ham (carrierCoe38 ((1 : ℕ) : ℝ)
      (reflIso38 ((1 : ℕ) : ℝ) ((B0).TinvC 1 (finitePlaneInsert38 Λ w)))) := by
  unfold HΛ
  congr 1
  have he : fourierSeq38 ((B0).finiteGapField38 Λ w) =
      (B0).Tinv (extZero38 Λ w) := by
    rw [BirkhoffTop38.finiteGapField38,
      (B0).cleanΦinv_of_mem _ (extZero38_mem_zero Λ w), (B0).fourierSeq38_Φinv]
  funext n
  change physicalFourier ((B0).finiteGapField38 Λ w) n =
    -carrierCoe38 ((1 : ℕ) : ℝ) ((B0).TinvC 1 (finitePlaneInsert38 Λ w)) (-n)
  rw [BirkhoffTop38.TinvC_coe, finitePlaneInsert38_coe]
  have hn := congrFun he (-n)
  rw [fourierSeq38_apply, neg_neg] at hn
  simpa only [neg_neg] using congrArg Neg.neg hn

end LiebLiniger.FixedPeriod.EXT
