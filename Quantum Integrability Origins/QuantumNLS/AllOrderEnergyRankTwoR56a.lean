import QuantumNLS.AllOrderEnergyMarginalToolsR56a
import QuantumNLS.Ext025HGP09

/-! The physical rank-two contact identity and its intensive-energy consequence. -/

set_option autoImplicit false
noncomputable section

section
/-! First-pair contact via the positive kinetic sandwich of the actual
rank-two marginal. The Fourier test verifies the literal collision pairing
on trigonometric polynomials and passes to the H¹ closure. -/
set_option maxHeartbeats 6000000
open Filter Topology
open scoped InnerProductSpace ENNReal BigOperators
namespace QuantumNLS.AllOrderEnergyMarginalContactR56a
open Energy EnergyPreparationDef PhysicalEnergy PhysicalTensor TensorCarrier
open MarginalEnergy TraceClass CollisionTrace CollisionIdentification EnergyContactTrace Ext025B10EnergyFamily
open AllOrderEnergyPairR56a AllOrderEnergyPartialRootR56a
open Ext025A12Normal Ext025A12PartialTrace Ext025B11TracePairing Ext025A12Trace
variable {L : ℝ} [Fact (0 < L)]

def left (m : ℕ) : Fin (2+m) := Fin.castAdd m 0
def right (m : ℕ) : Fin (2+m) := Fin.castAdd m 1
theorem left_ne_right (m : ℕ) : left m ≠ right m := by
  intro h
  have he := congrArg Fin.val h
  change (0 : ℕ) = 1 at he
  omega

private theorem rest_two_empty (p : Rest 2 0 1) : False := by
  obtain ⟨i, hi, hj⟩ := p
  fin_cases i <;> contradiction

private def spectator (m : ℕ) : Fin m ≃ Rest (2+m) (left m) (right m) where
  toFun j := ⟨Fin.natAdd 2 j, by
    constructor <;> intro h <;> have he := congrArg Fin.val h
    · change 2 + j.val = 0 at he
      omega
    · change 2 + j.val = 1 at he
      omega⟩
  invFun p := ⟨p.val.val - 2, by
    have h := p.val.isLt
    have h0 : p.val.val ≠ 0 := fun he => p.property.1 (Fin.ext he)
    have h1 : p.val.val ≠ 1 := fun he => p.property.2 (Fin.ext he)
    omega⟩
  left_inv j := by apply Fin.ext; change 2 + j.val - 2 = j.val; omega
  right_inv p := by
    apply Subtype.ext
    apply Fin.ext
    have h0 : p.val.val ≠ 0 := fun h => p.property.1 (Fin.ext h)
    have h1 : p.val.val ≠ 1 := fun h => p.property.2 (Fin.ext h)
    change 2 + (p.val.val - 2) = p.val.val
    omega

private def contactLabels (m : ℕ) :
    (TIdx 2 0 1 × Mom m) ≃ TIdx (2+m) (left m) (right m) where
  toFun p := (p.1.1, fun j => p.2 ((spectator m).symm j))
  invFun p := ((p.1, fun j => (rest_two_empty j).elim), fun j => p.2 (spectator m j))
  left_inv p := by
    apply Prod.ext
    · exact Prod.ext rfl (funext fun j => (rest_two_empty j).elim)
    · funext j
      change p.2 ((spectator m).symm (spectator m j)) = p.2 j
      rw [Equiv.symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext j
      change p.2 (spectator m ((spectator m).symm j)) = p.2 j
      rw [Equiv.apply_symm_apply]

private theorem contactLabels_collapse {m : ℕ} (w : Mom 2) (v : Mom m) :
    contactLabels m (collapse 0 1 w, v) = collapse (left m) (right m) (Fin.append w v) := by
  apply Prod.ext
  · change w 0 + w 1 = Fin.append w v (Fin.castAdd m 0) + Fin.append w v (Fin.castAdd m 1)
    rw [Fin.append_left, Fin.append_left]
  · funext j
    obtain ⟨i, rfl⟩ := (spectator m).surjective j
    change v ((spectator m).symm (spectator m i)) = Fin.append w v (Fin.natAdd 2 i)
    rw [Equiv.symm_apply_apply, Fin.append_right]

private theorem seqCongr_single {A B : Type*} [DecidableEq A] [DecidableEq B] (e : A ≃ B) (a : A) :
    seqCongr e (lp.single (E := fun _ => ℂ) 2 a 1) = lp.single (E := fun _ => ℂ) 2 (e a) 1 := by
  apply Subtype.ext
  funext b
  change lp.single (E := fun _ => ℂ) 2 a 1 (e.symm b) = lp.single (E := fun _ => ℂ) 2 (e a) 1 b
  classical
  by_cases h : b = e a
  · subst b
    simp [lp.single_apply]
  · have h' : e.symm b ≠ a := fun he => h (e.symm_apply_eq.mp he)
    simp [lp.single_apply, h, h']

private theorem prefixRoot_single (m : ℕ) (w : Mom 2) (v : Mom m) :
    prefixRoot (trigElem (L := L) {Fin.append w v} (fun _ => 1)) =
      (kinSqrt L 2 w : ℂ) • mode (2+m) (Fin.append w v) := by
  classical
  apply (eK L (2+m)).injective
  ext a
  rw [prefixRoot_coeff, momUnitary_trigElem, finVec_apply, map_smul,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp only [mode, LinearIsometryEquiv.apply_symm_apply, ev_eq_single]
  change _ = _ * lp.single (E := fun _ => ℂ) 2 (Fin.append w v) 1 a
  by_cases ha : a = Fin.append w v
  · subst a
    have hw : (fun i : Fin 2 => Fin.append w v (Fin.castAdd m i)) = w :=
      funext fun i => Fin.append_left w v i
    simp [Finset.mem_singleton, lp.single_apply]
  · simp [ha, Finset.mem_singleton, lp.single_apply]

private theorem fullRoot_single (w : Mom 2) :
    AhalfT L 2 (toHalf (trigElem (L := L) {w} (fun _ => 1))) =
      (kinSqrt L 2 w : ℂ) • mode 2 w := by
  classical
  apply (eK L 2).injective
  ext a
  rw [eK_AhalfT, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp only [mode, LinearIsometryEquiv.apply_symm_apply, ev_eq_single]
  rw [eK_apply]
  change (kinSqrt L 2 a : ℂ) * (momUnitary L 2 (physUnitary
    (physUnitary.symm (trigElem (L := L) {w} (fun _ => 1)).val))) a =
      _ * lp.single (E := fun _ => ℂ) 2 w 1 a
  rw [LinearIsometryEquiv.apply_symm_apply, momUnitary_trigElem, finVec_apply]
  by_cases ha : a = w
  · subst a
    simp [lp.single_apply]
  · simp [ha, lp.single_apply]

private theorem split_mode (m : ℕ) (w : Mom 2) (v : Mom m) :
    splitIsometry 2 m (mode (L := L) (2+m) (Fin.append w v)) =
      htmul (mode 2 w) (mode m v) := by
  rw [mode_eq_ptprod, mode_eq_ptprod, mode_eq_ptprod,
    ← splitIsometry_ptprod_append, append_modes]

private def outputBasis :
    HilbertBasis (TIdx 2 0 1) ℂ (CollisionProductL2 (L := L) (0 : Fin 2) 1) :=
  HilbertBasis.ofRepr (collisionProductUnitary (L := L) (0 : Fin 2) 1).symm

private def contactOutput (m : ℕ) :
    HilbertTensor ℂ (CollisionProductL2 (L := L) (0 : Fin 2) 1) (Xk L m) ≃ₗᵢ[ℂ]
      L2 (TIdx (2+m) (left m) (right m)) :=
  (htmulBasis (outputBasis (L := L)) (modeBasis (L := L) m)).repr.trans
    (seqCongr (contactLabels m))

private theorem contactOutput_mode (m : ℕ) (a : TIdx 2 0 1) (v : Mom m) :
    contactOutput (L := L) m
      (htmul (collisionProductUnitary (L := L) (0 : Fin 2) 1 (lp.single (E := fun _ => ℂ) 2 a 1)) (mode m v)) =
    lp.single (E := fun _ => ℂ) 2 (contactLabels m (a,v)) 1 := by
  let B := htmulBasis (outputBasis (L := L)) (modeBasis (L := L) m)
  have ha : outputBasis (L := L) a =
      collisionProductUnitary (L := L) (0 : Fin 2) 1 (lp.single (E := fun _ => ℂ) 2 a 1) :=
    ((outputBasis (L := L)).repr_symm_single a).symm
  have hb : B (a,v) = htmul (outputBasis (L := L) a) (modeBasis (L := L) m v) :=
    htmulBasis_apply _ _ (a,v)
  rw [← ha, ← modeBasis_apply, ← hb]
  change seqCongr (contactLabels m) (B.repr (B (a,v))) = _
  rw [B.repr_self, seqCongr_single]

private theorem sop_unitary (x : PhysH1 L 2) :
    Sop (by decide : (0 : Fin 2) ≠ 1) (PhysH1.unitary x) =
      productTrace (0 : Fin 2) 1 (by decide) x := by
  let e := PhysH1.unitary (L := L) (k := 2)
  change productTrace (0 : Fin 2) 1 (by decide) (e.symm (e x)) =
    productTrace (0 : Fin 2) 1 (by decide) x
  rw [e.symm_apply_apply]

set_option maxRecDepth 2048 in
private theorem contact_amplification (m : ℕ) (x : PhysH1 L (2+m)) :
    ‖htmap (contactRoot (L := L) (0 : Fin 2) 1 (by decide))
      (ContinuousLinearMap.id ℂ (Xk L m)) (splitIsometry 2 m (prefixRoot x))‖ =
    ‖productTrace (left m) (right m) (left_ne_right m) x‖ := by
  let S := contactRoot (L := L) (0 : Fin 2) 1 (by decide)
  let B := htmap S (ContinuousLinearMap.id ℂ (Xk L m))
  let F := (contactOutput (L := L) m).toContinuousLinearEquiv.toContinuousLinearMap ∘L B ∘L
    (splitIsometry 2 m).toContinuousLinearEquiv.toContinuousLinearMap ∘L prefixRootMap
  have hF : F = traceCLM (L := L) (left m) (right m) (left_ne_right m) := by
      apply traceCLM_unique
      intro U c
      rw [trigElem_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, map_smul]
      have hp : ∃ (w : Mom 2) (v : Mom m), a = Fin.append w v := by
        refine ⟨fun j => a (Fin.castAdd m j), fun j => a (Fin.natAdd 2 j), ?_⟩
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · rw [Fin.append_left]
        · rw [Fin.append_right]
      obtain ⟨w, v, rfl⟩ := hp
      change (c (Fin.append w v)) • contactOutput m
        (htmap S (ContinuousLinearMap.id ℂ (Xk L m))
          (splitIsometry 2 m (prefixRoot (trigElem {Fin.append w v} (fun _ => 1))))) =
          (c (Fin.append w v)) •
            traceCLM (left m) (right m) (left_ne_right m) (trigElem {Fin.append w v} (fun _ => 1))
      apply congrArg ((c (Fin.append w v)) • ·)
      rw [prefixRoot_single, map_smul, split_mode, map_smul, htmap_htmul,
        ContinuousLinearMap.id_apply, ← htmul_smul_left, ← map_smul, ← fullRoot_single]
      change contactOutput m
        (htmul (Sop (by decide : (0 : Fin 2) ≠ 1)
          (physUnitary (AhalfT L 2 (toHalf (trigElem {w} (fun _ => 1)))))) (mode m v)) = _
      rw [root_toHalf, sop_unitary]
      simp only [productTrace, ContinuousLinearMap.comp_apply]
      rw [traceCLM_single, traceCLM_single, map_smul, htmul_smul_left, map_smul]
      have hmodes := contactOutput_mode (L := L) m (collapse 0 1 w) v
      rw [contactLabels_collapse w v] at hmodes
      exact congrArg (fun q : L2 (TIdx (2+m) (left m) (right m)) =>
        (((Real.sqrt L)⁻¹ : ℝ) : ℂ) • q) hmodes
  have h := congrArg (fun A : PhysH1 L (2+m) →L[ℂ] L2 (TIdx (2+m) (left m) (right m)) =>
    ‖A x‖) hF
  change ‖contactOutput m (B (splitIsometry 2 m (prefixRoot x)))‖ = _ at h
  rw [LinearIsometryEquiv.norm_map, ← productTrace_norm _ _ (left_ne_right m)] at h
  exact h

private theorem separableMode (k : ℕ) : TopologicalSpace.SeparableSpace (Xk L k) := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  let b := modeBasis (L := L) k
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  rw [← hd.closure_eq]
  exact ((Set.countable_range b).isSeparable.span (R := ℂ)).closure

/-- The trace of the rank-two contact against the actual positive sandwich
equals the many-body pair contact integral. -/
theorem rank_two_contact (m : ℕ) (x : PhysH1 L (2+m))
    (ρ : FiniteEnergy L 2)
    (hρ : ρ.val = reducedDensityPower 2 m (toHalf x : Xk L (2+m))) :
    (EnergyFormPass.expectation (contactSandwich (0 : Fin 2) 1 (by decide)) ρ).re =
      ‖productTrace (left m) (right m) (left_ne_right m) x‖^2 := by
  let z := splitIsometry 2 m (prefixRoot x)
  let S := contactRoot (L := L) (0 : Fin 2) 1 (by decide)
  let K := contactSandwich (L := L) (0 : Fin 2) 1 (by decide)
  let P := InnerProductSpace.rankOne ℂ z z
  have ht : IsTraceClass P := (Fidelity.traceNorm_rankOne_le z z).trans_lt ENNReal.ofReal_lt_top
  have hp : partialTrace P ht = reducedDensity z := partialTrace_rankOne z ht
  have hreal : IsFormRealization ρ.val (reducedDensity z) := by
    rw [hρ]
    exact marginal_root_realizes x
  rw [EnergyFormPassFinal.expectation_realization K ρ (reducedDensity z) hreal, ← hp]
  have htc := partialTrace_isTraceClass P ht
  letI := separableMode (L := L) 2
  letI := separableMode (L := L) m
  obtain ⟨_, _, _, _, _, _, _, hb, hcycle, _, _⟩ :=
    Ext025HGP09.contract_GP09.{0,0,0,0,0,0,0,0,0,0} (E := Xk L 2) (X := Xk L 2) (Y := Xk L m)
  rw [hcycle _ K _ htc, hb (Ext025B10PhysicalEnergy.basis L 2)
    (refBasis (Xk L 2)) (partialTrace P ht * K) (finite_right K _ htc)]
  change (tr (partialTrace P ht * K)).re = _
  rw [partialTrace_duality P ht K, tr, trace_rankOne_right]
  let A := htmap S (ContinuousLinearMap.id ℂ (Xk L m))
  have hA : TensorCarrier.ampliate ℂ (Xk L 2) (Xk L m) K = A.adjoint.comp A := by
    simp only [TensorCarrier.ampliate_apply, A, adjoint_htmap, ContinuousLinearMap.adjoint_id,
      ← htmap_comp, ContinuousLinearMap.comp_id, K, contactSandwich, S]
  rw [hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  change RCLike.re ⟪A z, A z⟫_ℂ = _
  rw [← norm_sq_eq_re_inner, contact_amplification]

end QuantumNLS.AllOrderEnergyMarginalContactR56a
end

section
/-! The intensive energy identity on positive rank-one and rank-two
marginals of the same symmetric form-domain wave function. -/
set_option maxHeartbeats 5000000
open scoped ENNReal
namespace QuantumNLS.AllOrderEnergyIdentityR56a
open EnergyPreparationDef PhysicalEnergy PhysicalTensor TensorCarrier CollisionIdentification
open AllOrderEnergyPairR56a AllOrderEnergyPhysicalR56a AllOrderEnergyMarginalContactR56a
variable {L : ℝ} [Fact (0 < L)]

/-- The finite-particle factor accompanies the literal rank-two energy
trace; the rank-one trace gives the kinetic term after subtracting one. -/
theorem marginal_energy_identity {N : ℕ} (hk : 2 ≤ N) (κ : ℝ)
    (ψ : Xk L N) (hψ : ‖ψ‖ = 1) (x : PhysH1 L N)
    (hx : x.val = physUnitary ψ) (hsym : x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) :
    hN κ N x / N =
      ((energyTrace (marginal (by omega : 1 ≤ N) ψ x hx).val).toReal - 1) +
      κ * (1 - (N : ℝ)⁻¹) *
        (EnergyFormPass.expectation (contactSandwich (L := L) (0 : Fin 2) 1 (by decide))
          (marginal hk ψ x hx)).re := by
  obtain ⟨m, hN⟩ : ∃ m, N = 2 + m := ⟨N - 2, by omega⟩
  subst N
  have hval : (toHalf x : Xk L (2+m)) = ψ := by
    change physUnitary.symm x.val = ψ
    rw [hx, LinearIsometryEquiv.symm_apply_apply]
  have hDensity : (marginal hk ψ x hx).val = reducedDensityPower 2 m (toHalf x : Xk L (2+m)) := by
    rw [hval]
    change reducedDensityN (2+m) 2 hk ψ = _
    have hcast (n : ℕ) (e : 2 + m = 2 + n) :
        reducedDensityPower 2 n (castHTP e ψ) = reducedDensityPower 2 m ψ := by
      have hn : n = m := by omega
      subst n
      rfl
    exact hcast _ _
  let a := left m
  rw [rank_two_contact m x _ hDensity, marginal_energy_sym _ ψ x hx hψ hsym a,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 + ↑(1 : ℕ) * ‖gradientCLM a x‖ ^ 2),
    intensive_energy κ hsym a (right m) (left_ne_right m)]
  push_cast
  ring

end QuantumNLS.AllOrderEnergyIdentityR56a
end

set_option maxHeartbeats 22000000 in
run_cmd do
  let env ← Lean.getEnv
  let prefixes := ["QuantumNLS.AllOrderEnergyIdentityR56a.", "QuantumNLS.AllOrderEnergyMarginalContactR56a."]
  let mut pending := env.constants.toList.filterMap fun (n, _) =>
    if prefixes.any (fun pre => n.toString.startsWith pre) ||
      n.toString.startsWith "_private.QuantumNLS.AllOrderEnergyRankTwoR56a." then some n else none
  let roots := pending.length
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      if n == ``QuantumNLS.AllOrderEnergyInputsR55a.ActualModelRE679E41DInput ||
          n == ``QuantumNLS.AllOrderEnergyInputsR55a.flows ||
          n == ``QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional ||
          n == ``QuantumNLS.ActualModelCorollaryR53a.PacketEstimate then
        throwError "Unaccepted predecessor representation: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := ci.type.getUsedConstants.toList ++ pending
        if let some v := ci.value? (allowOpaque := true) then
          pending := v.getUsedConstants.toList ++ pending
      else throwError "Missing dependency: {n}"
  Lean.logInfo m!"R56a audit PASS: {roots} namespace constants; {seen.size} transitive constants."
