import QuantumNLS.Prop021ExcitationR130
import QuantumNLS.Prop021MarginalR128
import QuantumNLS.TensorFourier

/-! Exact one-particle marginal/depletion binding, on arbitrary complex
Hilbert space. Higher-k tensor union identification is not claimed here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 10000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Prop021OneParticleR130
open TensorCarrier TensorPlacements KernelDefinition TensorFourier PhysicalTensor TraceClass
open Prop021ExcitationR130
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma symSector_one : SymSector ℂ H 1 = ⊤ := by
  apply top_unique
  intro x _ σ
  rw [Subsingleton.elim σ 1, map_one]
  rfl

lemma symProj_one (x : HilbertTensorPower ℂ H 1) : symProj ℂ H 1 x = x := by
  rw [symProj_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr (by rw [symSector_one]; trivial)

lemma extend_q (u : H) : extendSymKernel (q u) =
    1-InnerProductSpace.rankOne ℂ (htpow 1 u : HilbertTensorPower ℂ H 1) (htpow 1 u) := by
  apply ContinuousLinearMap.ext
  intro x
  change ((q u) (symProjToSector 1 x)).val = _
  simp only [q,sub_apply,one_apply_eq_self,InnerProductSpace.rankOne_apply,
    Submodule.coe_sub,Submodule.coe_smul,condensate]
  change symProj ℂ H 1 x - ⟪(htpow 1 u : HilbertTensorPower ℂ H 1),symProj ℂ H 1 x⟫_ℂ • htpow 1 u = _
  rw [symProj_one]
  rfl

def ampliateLinear (m : ℕ) :
    (HilbertTensorPower ℂ H 1 →L[ℂ] HilbertTensorPower ℂ H 1) →ₗ[ℂ]
      (HilbertTensor ℂ (HilbertTensorPower ℂ H 1) (HilbertTensorPower ℂ H m) →L[ℂ]
       HilbertTensor ℂ (HilbertTensorPower ℂ H 1) (HilbertTensorPower ℂ H m)) where
  toFun A := htmap A (ContinuousLinearMap.id ℂ _)
  map_add' A B := htmap_add_left A B _
  map_smul' c A := htmap_smul_left c A _

lemma first_q (u : H) (m : ℕ) (x : HilbertTensorPower ℂ H (1+m)) :
    firstPlacement (q := m) (q u) x =
      x - blockPlacement 1 m (InnerProductSpace.rankOne ℂ
        (htpow 1 u : HilbertTensorPower ℂ H 1) (htpow 1 u)) x := by
  apply (splitIsometry (𝕜 := ℂ) (E := H) 1 m).injective
  have he : firstPlacement (q := m) (q u) = blockPlacement 1 m (extendSymKernel (q u)) := by
    ext y
    rfl
  rw [he,split_blockPlacement,extend_q]
  have hs := (ampliateLinear (H := H) m).map_sub
    (1 : HilbertTensorPower ℂ H 1 →L[ℂ] HilbertTensorPower ℂ H 1)
    (InnerProductSpace.rankOne ℂ (htpow 1 u) (htpow 1 u))
  change htmap (1-InnerProductSpace.rankOne ℂ (htpow 1 u) (htpow 1 u)) (ContinuousLinearMap.id ℂ _) = _ at hs
  rw [hs,sub_apply,map_sub,split_blockPlacement]
  have hi := congrArg (fun T => T (splitIsometry (𝕜 := ℂ) (E := H) 1 m x))
    (Ext025A12Tensor.ampliate_one (X := HilbertTensorPower ℂ H 1) (Y := HilbertTensorPower ℂ H m))
  exact congrArg (fun y => y-htmap (InnerProductSpace.rankOne ℂ
    (htpow 1 u : HilbertTensorPower ℂ H 1) (htpow 1 u)) (ContinuousLinearMap.id ℂ _) (splitIsometry 1 m x)) hi

lemma inner_U (u : H) (m : ℕ) (x : SymSector ℂ H (1+m)) :
    ⟪x,U_N_r (q := m) (q u) x⟫_ℂ = ⟪x.val,firstPlacement (q := m) (q u) x.val⟫_ℂ := by
  rw [U_N_r_eq_sandwich]
  change ⟪x.val,symProj ℂ H (1+m) (firstPlacement (q u) (symProj ℂ H (1+m) x.val))⟫_ℂ = _
  rw [inner_symProj_of_mem, symProj_eq_starProjection,
    Submodule.starProjection_eq_self_iff.mpr x.property]

lemma cast_U (p n r : ℕ) (h : n=r)
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    castSymSectorOperator (congrArg (fun k => p+k) h) (U_N_r (q := n) A) = U_N_r (q := r) A := by
  cases h
  rfl

lemma average_U (u : H) (m : ℕ) :
    average u (1+m) = U_N_r (q := m) (q u) := by
  have hm : 1+m-1=m := by omega
  unfold average
  rw [dite_eq_left (show 1 ≤ 1+m by omega)]
  exact cast_U 1 (1+m-1) m hm (q u)

/-- Exact one-particle reduced-density fidelity defect equals the actual
normalized excitation expectation, with no symmetry/depletion input. -/
theorem density_defect_add (u : H) (hu : ‖u‖=1) (m : ℕ)
    (x : SymSector ℂ H (1+m)) (hx : ‖x‖=1) :
    1-(⟪(htpow 1 u : HilbertTensorPower ℂ H 1),
      reducedDensityPower 1 m x.val (htpow 1 u)⟫_ℂ).re =
      ‖contraction u (1+m) x‖^2 := by
  rw [contraction_expectation u hu,average_U,inner_U,first_q,inner_sub_right]
  have hself : (⟪x.val,x.val⟫_ℂ).re = 1 := by
    have hi : ‖x.val‖^2 = (⟪x.val,x.val⟫_ℂ).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) x.val
    calc
      _ = ‖x.val‖^2 := hi.symm
      _ = 1 := by change ‖x‖^2=1; rw [hx]; norm_num
  have hd : (⟪(htpow 1 u : HilbertTensorPower ℂ H 1),
      reducedDensityPower 1 m x.val (htpow 1 u)⟫_ℂ).re =
      (⟪x.val,blockPlacement 1 m (InnerProductSpace.rankOne ℂ
        (htpow 1 u : HilbertTensorPower ℂ H 1) (htpow 1 u)) x.val⟫_ℂ).re := by
    have hr : (⟪(htpow 1 u : HilbertTensorPower ℂ H 1),
        reducedDensityPower 1 m x.val (htpow 1 u)⟫_ℂ).re =
        (⟪reducedDensityPower 1 m x.val (htpow 1 u),htpow 1 u⟫_ℂ).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [hr]
    change (⟪reducedDensity (splitIsometry 1 m x.val) (htpow 1 u),htpow 1 u⟫_ℂ).re = _
    have hred := inner_reducedDensity_left (𝕜 := ℂ) (splitIsometry 1 m x.val)
      (htpow 1 u) (htpow 1 u)
    have hmap := (splitIsometry (𝕜 := ℂ) (E := H) 1 m).inner_map_map x.val
      (blockPlacement 1 m (InnerProductSpace.rankOne ℂ (htpow 1 u) (htpow 1 u)) x.val)
    rw [split_blockPlacement] at hmap
    exact (congrArg Complex.re hred).trans (congrArg Complex.re hmap)
  simp only [Complex.sub_re]
  rw [hself,hd]

lemma cast_reduced (p n r : ℕ) (h : n=r) (x : HilbertTensorPower ℂ H (p+r)) :
    reducedDensityPower p n (castHTP (congrArg (fun k => p+k) h.symm) x) =
      reducedDensityPower p r x := by
  cases h
  rfl

/-- Literal DEF-030 packaging for every positive N. -/
theorem density_defect (u : H) (hu : ‖u‖=1) (N : ℕ) (hN : 1 ≤ N)
    (x : SymSector ℂ H N) (hx : ‖x‖=1) :
    1-(⟪(htpow 1 u : HilbertTensorPower ℂ H 1),
      reducedDensityN N 1 hN x.val (htpow 1 u)⟫_ℂ).re =
      ‖contraction u N x‖^2 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hN
  have hm : 1+m-1=m := by omega
  have hr : reducedDensityN (1+m) 1 hN x.val = reducedDensityPower 1 m x.val :=
    cast_reduced 1 (1+m-1) m hm x.val
  rw [hr]
  exact density_defect_add u hu m x hx

/-- The k=1 printed trace-distance estimate with the actual excitation
root. No assumed marginal or dGamma identification is present. -/
theorem oneParticle_distance (u : H) (hu : ‖u‖=1) (N : ℕ) (hN : 1 ≤ N)
    (x : SymSector ℂ H N) (hx : ‖x‖=1) :
    traceNorm (reducedDensityN N 1 hN x.val-
      InnerProductSpace.rankOne ℂ (htpow 1 u : HilbertTensorPower ℂ H 1) (htpow 1 u)) ≤
      ENNReal.ofReal (2*‖contraction u N x‖) := by
  have h := Prop021MarginalR128.marginal_fidelity N 1 hN x.val hx u hu
  have hd : 1-(⟪(htpow 1 u : HilbertTensorPower ℂ H 1),
      reducedDensityN N 1 hN x.val (htpow 1 u)⟫_ℂ).re = ‖contraction u N x‖^2 :=
    density_defect u hu N hN x hx
  have he : Real.sqrt (1-(⟪(htpow 1 u : HilbertTensorPower ℂ H 1),
      reducedDensityN N 1 hN x.val (htpow 1 u)⟫_ℂ).re) = ‖contraction u N x‖ :=
    (congrArg Real.sqrt hd).trans (Real.sqrt_sq (norm_nonneg _))
  exact h.trans_eq (congrArg ENNReal.ofReal (congrArg (fun r : ℝ => 2*r) he))

end QuantumNLS.Prop021OneParticleR130
#print axioms QuantumNLS.Prop021OneParticleR130.density_defect
#print axioms QuantumNLS.Prop021OneParticleR130.oneParticle_distance

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021OneParticleR130"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R130 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
