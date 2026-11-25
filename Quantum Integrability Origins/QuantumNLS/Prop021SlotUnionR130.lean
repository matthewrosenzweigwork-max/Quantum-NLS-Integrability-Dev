import QuantumNLS.Prop021OneParticleR130
import QuantumNLS.Prop021ProjectionUnionR128

/-! Physical tensor-slot condensate projections, their exact bosonic
symmetry defect, and the square-root-in-k union bound. The identification
of their ordered product with the k-factor projector remains separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 10000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop021SlotUnionR130
open TensorCarrier TensorFourier Prop021ExcitationR130 Prop021OneParticleR130
open Prop021ProjectionUnionR128
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma block_projection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (P : E →L[ℂ] E) (hP : IsStarProjection P)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    IsStarProjection (htmap P (ContinuousLinearMap.id ℂ F)) := by
  constructor
  · have hmul : P ∘L P = P := hP.isIdempotentElem.eq
    change htmap P (ContinuousLinearMap.id ℂ F) ∘L htmap P (ContinuousLinearMap.id ℂ F) = _
    rw [← htmap_comp,hmul,ContinuousLinearMap.comp_id]
  · change (htmap P (ContinuousLinearMap.id ℂ F)).adjoint = _
    rw [adjoint_htmap,hP.isSelfAdjoint.adjoint_eq,ContinuousLinearMap.adjoint_id]

def conjugate {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (e : E ≃ₗᵢ[ℂ] F) (P : E →L[ℂ] E) : F →L[ℂ] F :=
  e.toLinearIsometry.toContinuousLinearMap ∘L P ∘L e.symm.toLinearIsometry.toContinuousLinearMap

lemma conjugate_projection {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (e : E ≃ₗᵢ[ℂ] F) (P : E →L[ℂ] E) (hP : IsStarProjection P) :
    IsStarProjection (conjugate e P) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change e (P (e.symm (e (P (e.symm x))))) = e (P (e.symm x))
    rw [LinearIsometryEquiv.symm_apply_apply]
    have h := congrArg (fun T : E →L[ℂ] E => T (e.symm x)) hP.isIdempotentElem.eq
    exact congrArg e h
  · change (conjugate e P).adjoint = conjugate e P
    simp only [conjugate,ContinuousLinearMap.adjoint_comp,GenericUAdjoint.adjoint_iso,
      LinearIsometryEquiv.symm_symm,hP.isSelfAdjoint.adjoint_eq,ContinuousLinearMap.comp_assoc]

/-- The literal first-factor condensate projection on the full tensor power. -/
def firstProjection (u : H) (m : ℕ) : HilbertTensorPower ℂ H (1+m) →L[ℂ] HilbertTensorPower ℂ H (1+m) :=
  blockPlacement 1 m (InnerProductSpace.rankOne ℂ (htpow 1 u : HilbertTensorPower ℂ H 1) (htpow 1 u))

lemma prefix_projection (u : H) (hu : ‖u‖=1) (m : ℕ) : IsStarProjection (firstProjection u m) := by
  have hp := InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ)
    (by rw [norm_htpow,hu,one_pow] : ‖(htpow 1 u : HilbertTensorPower ℂ H 1)‖=1)
  have ht := block_projection _ hp (F := HilbertTensorPower ℂ H m)
  have he : firstProjection u m = conjugate (splitIsometry (𝕜 := ℂ) (E := H) 1 m).symm
      (htmap (InnerProductSpace.rankOne ℂ (htpow 1 u : HilbertTensorPower ℂ H 1) (htpow 1 u))
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m))) := by
    ext x
    rfl
  rw [he]
  exact conjugate_projection _ _ ht

/-- Relocate that actual projection to the indicated tensor factor. -/
def slot (u : H) (m : ℕ) (i : Fin (1+m)) :
    HilbertTensorPower ℂ H (1+m) →L[ℂ] HilbertTensorPower ℂ H (1+m) :=
  conjugate (permHilbertIsometry (Equiv.swap 0 i)) (firstProjection u m)

lemma slot_projection (u : H) (hu : ‖u‖=1) (m : ℕ) (i : Fin (1+m)) :
    IsStarProjection (slot u m i) :=
  conjugate_projection (permHilbertIsometry (Equiv.swap 0 i)) (firstProjection u m)
    (prefix_projection u hu m)

/-- An actual complex orthogonal projection gives R128's real Hilbert
projection, with both algebraic properties proved. -/
def realProjection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : E →L[ℂ] E) (hP : IsStarProjection P) : OrthogonalMap E where
  map := P.restrictScalars ℝ
  symmetric x y := by
    change (⟪x,P y⟫_ℂ).re = (⟪P x,y⟫_ℂ).re
    have h := congrArg Complex.re (P.adjoint_inner_right x y)
    rwa [hP.isSelfAdjoint.adjoint_eq] at h
  idempotent x := congrArg (fun T : E →L[ℂ] E => T x) hP.isIdempotentElem.eq

/-- The exact normalized excitation root measures the first-factor defect.
This identity does not require x to have unit norm. -/
theorem prefix_defect (u : H) (hu : ‖u‖=1) (m : ℕ) (x : SymSector ℂ H (1+m)) :
    ‖x.val-firstProjection u m x.val‖^2 = ‖contraction u (1+m) x‖^2 := by
  rw [contraction_expectation u hu,average_U,inner_U,first_q,inner_sub_right,Complex.sub_re]
  have he := (realProjection _ (prefix_projection u hu m)).defect_expectation x.val
  change ‖x.val-firstProjection u m x.val‖^2 = ‖x.val‖^2-(⟪x.val,firstProjection u m x.val⟫_ℂ).re at he
  have hn : (⟪x.val,x.val⟫_ℂ).re = ‖x.val‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x.val).symm
  rw [hn]
  exact he

/-- Bosonic permutation invariance gives the SAME excitation defect in
every tensor slot. No symmetry-to-depletion identification is assumed. -/
theorem slot_defect (u : H) (hu : ‖u‖=1) (m : ℕ) (x : SymSector ℂ H (1+m))
    (i : Fin (1+m)) : ‖x.val-slot u m i x.val‖ = ‖contraction u (1+m) x‖ := by
  let e := permHilbertIsometry (𝕜 := ℂ) (E := H) (Equiv.swap (0:Fin (1+m)) i)
  have hf : e x.val=x.val := x.property (Equiv.swap 0 i)
  have hi : e.symm x.val=x.val := by
    apply e.injective
    rw [LinearIsometryEquiv.apply_symm_apply,hf]
  have hn : ‖x.val-slot u m i x.val‖ = ‖x.val-firstProjection u m x.val‖ := by
    change ‖x.val-e (firstProjection u m (e.symm x.val))‖ = _
    rw [hi]
    have he : x.val-e (firstProjection u m x.val) = e (x.val-firstProjection u m x.val) := by
      rw [map_sub,hf]
    rw [he,e.norm_map]
  rw [hn]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (prefix_defect u hu m x)

/-- Any chosen k slots, including the first k, obey the actual tensor
projection union estimate with exactly sqrt(k) times the excitation norm. -/
theorem physical_slot_union (u : H) (hu : ‖u‖=1) (m : ℕ)
    (x : SymSector ℂ H (1+m)) (indices : List (Fin (1+m))) :
    ‖x.val-projectList (indices.map fun i => realProjection (slot u m i) (slot_projection u hu m i)) x.val‖ ≤
      Real.sqrt (indices.length:ℝ)*‖contraction u (1+m) x‖ := by
  have h := projection_union_uniform
    (indices.map fun i => realProjection (slot u m i) (slot_projection u hu m i)) x.val
    (norm_nonneg (contraction u (1+m) x)) (by
      intro P hP
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hP
      exact (slot_defect u hu m x i).le)
  simpa only [List.length_map] using h

end QuantumNLS.Prop021SlotUnionR130
#print axioms QuantumNLS.Prop021SlotUnionR130.prefix_defect
#print axioms QuantumNLS.Prop021SlotUnionR130.slot_defect
#print axioms QuantumNLS.Prop021SlotUnionR130.physical_slot_union

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021SlotUnionR130"].any
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
