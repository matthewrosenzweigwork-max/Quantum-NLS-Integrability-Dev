import QuantumNLS.Prop022AIsoTensor
import QuantumNLS.Prop022ACovTensor
import QuantumNLS.PhysicalTensor

/-! Reduced densities and trace distances under an isometric one-particle embedding. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Prop021MarginalTransportR132
open TensorCarrier PhysicalTensor TraceClass Prop022AIsoTensor

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Zero extension along a linear isometry, including to a larger Hilbert space. -/
def extend [CompleteSpace E] [CompleteSpace F] (I : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) :
    F →L[ℂ] F :=
  I.toContinuousLinearMap ∘L A ∘L I.toContinuousLinearMap.adjoint

theorem extend_apply_image [CompleteSpace E] [CompleteSpace F]
    (I : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) (x : E) :
    extend I A (I x) = I (A x) := by
  rw [extend]
  have h : I.toContinuousLinearMap.adjoint (I x) = x :=
    DFunLike.congr_fun I.adjoint_comp_self x
  exact congrArg (fun y => I (A y)) h

theorem extend_adjoint [CompleteSpace E] [CompleteSpace F]
    (I : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) :
    (extend I A).adjoint = extend I A.adjoint := by
  simp only [extend, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

theorem extend_mul [CompleteSpace E] [CompleteSpace F]
    (I : E →ₗᵢ[ℂ] F) (A B : E →L[ℂ] E) :
    extend I (A * B) = extend I A * extend I B := by
  ext x
  change I (A (B (I.toContinuousLinearMap.adjoint x))) =
    extend I A (I (B (I.toContinuousLinearMap.adjoint x)))
  rw [extend_apply_image]

private theorem extend_nonneg [CompleteSpace E] [CompleteSpace F]
    (I : E →ₗᵢ[ℂ] F) {A : E →L[ℂ] E} (hA : 0 ≤ A) : 0 ≤ extend I A := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  rw [extend_mul, ContinuousLinearMap.star_eq_adjoint, ← extend_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint]
  exact star_mul_self_nonneg _

private theorem extend_abs [CompleteSpace E] [CompleteSpace F]
    (I : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) :
    CFC.abs (extend I A) = extend I (CFC.abs A) := by
  change CFC.sqrt (star (extend I A) * extend I A) = _
  apply (CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _)
    (extend_nonneg I (CFC.abs_nonneg A))).mpr
  rw [← extend_mul, CFC.abs_mul_abs, extend_mul, ContinuousLinearMap.star_eq_adjoint,
    ← extend_adjoint, ← ContinuousLinearMap.star_eq_adjoint]

/-- Adding zero on the orthogonal complement preserves the trace norm exactly. -/
theorem traceNorm_extend [CompleteSpace E] [CompleteSpace F]
    (I : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) : traceNorm (extend I A) = traceNorm A := by
  let S := CFC.sqrt (CFC.abs A)
  let T := S ∘L I.toContinuousLinearMap.adjoint
  have hS : S.adjoint ∘L S = CFC.abs A := by
    have hself : IsSelfAdjoint S := (CFC.sqrt_nonneg (a := CFC.abs A)).isSelfAdjoint
    change star S * S = CFC.abs A
    rw [hself.star_eq, CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg A)]
  have hT : T.adjoint ∘L T = extend I (CFC.abs A) := by
    simp only [T, extend, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ← hS, ContinuousLinearMap.comp_assoc]
  have hT' : T.adjoint = I.toContinuousLinearMap ∘L S.adjoint := by
    simp [T, ContinuousLinearMap.adjoint_comp]
  unfold traceNorm posTrace
  rw [extend_abs, ← hT, traceIn_adjoint_comp_self, hsSq_eq_hsSq_adjoint _ (refBasis E), hT']
  conv_rhs => rw [← hS, traceIn_adjoint_comp_self]
  unfold hsSq
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map]
  have hself : S.adjoint = S := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (CFC.sqrt_nonneg (a := CFC.abs A)).isSelfAdjoint.star_eq
  rw [hself]

/-- The embedding on a completed tensor power, as a bounded linear map. -/
abbrev tensorCLM (J : E →ₗᵢ[ℂ] F) (n : ℕ) :=
  (tensorMapI J n).toContinuousLinearMap

theorem split_tensorMapI (J : E →ₗᵢ[ℂ] F) (k m : ℕ) (z : HilbertTensorPower ℂ E (k + m)) :
    splitIsometry k m (tensorMapI J (k + m) z) =
      htmap (tensorCLM J k) (tensorCLM J m) (splitIsometry k m z) := by
  have pure (f : Fin (k + m) → E) :
      splitIsometry k m (tensorMapI J (k + m) ((ptprod f : AlgTensorPower ℂ E (k + m)) :
        HilbertTensorPower ℂ E (k + m))) =
      htmap (tensorCLM J k) (tensorCLM J m) (splitIsometry k m
        ((ptprod f : AlgTensorPower ℂ E (k + m)) : HilbertTensorPower ℂ E (k + m))) := by
    let a : Fin k → E := fun i => f (Fin.castAdd m i)
    let b : Fin m → E := fun i => f (Fin.natAdd k i)
    have hf : f = Fin.append a b := (Fin.append_castAdd_natAdd (f := f)).symm
    have happend : (fun i => J (Fin.append a b i)) =
        Fin.append (fun i => J (a i)) (fun i => J (b i)) := by
      funext i
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
    rw [hf, tensorMapI_coe, algMapI_ptprod, happend, splitIsometry_ptprod_append,
      splitIsometry_ptprod_append, htmap_htmul]
    simp only [LinearIsometry.coe_toContinuousLinearMap, tensorMapI_coe, algMapI_ptprod]
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((splitIsometry k m).continuous.comp (tensorMapI J (k + m)).continuous)
      ((htmap _ _).continuous.comp (splitIsometry k m).continuous)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      rw [UniformSpace.Completion.coe_smul]
      simp only [map_smul, pure f]
    | add x y hx hy =>
      rw [UniformSpace.Completion.coe_add]
      simp only [map_add, hx, hy]

theorem cast_tensorMapI (J : E →ₗᵢ[ℂ] F) {n m : ℕ} (h : n = m)
    (x : HilbertTensorPower ℂ E n) :
    castHTP h (tensorMapI J n x) = tensorMapI J m (castHTP h x) := by
  subst m
  rfl

private theorem density_htmap {X Y X' Y' : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [CompleteSpace X']
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y'] [CompleteSpace Y']
    (I : X →ₗᵢ[ℂ] X') (J : Y →ₗᵢ[ℂ] Y') (x : HilbertTensor ℂ X Y) :
    reducedDensity (htmap I.toContinuousLinearMap J.toContinuousLinearMap x) =
      extend I (reducedDensity x) := by
  let U := I.toContinuousLinearMap
  let V := J.toContinuousLinearMap
  have hrank (a b : X') : U.adjoint ∘L InnerProductSpace.rankOne ℂ a b ∘L U =
      InnerProductSpace.rankOne ℂ (U.adjoint a) (U.adjoint b) := by
    ext y
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, map_smul,
      ContinuousLinearMap.adjoint_inner_left]
  ext a
  refine ext_inner_right ℂ fun b => ?_
  have hL : ⟪htmap U V x, htmap (InnerProductSpace.rankOne ℂ b a)
       (ContinuousLinearMap.id ℂ Y') (htmap U V x)⟫_ℂ =
      ⟪x, htmap (InnerProductSpace.rankOne ℂ (U.adjoint b) (U.adjoint a))
        (ContinuousLinearMap.id ℂ Y) x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_htmap]
    have e : htmap U.adjoint V.adjoint
        (htmap (InnerProductSpace.rankOne ℂ b a) (ContinuousLinearMap.id ℂ Y') (htmap U V x)) =
        htmap (U.adjoint ∘L InnerProductSpace.rankOne ℂ b a ∘L U)
          (V.adjoint ∘L ContinuousLinearMap.id ℂ Y' ∘L V) x := by
      rw [htmap_comp, htmap_comp]
      rfl
    rw [e, hrank, ContinuousLinearMap.id_comp, J.adjoint_comp_self]
    rfl
  change ⟪reducedDensity (htmap U V x) a, b⟫_ℂ =
    ⟪(U ∘L reducedDensity x ∘L U.adjoint) a, b⟫_ℂ
  rw [inner_reducedDensity_left, hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_right U, inner_reducedDensity_left]

/-- A reduced density is extended by zero, with no change to its nonzero spectral data. -/
theorem reducedDensityN_tensorMapI (J : E →ₗᵢ[ℂ] F) (N k : ℕ) (hk : k ≤ N)
    (x : HilbertTensorPower ℂ E N) :
    reducedDensityN N k hk (tensorMapI J N x) =
      extend (tensorMapI J k) (reducedDensityN N k hk x) := by
  unfold reducedDensityN reducedDensityPower
  rw [cast_tensorMapI, split_tensorMapI, density_htmap]

/-- Transporting the tensor projector and the many-body vector preserves their marginal distance. -/
theorem marginal_distance_tensorMapI (J : E →ₗᵢ[ℂ] F) (N k : ℕ) (hk : k ≤ N)
    (x : HilbertTensorPower ℂ E N) (u : E) :
    traceNorm (reducedDensityN N k hk (tensorMapI J N x) -
      InnerProductSpace.rankOne ℂ (htpow k (J u)) (htpow k (J u))) =
      traceNorm (reducedDensityN N k hk x - InnerProductSpace.rankOne ℂ (htpow k u) (htpow k u)) := by
  rw [reducedDensityN_tensorMapI, ← tensorMapI_htpow]
  have hp : InnerProductSpace.rankOne ℂ (tensorMapI J k (htpow k u)) (tensorMapI J k (htpow k u)) =
      extend (tensorMapI J k) (InnerProductSpace.rankOne ℂ (htpow k u) (htpow k u)) := by
    ext y
    simp only [extend, ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply,
      map_smul, ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap]
  rw [hp, ← traceNorm_extend (tensorMapI J k)]
  congr 1
  ext y
  simp [extend]

end QuantumNLS.Prop021MarginalTransportR132

#print axioms QuantumNLS.Prop021MarginalTransportR132.marginal_distance_tensorMapI

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let moduleName := "Prop021MarginalTransportR132"
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith ("QuantumNLS." ++ moduleName ++ ".") ||
        n.toString.startsWith ("_private.QuantumNLS." ++ moduleName ++ ".") then
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
  Lean.logInfo m!"R132 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
