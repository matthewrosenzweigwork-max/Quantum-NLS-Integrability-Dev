import QuantumNLS.Prop001RfourteenTraceRegrouping
import QuantumNLS.Prop001RfourteenIdentification

/-! Trace duality transports for the finite marginal calculation. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RfifteenTransport
open TraceClass TraceIdeal TraceCompact TensorCarrier PhysicalTensor PhysicalEnergyTrace
  Ext025B11TracePairing Ext025A12Trace Ext025A12Normal Ext025A12Tensor
  Ext025A12PartialTrace Ext025A12Collision Prop001 Prop001RfourteenTraceRegrouping
variable {X Y Z : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]

/-- Unitary change of carrier preserves the actual complex trace. -/
theorem tr_pull (e : X ≃ₗᵢ[ℂ] Y) (T : Y →L[ℂ] Y) (hT : IsTraceClass T) :
    tr (pull e T) = tr T := by
  classical
  let b := refBasis X
  let c := HilbertBasis.ofRepr (e.symm.trans b.repr)
  have hc (i : RefIndex X) : c i = e (b i) := by
    rw [← c.repr_symm_single]
    show (e.symm.trans b.repr).symm (lp.single 2 i (1 : ℂ)) = e (b i)
    rw [LinearIsometryEquiv.symm_trans,LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.symm_symm,b.repr_symm_single]
  change trace b (pull e T) = trace (refBasis Y) T
  rw [← trace_basis_independent c (refBasis Y) T hT]
  unfold trace
  apply tsum_congr
  intro i
  rw [pull_apply,inner_symm_right,hc]

/-- Trace pairing separates all trace-class operators. -/
theorem tr_separates (S T : X →L[ℂ] X)
    (h : ∀ A : X →L[ℂ] X, tr (S*A) = tr (T*A)) : S = T := by
  ext y
  apply ext_inner_left ℂ
  intro x
  simpa only [tr,Ext025A12Normal.trace_rankOne_left] using h (InnerProductSpace.rankOne ℂ y x)

theorem left_finite (B T : X →L[ℂ] X) (hT : IsTraceClass T) : IsTraceClass (B*T) :=
  (traceNorm_mul_left_le B T).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT)

/-- Bounded left multiplication passes through the constructed partial trace. -/
theorem partialTrace_left (B : X →L[ℂ] X)
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (hT : IsTraceClass T) :
    partialTrace (ampliate ℂ X Y B*T) (left_finite _ T hT) =
      B*partialTrace T hT := by
  apply tr_separates
  intro A
  rw [partialTrace_duality]
  calc
    tr (ampliate ℂ X Y B*T*ampliate ℂ X Y A) =
        tr (T*ampliate ℂ X Y A*ampliate ℂ X Y B) := by
      rw [mul_assoc]
      exact trace_cycle (refBasis _) (ampliate ℂ X Y B) (T*ampliate ℂ X Y A)
        (finite_right _ T hT)
    _ = tr (T*ampliate ℂ X Y (A*B)) := by rw [ampliate_mul,mul_assoc]
    _ = tr (partialTrace T hT*(A*B)) := (partialTrace_duality T hT (A*B)).symm
    _ = tr (B*partialTrace T hT*A) := by
      calc
        _ = tr ((partialTrace T hT*A)*B) := by rw [mul_assoc]
        _ = tr (B*(partialTrace T hT*A)) :=
          (trace_cycle (refBasis X) B (partialTrace T hT*A)
            (finite_right A _ (partialTrace_isTraceClass T hT))).symm
        _ = _ := by rw [mul_assoc]

/-- Bounded right multiplication passes through the constructed partial trace. -/
theorem partialTrace_right (B : X →L[ℂ] X)
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (hT : IsTraceClass T) :
    partialTrace (T*ampliate ℂ X Y B) (finite_right _ T hT) =
      partialTrace T hT*B := by
  apply tr_separates
  intro A
  rw [partialTrace_duality,mul_assoc,← ampliate_mul,← partialTrace_duality,mul_assoc]

/-- The visible-block commutator reduces on arbitrary trace-class inputs. -/
theorem partialTrace_commutator (B : X →L[ℂ] X)
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (hT : IsTraceClass T) :
    partialTrace (ampliate ℂ X Y B*T-T*ampliate ℂ X Y B)
      (commutator_finite _ T hT) = B*partialTrace T hT-partialTrace T hT*B := by
  have he := map_sub (partialTraceLinear (X := X) (Y := Y))
    (⟨ampliate ℂ X Y B*T,lt_top_iff_ne_top.mpr (finite_left _ T hT.ne)⟩)
    (⟨T*ampliate ℂ X Y B,finite_right _ T hT⟩)
  have hv := congrArg Subtype.val he
  calc
    _ = partialTrace (ampliate ℂ X Y B*T) (left_finite _ T hT)-
        partialTrace (T*ampliate ℂ X Y B) (finite_right _ T hT) := hv
    _ = _ := by rw [partialTrace_left,partialTrace_right]

/-- Conjugation of a pure density uses the actual isometric inverse. -/
theorem pull_rankOne (e : X ≃ₗᵢ[ℂ] Y) (x y : Y) :
    pull e (InnerProductSpace.rankOne ℂ x y) =
      InnerProductSpace.rankOne ℂ (e.symm x) (e.symm y) := by
  ext z
  simp only [pull_apply,InnerProductSpace.rankOne_apply,map_smul]
  rw [inner_symm_left]

theorem rankOne_finite (x y : X) : IsTraceClass (InnerProductSpace.rankOne ℂ x y) :=
  (Fidelity.traceNorm_rankOne_le x y).trans_lt ENNReal.ofReal_lt_top

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem reducedDensityPower_cast (k m n : ℕ) (h : m=n)
    (z : HilbertTensorPower ℂ H (k+n)) :
    reducedDensityPower k m (castHTP (congrArg (fun j => k+j) h).symm z) =
      reducedDensityPower k n z := by
  cases h
  rfl

/-- Compatibility with the repository's actual finite pure-state marginal. -/
theorem splitTrace_rankOne (k m : ℕ) (z : HilbertTensorPower ℂ H (k+m)) :
    splitTrace k m (InnerProductSpace.rankOne ℂ z z) (rankOne_finite z z) =
      reducedDensityN (k+m) k (by omega) z := by
  unfold splitTrace
  simp only [pull_rankOne,partialTrace_rankOne,LinearIsometryEquiv.symm_symm]
  exact (reducedDensityPower_cast k (k+m-k) m (by omega) z).symm

end QuantumNLS.Prop001RfifteenTransport

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RfifteenTransport" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
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
  Lean.logInfo m!"Prop001RfifteenTransport audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."


#print axioms QuantumNLS.Prop001RfifteenTransport.tr_pull
#print axioms QuantumNLS.Prop001RfifteenTransport.tr_separates
#print axioms QuantumNLS.Prop001RfifteenTransport.partialTrace_left
#print axioms QuantumNLS.Prop001RfifteenTransport.partialTrace_right
#print axioms QuantumNLS.Prop001RfifteenTransport.partialTrace_commutator
#print axioms QuantumNLS.Prop001RfifteenTransport.pull_rankOne
#print axioms QuantumNLS.Prop001RfifteenTransport.rankOne_finite
#print axioms QuantumNLS.Prop001RfifteenTransport.splitTrace_rankOne

#print axioms QuantumNLS.Prop001RfifteenTransport.left_finite

#print axioms QuantumNLS.Prop001RfifteenTransport.reducedDensityPower_cast
