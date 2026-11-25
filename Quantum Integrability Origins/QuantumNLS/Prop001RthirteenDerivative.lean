import QuantumNLS.Prop001RthirteenSeries
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The actual product hierarchy differentiated in trace norm, rather than
only against matrix elements. No collision equation is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Prop001RthirteenDerivative
open TraceClass TensorCarrier Prop001
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E

theorem traceNorm_rankOne_difference (x y a b : E) :
    traceNorm (InnerProductSpace.rankOne ℂ x y-InnerProductSpace.rankOne ℂ a b) ≤
      ENNReal.ofReal (‖x-a‖*‖y‖+‖a‖*‖y-b‖) := by
  have he : InnerProductSpace.rankOne ℂ x y-InnerProductSpace.rankOne ℂ a b =
      InnerProductSpace.rankOne ℂ (x-a) y+InnerProductSpace.rankOne ℂ a (y-b) := by
    ext z
    simp only [sub_apply,add_apply,
      InnerProductSpace.rankOne_apply,inner_sub_left,sub_smul,smul_sub]
    module
  rw [he]
  exact (traceNorm_add_le _ _).trans ((add_le_add (Fidelity.traceNorm_rankOne_le _ _)
    (Fidelity.traceNorm_rankOne_le _ _)).trans_eq (ENNReal.ofReal_add (by positivity) (by positivity)).symm)

theorem rankOne_trace_tendsto {ι : Type*} {l : Filter ι}
    (x y : ι → E) (a b : E) (hx : Tendsto x l (𝓝 a)) (hy : Tendsto y l (𝓝 b)) :
    Tendsto (fun i => traceNorm (InnerProductSpace.rankOne ℂ (x i) (y i)-
      InnerProductSpace.rankOne ℂ a b)) l (𝓝 0) := by
  have ha : Tendsto (fun _ : ι => a) l (𝓝 a) := tendsto_const_nhds
  have hbconst : Tendsto (fun _ : ι => b) l (𝓝 b) := tendsto_const_nhds
  have h1 : Tendsto (fun i => ‖x i-a‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hx.sub ha).norm
  have h2 : Tendsto (fun i => ‖y i-b‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hy.sub hbconst).norm
  have hb : Tendsto (fun i => ‖x i-a‖*‖y i‖+‖a‖*‖y i-b‖) l (𝓝 0) := by
    simpa only [zero_mul,mul_zero,zero_add] using (h1.mul hy.norm).add (ha.norm.mul h2)
  have hb' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [Function.comp_def,ENNReal.ofReal_zero] using hb')
    (fun _ => bot_le) (fun i => traceNorm_rankOne_difference (x i) (y i) a b)

omit [CompleteSpace E] in
/-- Product rule for the projector's literal difference quotient. -/
theorem projector_slope (α : ℝ → E) (s t : ℝ) :
    slope (fun r => InnerProductSpace.rankOne ℂ (α r) (α r)) s t =
      InnerProductSpace.rankOne ℂ (slope α s t) (α t)+
        InnerProductSpace.rankOne ℂ (α s) (slope α s t) := by
  have hc (r : ℝ) : (starRingEnd ℂ) ((algebraMap ℝ ℂ) r) = (algebraMap ℝ ℂ) r := by
    change (starRingEnd ℂ) (r : ℂ) = (r : ℂ)
    exact Complex.conj_ofReal r
  ext z
  simp only [slope_def_module,smul_apply,sub_apply,
    add_apply,InnerProductSpace.rankOne_apply]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),inner_smul_left,inner_sub_left,map_inv₀,map_sub,
    sub_smul,smul_sub,smul_smul]
  simp only [hc]
  module

/-- A differentiable vector curve gives a trace-norm differentiable
projector. This limit uses precisely the frozen trace norm. -/
theorem projector_trace_derivative (α : ℝ → E) (v : E) (t : ℝ)
    (h : HasDerivAt α v t) :
    Tendsto (fun s => traceNorm
      (slope (fun r => InnerProductSpace.rankOne ℂ (α r) (α r)) t s -
        (InnerProductSpace.rankOne ℂ v (α t)+InnerProductSpace.rankOne ℂ (α t) v)))
      (𝓝[≠] t) (𝓝 0) := by
  have hc : Tendsto α (𝓝[≠] t) (𝓝 (α t)) :=
    h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h1 := rankOne_trace_tendsto (slope α t) α v (α t) h.tendsto_slope hc
  have h2 := rankOne_trace_tendsto (fun _ => α t) (slope α t) (α t) v
    tendsto_const_nhds h.tendsto_slope
  have hb := h1.add h2
  simp only [add_zero] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
  intro s
  dsimp only
  rw [projector_slope]
  have he :
      InnerProductSpace.rankOne ℂ (slope α t s) (α s)+InnerProductSpace.rankOne ℂ (α t) (slope α t s)-
        (InnerProductSpace.rankOne ℂ v (α t)+InnerProductSpace.rankOne ℂ (α t) v) =
      (InnerProductSpace.rankOne ℂ (slope α t s) (α s)-InnerProductSpace.rankOne ℂ v (α t))+
        (InnerProductSpace.rankOne ℂ (α t) (slope α t s)-InnerProductSpace.rankOne ℂ (α t) v) := by abel
  rw [he]
  exact traceNorm_add_le _ _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

/-- Trace-norm derivative of the literal source product hierarchy along
the already constructed global Hartree trajectory. -/
theorem trajectory_trace_derivative (D : ClassicalData H) (u : Sphere H) (k : ℕ) (t : ℝ) :
    let z := (htpow k (trajectory D u t) : HilbertTensorPower ℂ H k)
    let w := tensorVelocity k (trajectory D u t)
      (Ext025A8.sourceHartreeField D.A (trajectory D u t))
    Tendsto (fun s => traceNorm (slope (fun r => coherentProjector k (trajectory D u r)) t s -
      (InnerProductSpace.rankOne ℂ w z+InnerProductSpace.rankOne ℂ z w))) (𝓝[≠] t) (𝓝 0) :=
  projector_trace_derivative _ _ t (trajectory_tensor_derivative D u k t)

end QuantumNLS.Prop001RthirteenDerivative

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RthirteenDerivative" then
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
  Lean.logInfo m!"Prop001RthirteenDerivative audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."

#print axioms QuantumNLS.Prop001RthirteenDerivative.traceNorm_rankOne_difference

#print axioms QuantumNLS.Prop001RthirteenDerivative.rankOne_trace_tendsto

#print axioms QuantumNLS.Prop001RthirteenDerivative.projector_slope

#print axioms QuantumNLS.Prop001RthirteenDerivative.projector_trace_derivative

#print axioms QuantumNLS.Prop001RthirteenDerivative.trajectory_trace_derivative
