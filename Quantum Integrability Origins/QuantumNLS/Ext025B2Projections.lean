import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! GP-17: projection-rank stability and a precise counterexample to the
unqualified finite-rank clause. Isolating finitely many spectral values does
not impose finite multiplicity. The identity has an explicit resolvent away
from 1, and its normalized contour integral is the identity. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory Complex
open scoped InnerProductSpace
namespace QuantumNLS.Ext025B2Projections
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fixed_zero_of_norm_sub_lt_one (P Q : E →L[ℂ] E)
    (hPQ : ‖P - Q‖ < 1) (v : E) (hP : P v = v) (hQ : Q v = 0) : v = 0 := by
  have h := (P - Q).le_opNorm v
  simp only [sub_apply, hP, hQ, sub_zero] at h
  have hn := norm_nonneg v
  have hz : ‖v‖ = 0 := by nlinarith
  exact norm_eq_zero.mp hz

/-- A near projection maps the other range injectively into its own range. -/
theorem range_injective (P Q : E →L[ℂ] E) (hP : ∀ v, P (P v) = P v)
    (hPQ : ‖P - Q‖ < 1) :
    Function.Injective (fun v : LinearMap.range P.toLinearMap => Q (v : E)) := by
  intro v w hvw
  have hfix : P ((v : E) - w) = (v : E) - w := by
    obtain ⟨x, hx⟩ := v.property
    obtain ⟨y, hy⟩ := w.property
    rw [map_sub]
    rw [← hx, ← hy]
    exact congrArg₂ (fun a b : E => a - b) (hP x) (hP y)
  have hzero : Q ((v : E) - w) = 0 := by
    change Q (v : E) = Q (w : E) at hvw
    rw [map_sub, hvw, sub_self]
  have h := fixed_zero_of_norm_sub_lt_one P Q hPQ _ hfix hzero
  exact Subtype.ext (sub_eq_zero.mp h)

/-- With one finite-dimensional range, nearby idempotents have the same finite
rank. The finite-multiplicity premise is explicit. -/
theorem «FIN-EXT025-GP-17-rank-stability» (P Q : E →L[ℂ] E)
    (hP : ∀ v, P (P v) = P v) (hQ : ∀ v, Q (Q v) = Q v)
    (hPQ : ‖P - Q‖ < 1) [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)] :
    FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range Q.toLinearMap) =
        Module.finrank ℂ (LinearMap.range P.toLinearMap) := by
  let PQ : LinearMap.range Q.toLinearMap →ₗ[ℂ] LinearMap.range P.toLinearMap :=
    P.toLinearMap.rangeRestrict.comp (LinearMap.range Q.toLinearMap).subtype
  let QP : LinearMap.range P.toLinearMap →ₗ[ℂ] LinearMap.range Q.toLinearMap :=
    Q.toLinearMap.rangeRestrict.comp (LinearMap.range P.toLinearMap).subtype
  have hPQ' : Function.Injective PQ := by
    intro v w h
    apply range_injective Q P hQ (by simpa only [norm_sub_rev] using hPQ)
    exact congrArg Subtype.val h
  have hQP' : Function.Injective QP := by
    intro v w h
    apply range_injective P Q hP hPQ
    exact congrArg Subtype.val h
  let := FiniteDimensional.of_injective PQ hPQ'
  exact ⟨inferInstance, le_antisymm
    (LinearMap.finrank_le_finrank_of_injective hPQ')
    (LinearMap.finrank_le_finrank_of_injective hQP')⟩

/-- Explicit inverse of zI-I, defined for every z different from 1. -/
def identityResolvent (z : ℂ) : E →L[ℂ] E :=
  (z - 1)⁻¹ • ContinuousLinearMap.id ℂ E

theorem identity_resolvent_equations (z : ℂ) (hz : z ≠ 1) :
    (z • ContinuousLinearMap.id ℂ E - ContinuousLinearMap.id ℂ E).comp
      (identityResolvent z) = ContinuousLinearMap.id ℂ E ∧
    (identityResolvent z).comp
      (z • ContinuousLinearMap.id ℂ E - ContinuousLinearMap.id ℂ E) =
        ContinuousLinearMap.id ℂ E := by
  have heq : z • ContinuousLinearMap.id ℂ E - ContinuousLinearMap.id ℂ E =
      (z - 1) • ContinuousLinearMap.id ℂ E := by
    ext v
    simp [sub_smul]
  rw [heq]
  constructor <;> ext v <;>
    simp [identityResolvent, smul_smul, sub_ne_zero.mpr hz]

/-- The normalized contour projection of the identity is the identity. -/
theorem identity_contour [CompleteSpace E] {R : ℝ} (hR : 0 < R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      (∮ z in C((1 : ℂ), R), identityResolvent (E := E) z) =
        ContinuousLinearMap.id ℂ E := by
  simp only [identityResolvent]
  rw [circleIntegral.integral_smul_const,
    circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hR : (1 : ℂ) ∈ Metric.ball 1 R),
    smul_smul, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_smul]

/-- CONTRACT ISSUE: in any infinite-dimensional Hilbert space the contour
above has infinite rank. No finite multiplicity follows from an isolated
one-point cluster and a resolvent neighborhood. -/
theorem identity_not_finite_rank
    (hinf : ¬FiniteDimensional ℂ E) :
    ¬FiniteDimensional ℂ (LinearMap.range (ContinuousLinearMap.id ℂ E).toLinearMap) := by
  intro h
  let := h
  apply hinf
  exact FiniteDimensional.of_injective
    (ContinuousLinearMap.id ℂ E).toLinearMap.rangeRestrict
    (fun x y hxy => congrArg Subtype.val hxy)

/-- The identity is selfadjoint on every complex Hilbert space. -/
theorem identity_selfadjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    IsSelfAdjoint (ContinuousLinearMap.id ℂ H) := by
  change star (1 : H →L[ℂ] H) = 1
  exact star_one _

/-- Elementary residue moments for a single zero, the local contribution
needed by the general logarithmic-derivative argument principle. -/
theorem «FIN-EXT025-GP-17-elementary-moment» (c a : ℂ) (R : ℝ)
    (ha : a ∈ Metric.ball c R) (k : ℕ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∮ z in C(c, R), (z - a)⁻¹ * z^k) = a^k := by
  have h : DiffContOnCl ℂ (fun z : ℂ => z^k) (Metric.ball c R) :=
    (differentiable_id.pow k).differentiableOn.diffContOnCl
  simpa only [smul_eq_mul] using
    h.two_pi_i_inv_smul_circleIntegral_sub_inv_smul ha

end QuantumNLS.Ext025B2Projections

#print axioms QuantumNLS.Ext025B2Projections.identity_selfadjoint
#print axioms QuantumNLS.Ext025B2Projections.«FIN-EXT025-GP-17-elementary-moment»
#print axioms QuantumNLS.Ext025B2Projections.fixed_zero_of_norm_sub_lt_one
#print axioms QuantumNLS.Ext025B2Projections.range_injective
#print axioms QuantumNLS.Ext025B2Projections.«FIN-EXT025-GP-17-rank-stability»
#print axioms QuantumNLS.Ext025B2Projections.identityResolvent
#print axioms QuantumNLS.Ext025B2Projections.identity_resolvent_equations
#print axioms QuantumNLS.Ext025B2Projections.identity_contour
#print axioms QuantumNLS.Ext025B2Projections.identity_not_finite_rank

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025B2Projections." then
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
  Lean.logInfo m!"Ext025B2Projections audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
