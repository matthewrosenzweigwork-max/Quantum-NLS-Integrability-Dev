import QuantumNLS.Local006SequenceAlgebraE
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Normed

/-! Hilbert-space transposition and convergence tools for positive Fourier
kernel majorants. Identifying the normalized derivative with such kernels is
still a separate source obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.Local006.TransposeMajorantG

abbrev RealSeq := lp (fun _ : ℤ => ℝ) 2

def transpose (T : RealSeq →L[ℝ] RealSeq) : RealSeq →L[ℝ] RealSeq :=
  ContinuousLinearMap.adjoint T

@[simp] theorem transpose_norm (T : RealSeq →L[ℝ] RealSeq) : ‖transpose T‖ = ‖T‖ :=
  ContinuousLinearMap.adjoint.norm_map T

/-- On the real Hilbert space the adjoint matrix is exactly the transpose,
without conjugation. This applies in particular to positive Fourier kernels. -/
theorem transpose_entry (T : RealSeq →L[ℝ] RealSeq) (i j : ℤ) :
    transpose T (lp.single 2 j 1) i = T (lp.single 2 i 1) j := by
  have h := T.adjoint_inner_right (lp.single 2 i 1) (lp.single 2 j 1)
  simpa only [lp.inner_single_left, lp.inner_single_right, real_inner_comm,
    real_inner_self_eq_norm_sq, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    one_mul, mul_one, transpose] using h

/-- Absolute operator-norm convergence is retained by transposition, and the
sum has the same norm as the original summed kernel. -/
theorem transpose_series {T : ℕ → RealSeq →L[ℝ] RealSeq}
    (hT : Summable (fun k => ‖T k‖)) :
    Summable (fun k => ‖transpose (T k)‖) ∧
      HasSum (fun k => transpose (T k)) (transpose (∑' k, T k)) ∧
      ‖transpose (∑' k, T k)‖ = ‖∑' k, T k‖ := by
  refine ⟨by simpa using hT, ?_, transpose_norm _⟩
  exact ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap.hasSum hT.of_norm.hasSum

/-- The factor counting all differentiated slots is summable on the same
strictly smaller ball; this does not assume a derivative bound. -/
theorem differentiated_geometric_summable {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hsmall : C * t < 1) :
    Summable (fun d : ℕ => (d + 1 : ℝ) * C ^ (d + 1) * t ^ d) := by
  have hq : ‖C * t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC ht)]; exact hsmall
  have h0 := summable_geometric_of_norm_lt_one hq
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  simp only [pow_one] at h1
  apply ((h1.add h0).mul_left C).congr
  intro d
  simp only [mul_pow, pow_succ]
  ring

end QuantumNLS.Local006.TransposeMajorantG
#print axioms QuantumNLS.Local006.TransposeMajorantG.transpose_entry
#print axioms QuantumNLS.Local006.TransposeMajorantG.transpose_series
#print axioms QuantumNLS.Local006.TransposeMajorantG.differentiated_geometric_summable

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.TransposeMajorantG." ||
        n.toString.startsWith "_private.QuantumNLS.Local006TransposeMajorantG" then
      pending := pending.push n
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
  Lean.logInfo m!"Local006TransposeMajorantG audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
