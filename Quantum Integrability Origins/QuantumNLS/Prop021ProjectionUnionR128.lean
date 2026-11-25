import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! PROP-021's projection union estimate. The proof is on an arbitrary real
Hilbert carrier and uses only symmetry and idempotence of each projection.
Tensor placement, bosonic symmetry and the physical dGamma identification
are not encoded as hypotheses standing for their desired conclusions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace
namespace QuantumNLS.Prop021ProjectionUnionR128
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure OrthogonalMap (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  map : E →L[ℝ] E
  symmetric : ∀ x y, ⟪x,map y⟫_ℝ = ⟪map x,y⟫_ℝ
  idempotent : ∀ x, map (map x) = map x

namespace OrthogonalMap
lemma orthogonal (P : OrthogonalMap E) (x y : E) :
    ⟪x-P.map x,P.map y⟫_ℝ = 0 := by
  rw [P.symmetric,map_sub,P.idempotent,sub_self,inner_zero_left]

/-- Contractivity follows from the two defining algebraic properties. -/
theorem norm_le (P : OrthogonalMap E) (x : E) : ‖P.map x‖ ≤ ‖x‖ := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (P.orthogonal x x)
  rw [sub_add_cancel] at h
  nlinarith [sq_nonneg ‖x-P.map x‖,norm_nonneg x,norm_nonneg (P.map x)]

/-- The squared defect is the complementary projection expectation. -/
theorem defect_expectation (P : OrthogonalMap E) (x : E) :
    ‖x-P.map x‖^2 = ‖x‖^2-⟪x,P.map x⟫_ℝ := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (P.orthogonal x x)
  rw [sub_add_cancel] at h
  have hi := P.symmetric x (P.map x)
  rw [P.idempotent,real_inner_self_eq_norm_sq] at hi
  linarith

/-- Pythagorean decomposition of the error after one additional projection. -/
theorem step (P : OrthogonalMap E) (x y : E) :
    ‖x-P.map y‖^2 ≤ ‖x-P.map x‖^2+‖x-y‖^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (P.orthogonal x (x-y))
  have he : x-P.map x+P.map (x-y) = x-P.map y := by rw [map_sub]; abel
  rw [he] at h
  have hn := P.norm_le (x-y)
  nlinarith [norm_nonneg (P.map (x-y)),norm_nonneg (x-y)]
end OrthogonalMap

/-- Ordered product of projections, evaluated on a vector. -/
def projectList : List (OrthogonalMap E) → E → E
  | [],x => x
  | P::ps,x => P.map (projectList ps x)

/-- The elementary operator union bound, in squared-vector form.
Commutation is not needed for this ordered-product version. -/
theorem projection_union (ps : List (OrthogonalMap E)) (x : E) :
    ‖x-projectList ps x‖^2 ≤ ((ps.map fun P => ‖x-P.map x‖^2).sum) := by
  induction ps with
  | nil => simp [projectList]
  | cons P ps ih =>
    simp only [projectList,List.map_cons,List.sum_cons]
    have h := P.step x (projectList ps x)
    linarith

/-- Uniform one-factor defects give the exact square-root-in-k estimate. -/
theorem projection_union_uniform (ps : List (OrthogonalMap E)) (x : E)
    {d : ℝ} (hd : 0 ≤ d) (hb : ∀ P ∈ ps, ‖x-P.map x‖ ≤ d) :
    ‖x-projectList ps x‖ ≤ Real.sqrt (ps.length:ℝ) * d := by
  have hsum : (ps.map fun P => ‖x-P.map x‖^2).sum ≤ (ps.length:ℝ)*d^2 := by
    induction ps with
    | nil => simp
    | cons P ps ih =>
      have hP := hb P (by simp)
      have ht := ih (fun Q hQ => hb Q (by simp [hQ]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith [norm_nonneg (x-P.map x)]
  have h := (projection_union ps x).trans hsum
  have hs : (Real.sqrt (ps.length:ℝ)*d)^2 = (ps.length:ℝ)*d^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hp : 0 ≤ Real.sqrt (ps.length:ℝ)*d := mul_nonneg (Real.sqrt_nonneg _) hd
  nlinarith [norm_nonneg (x-projectList ps x)]
end QuantumNLS.Prop021ProjectionUnionR128
#print axioms QuantumNLS.Prop021ProjectionUnionR128.projection_union
#print axioms QuantumNLS.Prop021ProjectionUnionR128.projection_union_uniform

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021ProjectionUnionR128"].any
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
  Lean.logInfo m!"R128 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
