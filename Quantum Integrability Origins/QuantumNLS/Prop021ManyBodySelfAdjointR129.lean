import QuantumNLS.Prop021ManyBodyR129
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! Self-adjointness of the maximal physical Hilbert direct sum, proved by
testing the adjoint on every entire homogeneous sector. No lower bound or
uniform sector bound is needed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology
namespace QuantumNLS.Prop021ManyBodySelfAdjointR129
open BetheCoefficientTransform Ext025B3PhysicalSectors Prop021ManyBodyR129
variable {L : ℝ} [Fact (0 < L)]

lemma single_mem_domain (A : ∀ n, HN L n →L[ℂ] HN L n) (n : ℕ) (z : HN L n) :
    inclusion L n z ∈ (block A).domain := by
  have hp : projection L n (inclusion L n z) = inclusion L n z := by
    rw [projection_eq_single]
    change lp.single 2 n ((lp.single 2 n z) n) = lp.single 2 n z
    simp only [lp.single_apply, Pi.single_eq_same]
  rw [← hp]
  exact projection_mem_blockDomain A n _

lemma block_single (A : ∀ n, HN L n →L[ℂ] HN L n) (n : ℕ) (z : HN L n) :
    block A ⟨inclusion L n z, single_mem_domain A n z⟩ = inclusion L n (A n z) := by
  apply lp.ext
  funext m
  change A m ((lp.single 2 n z) m) = (lp.single 2 n (A n z)) m
  by_cases h : m = n
  · subst m; simp only [lp.single_apply, Pi.single_eq_same]
  · simp only [lp.single_apply, Pi.single_eq_of_ne h, map_zero]

lemma block_dense (A : ∀ n, HN L n →L[ℂ] HN L n) :
    Dense ((block A).domain : Set (Fock L)) := by
  intro x
  apply mem_closure_of_tendsto ((projection_hasSum L x).tendsto_sum_nat)
  exact Filter.Eventually.of_forall (fun J =>
    (block A).domain.sum_mem (fun n _ => projection_mem_blockDomain A n x))

/-- Maximal direct sum self-adjointness for all bounded self-adjoint
sector families, with no norm-growth hypothesis. -/
theorem block_selfAdjoint (A : ∀ n, HN L n →L[ℂ] HN L n)
    (hA : ∀ n, (A n).adjoint = A n) : IsSelfAdjoint (block A) := by
  have hd := block_dense A
  have hf : (block A).IsFormalAdjoint (block A) :=
    Prop021DuhamelR128.block_symmetric A hA
  have hlo : block A ≤ (block A).adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hd hf
  have hc (x : (block A).adjoint.domain) (n : ℕ) :
      A n (x.val n) = (block A).adjoint x n := by
    apply ext_inner_right ℂ
    intro z
    have hi := (block A).adjoint_isFormalAdjoint hd x
      ⟨inclusion L n z, single_mem_domain A n z⟩
    rw [block_single] at hi
    change ⟪(block A).adjoint x, lp.single 2 n z⟫_ℂ =
      ⟪x.val, lp.single 2 n (A n z)⟫_ℂ at hi
    rw [lp.inner_single_right, lp.inner_single_right,
      ← ContinuousLinearMap.adjoint_inner_left, hA n] at hi
    exact hi.symm
  have hhi : (block A).adjoint ≤ block A := by
    refine ⟨?_, ?_⟩
    · intro x hx
      change Memℓp (fun n => A n (x n)) 2
      have he : (fun n => A n (x n)) = (fun n => (block A).adjoint ⟨x,hx⟩ n) :=
        funext (fun n => hc ⟨x,hx⟩ n)
      rw [he]
      exact lp.memℓp _
    · intro x y hxy
      apply lp.ext
      funext n
      change (block A).adjoint x n = A n (y.val n)
      rw [← hc x n, hxy]
  exact le_antisymm hhi hlo

/-- The literal Q7B H_N is self-adjoint on exactly its maximal domain. -/
theorem hamiltonian_selfAdjoint (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (N : ℕ) : IsSelfAdjoint (hamiltonian B N) :=
  block_selfAdjoint (sector B N) (sector_adjoint B hB N)

end QuantumNLS.Prop021ManyBodySelfAdjointR129
#print axioms QuantumNLS.Prop021ManyBodySelfAdjointR129.hamiltonian_selfAdjoint

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021ManyBodySelfAdjointR129"].any
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
  Lean.logInfo m!"R129 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
