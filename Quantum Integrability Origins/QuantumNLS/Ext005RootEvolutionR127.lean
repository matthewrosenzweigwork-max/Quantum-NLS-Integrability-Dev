import QuantumNLS.Prop022DomainR122

/-! Bounded action of the frozen physical evolution in every completed
number-moment norm. All bounds come from the proved cutoff estimates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace Topology ComplexConjugate
open Set Filter ContinuousLinearMap
namespace QuantumNLS.Ext005RootEvolutionR127
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005FormScaleR109 Ext005FormCutoffR109 Ext005PairCommutatorR108
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
open Prop022FockPropagatorR122 Prop022DomainR122
variable {L : ℝ} [Fact (0 < L)]
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
local notation "V" => evolution B M A hM hA hB hs u₀

def domainAction (j : ℕ) (hj : 1 ≤ j) (s t : ℝ) :
    Fock L →ₗ[ℂ] momentDomain (L := L) j :=
  (((V s t).toLinearMap.comp (embedding j).toLinearMap).codRestrict
    (momentDomain j) (fun w =>
      (evolution_energy B M A hM hA hB hs u₀ j hj s t
        ⟨embedding j w, embedding_mem j w⟩).1))

def rootLinear (j : ℕ) (hj : 1 ≤ j) (s t : ℝ) : Fock L →ₗ[ℂ] Fock L :=
  (momentRoot j).toFun.comp (domainAction B M A hM hA hB hs u₀ j hj s t)

lemma rootLinear_bound (j : ℕ) (hj : 1 ≤ j) (s t : ℝ) (w : Fock L) :
    ‖rootLinear B M A hM hA hB hs u₀ j hj s t w‖ ≤
      Real.sqrt (Real.exp (differenceConstant j*(M*pairMajorant A)*|t-s|)) * ‖w‖ := by
  have he := (evolution_energy B M A hM hA hB hs u₀ j hj s t
    ⟨embedding j w, embedding_mem j w⟩).2
  rw [energy_embedding] at he
  change energy j (domainAction B M A hM hA hB hs u₀ j hj s t w).val ≤ _ at he
  rw [energy_eq_root j (domainAction B M A hM hA hB hs u₀ j hj s t w)] at he
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (Real.exp_pos _).le]
  exact he.trans_eq (mul_comm _ _)

def rootEvolution (j : ℕ) (hj : 1 ≤ j) (s t : ℝ) : Fock L →L[ℂ] Fock L :=
  (rootLinear B M A hM hA hB hs u₀ j hj s t).mkContinuous
    (Real.sqrt (Real.exp (differenceConstant j*(M*pairMajorant A)*|t-s|)))
    (rootLinear_bound B M A hM hA hB hs u₀ j hj s t)

lemma rootEvolution_apply (j : ℕ) (hj : 1 ≤ j) (s t : ℝ)
    (x : momentDomain (L := L) j) :
    rootEvolution B M A hM hA hB hs u₀ j hj s t (momentRoot j x) =
      rootLift j (V s t x.val) := by
  rw [rootLift_eq j _ (evolution_energy B M A hM hA hB hs u₀ j hj s t x).1]
  change momentRoot j (domainAction B M A hM hA hB hs u₀ j hj s t (momentRoot j x)) = _
  congr 1
  apply Subtype.ext
  change V s t (embedding j (momentRoot j x)) = V s t x.val
  rw [embedding_root]

/-- Strong form convergence of evolved finite-particle approximations,
including the lowest j=1 domain without any extra initial moments. -/
theorem evolved_cutoff_root_tendsto (j : ℕ) (hj : 1 ≤ j) (s t : ℝ)
    (x : momentDomain (L := L) j) :
    Tendsto (fun N => rootLift j (V s t (cutoff N x.val))) atTop
      (𝓝 (rootLift j (V s t x.val))) := by
  have h := ((rootEvolution B M A hM hA hB hs u₀ j hj s t).continuous.tendsto
    (momentRoot j x)).comp (root_cutoff_tendsto j x)
  simp only [Function.comp_def] at h
  have hfun : (fun N => rootEvolution B M A hM hA hB hs u₀ j hj s t
      (momentRoot j ⟨cutoff N x.val, cutoff_mem j N x.val⟩)) =
      (fun N => rootLift j (V s t (cutoff N x.val))) :=
    funext (fun N => rootEvolution_apply B M A hM hA hB hs u₀ j hj s t
      ⟨cutoff N x.val, cutoff_mem j N x.val⟩)
  rw [hfun, rootEvolution_apply] at h
  exact h

end QuantumNLS.Ext005RootEvolutionR127
#print axioms QuantumNLS.Ext005RootEvolutionR127.evolved_cutoff_root_tendsto

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005RootEvolutionR127." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005RootEvolutionR127." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R127 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
