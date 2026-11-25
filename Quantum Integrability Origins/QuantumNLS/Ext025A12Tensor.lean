import QuantumNLS.FiniteTraceCompression
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! Strong convergence of finite tensor-factor projections. No countable
basis or separability restriction is introduced. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Ext025A12Tensor
open TraceClass TensorCarrier FiniteTraceCompression
variable {X Y ι : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

theorem norm_ampliate_le (A : X →L[ℂ] X) : ‖ampliate ℂ X Y A‖ ≤ ‖A‖ := by
  exact (norm_htmap_le A (ContinuousLinearMap.id ℂ Y)).trans
    (by nlinarith [ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Y),norm_nonneg A])

theorem ampliate_mul (A B : X →L[ℂ] X) :
    ampliate ℂ X Y (A*B) = ampliate ℂ X Y A * ampliate ℂ X Y B := by
  simpa only [ampliate_apply,ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_id] using
    htmap_comp A B (ContinuousLinearMap.id ℂ Y) (ContinuousLinearMap.id ℂ Y)

/-- Finite projections in a tensor factor converge strongly on the completed
Hilbert tensor product. -/
theorem ampliate_proj_strong (b : HilbertBasis ι ℂ X) (z : HilbertTensor ℂ X Y) :
    Tendsto (fun s : Finset ι => ampliate ℂ X Y (proj b s) z) atTop (𝓝 z) := by
  let B := fun s : Finset ι => ampliate ℂ X Y (proj b s)
  have hn (s : Finset ι) : ‖B s‖ ≤ 1 := (norm_ampliate_le _).trans (norm_proj_le b s)
  have he : Equicontinuous (fun s z => B s z) :=
    (LipschitzWith.uniformEquicontinuous (fun s z => B s z) 1
      (fun s => (B s).lipschitzWith.weaken (by exact_mod_cast hn s))).equicontinuous
  let c := refBasis Y
  apply forall_of_hilbertBasis (htmulBasis b c)
    (P := fun z => Tendsto (fun s : Finset ι => B s z) atTop (𝓝 z))
    (he.isClosed_setOfPred_tendsto continuous_id)
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : Finset ι => (0 : HilbertTensor ℂ X Y)) atTop (𝓝 0))
  · intro x y hx hy
    simpa only [map_add] using hx.add hy
  · intro a x hx
    simpa only [map_smul] using tendsto_const_nhds.smul hx
  · intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({p.1} : Finset ι)] with s hs
    simp only [htmulBasis_apply]
    change htmul (b p.1) (c p.2) = htmap (proj b s) (ContinuousLinearMap.id ℂ Y)
      (htmul (b p.1) (c p.2))
    rw [htmap_htmul,proj_basis b s (Finset.singleton_subset_iff.mp hs),ContinuousLinearMap.id_apply]

theorem ampliate_proj_mul_strong (b : HilbertBasis ι ℂ X) (A : X →L[ℂ] X)
    (z : HilbertTensor ℂ X Y) :
    Tendsto (fun s : Finset ι => ampliate ℂ X Y (proj b s*A) z) atTop
      (𝓝 (ampliate ℂ X Y A z)) := by
  simp only [ampliate_mul,mul_apply_eq_comp]
  exact ampliate_proj_strong b _

theorem ampliate_positive (A : X →L[ℂ] X) (hA : A.IsPositive) :
    (ampliate ℂ X Y A).IsPositive := by
  let S := CFC.sqrt A
  have hs : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have he : ampliate ℂ X Y A = (ampliate ℂ X Y S).adjoint * ampliate ℂ X Y S := by
    simp only [ampliate_apply,adjoint_htmap,hs.adjoint_eq,ContinuousLinearMap.adjoint_id]
    change ampliate ℂ X Y A = ampliate ℂ X Y S * ampliate ℂ X Y S
    rw [← ampliate_mul]
    rw [show S*S = A from CFC.sqrt_mul_sqrt_self A (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA)]
  rw [he]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

theorem ampliate_one : ampliate ℂ X Y (1 : X →L[ℂ] X) = 1 := by
  ext z
  apply forall_of_hilbertBasis (htmulBasis (refBasis X) (refBasis Y))
    (P := fun z => ampliate ℂ X Y (1 : X →L[ℂ] X) z = z)
    (isClosed_eq (ampliate ℂ X Y (1 : X →L[ℂ] X)).continuous continuous_id)
  · simp
  · intro x y hx hy
    simp only [map_add,hx,hy]
  · intro a x hx
    simp only [map_smul,hx]
  · intro p
    simp only [htmulBasis_apply,ampliate_apply,htmap_htmul,one_apply_eq_self,
      ContinuousLinearMap.id_apply]

end QuantumNLS.Ext025A12Tensor

#print axioms QuantumNLS.Ext025A12Tensor.ampliate_proj_strong
#print axioms QuantumNLS.Ext025A12Tensor.ampliate_positive
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A12Tensor" then
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
  Lean.logInfo m!"Ext025A12Tensor audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
