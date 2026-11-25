import QuantumNLS.BetheSpectralContinuity

/-! Internal sufficient specialization of EXT-002 for the periodic proof.
The carrier, ordered kernels, coupling and half-phase convention are the
literal frozen physical definitions. No algebraic creation-operator family
is defined or identified here. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheBasisBinding
open TensorCarrier TensorPlacements PhysicalTensor BetheIntegralOperator
open BetheTransferOperators BethePhysicalTransfer BetheHigherPlacement
open BetheSpectralContinuity

/-- The exact sufficient EXT-002 instance used by the periodic basis proof.
It uses the original coordinate vector, ordinary product torus measure,
both ordered kernels compressed by the symmetric projection, and the
unchanged physical transfer with coefficient c^m (N)_m. The entire scalar
has the printed product off roots; at roots it is its removable value. -/
theorem ext002_periodic_specialization (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) :
    Function.Injective (BetheSmooth.sourceRoots L n c) ∧
    TransferSeparation.OnShell L c (BetheSmooth.sourceRoots L n c) ∧
    (physUnitary (sourceVector L hc hn).1 =
      ContinuousMap.toLp 2 (torusPiMeasure L N) ℂ
        (BetheGeneralSliceEndpoints.sourceInput L hc hn)) ∧
    (∀ m z, physicalKernel L m z =
      (positionInclusion L m).adjoint ∘L rawOperator L m z ∘L positionInclusion L m) ∧
    (∀ m, m ≤ N → N.descFactorial m = N.factorial / (N-m).factorial) ∧
    Differentiable ℂ (spectralValue L hc hn) ∧
    (∀ z, (∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ)) →
      spectralValue L hc hn z = TransferSeparation.sFun L c
        (BetheSmooth.sourceRoots L n c) z) ∧
    (∀ z, transfer L N c z (sourceVector L hc hn) =
      spectralValue L hc hn z • sourceVector L hc hn) ∧
    (∀ z, physUnitary ((transfer L N c z (sourceVector L hc hn)).1) =
      ContinuousMap.toLp 2 (torusPiMeasure L N) ℂ
        (spectralValue L hc hn z • BetheGeneralSliceEndpoints.sourceInput L hc hn)) := by
  have hs : TransferSeparation.OnShell L c (BetheSmooth.sourceRoots L n c) := by
    cases N with
    | zero => intro i; exact Fin.elim0 i
    | succ M => exact BetheOnShell.sourceRoots_onShell (Fact.out : 0 < L) hc hn
  exact ⟨(BetheSmooth.sourceRoots_strictAnti (Fact.out : 0 < L) hc hn).injective,
    hs,
    sourceVector_position L hc hn, fun _ _ => rfl,
    fun m hm => falling_factorial N m hm, spectralValue_entire L hc hn,
    spectralValue_nonpole L hc hn, transfer_source_all L hc hn,
    transfer_continuous_representative_all L hc hn⟩

end QuantumNLS.BetheBasisBinding

#print axioms QuantumNLS.BetheBasisBinding.ext002_periodic_specialization

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheBasisBinding.ext002_periodic_specialization]
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
            throwError "Basis binding nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheSpectralContinuity.transfer_source_all,
    ``QuantumNLS.BetheSpectralContinuity.transfer_source_root,
    ``QuantumNLS.BetheSpectralContinuity.continuous_source_action,
    ``QuantumNLS.BetheEndpointProducts.endpoint_spectral_products,
    ``QuantumNLS.BethePhysicalAssembly.transfer_source_nonpole,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BethePhysicalTransfer.transfer,
    ``QuantumNLS.BetheTransferKernelAdjoint.rawPlus,
    ``QuantumNLS.BetheTransferKernelAdjoint.rawMinus,
    ``QuantumNLS.BetheOnShell.sourceRoots_onShell] do
    unless seen.contains n do
      throwError "Basis binding missing internal ingredient: {n}"
  for n in seen do
    if n == ``sorryAx ||
        (n.toString.startsWith "QuantumNLS.BetheEigen." &&
          !(n.toString.startsWith "QuantumNLS.BetheEigen.pi_ae_injective")) ||
        (n.toString.startsWith "QuantumNLS.TransferSeparation" &&
          !(#[``QuantumNLS.TransferSeparation.sFun,
          ``QuantumNLS.TransferSeparation.OnShell,
          ``QuantumNLS.TransferSeparation.shiftPoly,
          ``QuantumNLS.TransferSeparation.eval_shiftPoly,
          ``QuantumNLS.TransferSeparation.prod_plus_mul,
          ``QuantumNLS.TransferSeparation.prod_minus_mul].contains n)) then
      throwError "Basis binding forbidden dependency: {n}"
  Lean.logInfo m!"Basis binding aggregate audit PASS: {seen.size} transitive constants. Internal literal physical specialization of EXT-002; no external premise or basis conclusion."
