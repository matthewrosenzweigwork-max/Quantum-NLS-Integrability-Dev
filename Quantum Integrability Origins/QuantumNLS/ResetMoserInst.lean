import QuantumNLS.ResetMoserIsotropy

/-!
# `thm:reset-moser` (LOCAL-017): instance shim for the bounded two-forms `Form = K →L[ℝ] K →L[ℝ] ℝ`

In the ambient context (`InnerProductSpace.complexToReal` as a local instance on `K = ℓ²(ℤ;ℂ)`) typeclass search does not
find `AddGroup Form` / `ContinuousSub Form` / `NormSMulClass ℝ Form` by itself, although the Mathlib instances
`ContinuousLinearMap.toNormedAddCommGroup` and `ContinuousLinearMap.toNormedSpace` apply verbatim. This module only
registers those two Mathlib instances for `Form` (no new mathematics, no axioms).
-/

set_option autoImplicit false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive

instance instFormNormedAddCommGroup : NormedAddCommGroup Form := ContinuousLinearMap.toNormedAddCommGroup
instance instFormNormedSpace : NormedSpace ℝ Form := ContinuousLinearMap.toNormedSpace

end QuantumNLS.ResetMoser
