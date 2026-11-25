import Mathlib
import QuantumNLS.L2SpatialTransfer
import QuantumNLS.RiccatiMonodromy

/-!
# R-3FEAD88B step B: L² discriminant equals the classical discriminant for continuous representatives

For an `L²` profile `u` on the circle of length `L` with a continuous representative `g : ℝ → ℂ`
(`profile u =ᵐ g` on `[0, L]`), the physical discriminant `L2SpatialTransfer.discriminant κ u z`
equals the classical discriminant `SpatialTransfer.discriminant L κ g z` (the trace of the
transfer of the unbalanced coefficient `unbalCoef κ g z` at `L`).

Chain of frozen results used:
* `L2SpatialTransfer.discriminant_eq_unbalanced`: the L² discriminant is the trace of
  `transfer (unbalCoef κ (profile u) z) L`;
* `L1SpatialTransfer.transfer_eq_of_ae`: transfers of a.e.-equal coefficients agree on `[0, L]`;
* `L2SpatialTransfer.transfer_eq_classical`: for continuous `A` the transfer agrees with any
  fundamental solution on `[0, L]`;
* `LinearFundamental.discriminant_eq_unbalanced`: the classical discriminant is the trace of an
  unbalanced fundamental solution.

Consequence (`discriminant_eq_monodromy`): with a pointwise `C¹`, `L`-periodic Riccati solution `r`
of `g`, the L² discriminant equals `m + m⁻¹`, `m = exp(-izL/2 + κ ∫₀ᴸ conj(g) r)`.

Scope: continuous representative `g` (or a continuous torus representative `v`). The Ell² fixed
point producing `g` and `r` is NOT in this module (step C). No sorry, admit, native_decide or
custom axioms.
-/

namespace QuantumNLS.RiccatiL2Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix Interval
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer
open QuantumNLS.L2SpatialTransfer (profile)

/-- **L² discriminant = classical discriminant** for a continuous representative `g` of `profile u`
on `[0, L]`. -/
theorem discriminant_eq_classical_of_ae {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) {g : ℝ → ℂ} (hg : Continuous g)
    (hae : profile u =ᵐ[volume.restrict (Icc 0 L)] g) (z : ℂ) :
    QuantumNLS.L2SpatialTransfer.discriminant κ u z
      = QuantumNLS.SpatialTransfer.discriminant L κ g z := by
  obtain ⟨Mu, hMu, hdisc⟩ := QuantumNLS.LinearFundamental.discriminant_eq_unbalanced L κ hκ hg z
  have hA : Continuous (unbalCoef κ g z) := continuous_coef κ 1 hg z
  have hAB : unbalCoef κ (profile u) z =ᵐ[volume.restrict (Icc 0 L)] unbalCoef κ g z := by
    filter_upwards [hae] with s hs
    simp only [unbalCoef, coef, hs]
  have hLmem : L ∈ Icc (0 : ℝ) L := ⟨(Fact.out : 0 < L).le, le_rfl⟩
  have hT : transfer (unbalCoef κ (profile u) z) L = transfer (unbalCoef κ g z) L :=
    transfer_eq_of_ae (Fact.out : 0 < L).le hAB hLmem
  rw [QuantumNLS.L2SpatialTransfer.discriminant_eq_unbalanced hκ u z, hdisc, hT]
  exact congrArg Matrix.trace (QuantumNLS.L2SpatialTransfer.transfer_eq_classical hA hMu hLmem)

/-- **Torus-representative form.** A continuous function `v` on the circle with `v =ᵐ u` gives the
classical discriminant of its pull-back `s ↦ v (s : AddCircle L)`. -/
theorem discriminant_eq_classical_of_torus {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) {v : AddCircle L → ℂ} (hvc : Continuous v)
    (hv : v =ᵐ[volume] u) (z : ℂ) :
    QuantumNLS.L2SpatialTransfer.discriminant κ u z
      = QuantumNLS.SpatialTransfer.discriminant L κ (fun s : ℝ => v (s : AddCircle L)) z := by
  have hq : Continuous (fun s : ℝ => (s : AddCircle L)) := AddCircle.continuous_mk' L
  have hg : Continuous (fun s : ℝ => v (s : AddCircle L)) := hvc.comp hq
  have hae : profile u =ᵐ[volume.restrict (Icc 0 L)] (fun s : ℝ => v (s : AddCircle L)) :=
    (QuantumNLS.L2SpatialTransfer.profile_ae_of_representative u hv).symm
  exact discriminant_eq_classical_of_ae hκ u hg hae z

/-- **Monodromy form.** If `g` is continuous and `r` is a pointwise `C¹`, `L`-periodic solution of
the Riccati equation `r' = iz r + g - κ conj(g) r²`, then the L² discriminant of `profile u` is
`m + m⁻¹` with `m = ψ(L)`. -/
theorem discriminant_eq_monodromy {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) {g r : ℝ → ℂ} {z : ℂ} (hg : Continuous g)
    (hae : profile u =ᵐ[volume.restrict (Icc 0 L)] g)
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + g x - (κ : ℂ) * conj (g x) * r x ^ 2) x)
    (hper : r L = r 0) :
    QuantumNLS.L2SpatialTransfer.discriminant κ u z
      = QuantumNLS.RiccatiMonodromy.psi κ g r z L
        + (QuantumNLS.RiccatiMonodromy.psi κ g r z L)⁻¹ := by
  rw [discriminant_eq_classical_of_ae hκ u hg hae z]
  exact QuantumNLS.RiccatiMonodromy.discriminant_monodromy (Fact.out : 0 < L) hκ hg hr hper

end QuantumNLS.RiccatiL2Classical

#print axioms QuantumNLS.RiccatiL2Classical.discriminant_eq_classical_of_ae
#print axioms QuantumNLS.RiccatiL2Classical.discriminant_eq_classical_of_torus
#print axioms QuantumNLS.RiccatiL2Classical.discriminant_eq_monodromy
