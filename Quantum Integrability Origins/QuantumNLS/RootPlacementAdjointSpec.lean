import QuantumNLS.RootSymbolConvergence
import QuantumNLS.BasisAdjoint

/-! integrator-authored trusted spec for R-FFA8D3F2 `lem:root-placement` (ROOT_spectral_measure.tex:55 ff),
R-99FDE9B6 `basis:lem:adjoint` (periodic_basis.tex:378 ff) and DEF-048 "Normalized quantum transfer and ordered
kernels" (DEFINITIONS_LEDGER.md:1174). K_{r,z} is the compression of the alternating-simplex kernels of
eq:root-kernels (Sol's `physicalKernel`; trusted import, Terra r103); U_{N,r} the realized DEF-009 placement.
DEF-048: S_N(z) = (1 + e^{izL}) Id + Σ_{r=1}^N κ^r (N)_r N^{−r} U_{N,r}(K_{r,z}) with (N)_r N^{−r} =
N.descFactorial r / N^r; the symbol 1 + e^{izL} + Σ_{r≥1} κ^r ⟨u^{⊗r}, K_{r,z}u^{⊗r}⟩ converges absolutely and
locally uniformly on Im z > κ (κ ≥ 0, unit u).
R-FFA8D3F2: ‖K_{r,z}‖ ≤ 2 (Im z)^{−r}; ⟨u^{⊗N}, U_{N,r}(A)u^{⊗N}⟩ = ⟨u^{⊗r}, A u^{⊗r}⟩; and
‖(U_{N,r}(A) − a) u^{⊗N}‖ ≤ 2r‖A‖/√N.
R-99FDE9B6: K_{m,z}* = e^{−iL z̄} K_{m,z̄}; U_{N,m} preserves adjoints; S_{N,c}(z)* = e^{−iL z̄} S_{N,c}(z̄);
T(x) = e^{−iLx/2} S_{N,c}(x) is self-adjoint for real x. -/

open Filter Topology
open scoped InnerProductSpace ComplexConjugate
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
open QuantumNLS.NormalizedTransfer QuantumNLS.BethePhysicalTransfer QuantumNLS.HighMomentsRank

namespace QuantumNLS.RootPlacementAdjointSpec

variable {L : ℝ} [Fact (0 < L)]

/-- DEF-048: literal operator and symbol, and the strip convergence. -/
theorem spec_def048 (κ : ℝ) (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) :
    (∀ N z, normalizedTransfer L κ N z =
      (1 + Complex.exp (Complex.I * z * L)) • ContinuousLinearMap.id ℂ _ +
        ∑ j : Fin N, (((κ ^ (j.val + 1) : ℝ) * ((N.descFactorial (j.val + 1) : ℝ) / (N : ℝ) ^ (j.val + 1)) : ℝ) : ℂ) •
          genericU_N_r N (j.val + 1) j.2 (physicalKernel L (j.val + 1) z)) ∧
    (∀ z r, symbolTerm L κ u z r = ((κ ^ r : ℝ) : ℂ) * kernelProductSymbol (physicalKernel L r z) u) ∧
    (∀ z, productSymbol L κ u z = 1 + Complex.exp (Complex.I * z * L) + ∑' j : ℕ, symbolTerm L κ u z (j + 1)) ∧
    (∀ z : ℂ, κ < z.im → Summable (fun j : ℕ => ‖symbolTerm L κ u z (j + 1)‖)) ∧
    TendstoLocallyUniformlyOn (fun (n : ℕ) (z : ℂ) => ∑ j ∈ Finset.range n, symbolTerm L κ u z (j + 1))
      (fun z => ∑' j : ℕ, symbolTerm L κ u z (j + 1)) atTop {z : ℂ | κ < z.im} :=
  ⟨fun N z => rfl, fun z r => rfl, fun z => rfl,
    fun z hz => RootSymbolConvergence.summable_norm_symbolTerm κ hκ u hu z hz,
    RootSymbolConvergence.tendstoLocallyUniformlyOn_symbol κ hκ u hu⟩

/-- R-FFA8D3F2. -/
theorem spec_rootPlacement (u : L2T L) (hu : ‖u‖ = 1) {N r : ℕ} (hr1 : 1 ≤ r) (hrN : r ≤ N) (z : ℂ)
    (hη : 0 < z.im) :
    ‖physicalKernel L r z‖ ≤ 2 * (z.im)⁻¹ ^ r ∧
    (∀ A : BoundedSymmetricKernel (L2T L) r,
      ⟪(QuantumNLS.ProductPreparation.PositiveMassPreparation.bosonicProduct (L := L) N u),
        genericU_N_r N r hrN A (QuantumNLS.ProductPreparation.PositiveMassPreparation.bosonicProduct (L := L) N u)⟫_ℂ =
        ⟪(htpow r u : HilbertTensorPower ℂ (L2T L) r),
          ((A ⟨htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ (L2T L) r) : HilbertTensorPower ℂ (L2T L) r)⟫_ℂ ∧
      ‖(genericU_N_r N r hrN A - kernelProductSymbol A u • (1 : BoundedSymmetricKernel (L2T L) N))
          (QuantumNLS.ProductPreparation.PositiveMassPreparation.bosonicProduct (L := L) N u)‖ ≤
        2 * r * ‖A‖ / Real.sqrt N) :=
  RootPlacementBound.lem_root_placement u hu hr1 hrN z hη

/-- R-99FDE9B6. -/
theorem spec_adjoint :
    (∀ (m : ℕ) (z : ℂ), (physicalKernel L m z).adjoint =
      Complex.exp (-Complex.I * L * conj z) • physicalKernel L m (conj z)) ∧
    (∀ (N m : ℕ) (hm : m ≤ N) (K : SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m),
      (genericU_N_r N m hm K).adjoint = genericU_N_r N m hm K.adjoint) ∧
    (∀ (N : ℕ) (c : ℝ) (z : ℂ), (transfer L N c z).adjoint =
      Complex.exp (-Complex.I * L * conj z) • transfer L N c (conj z)) ∧
    (∀ (N : ℕ) (c x : ℝ), IsSelfAdjoint (Complex.exp (-Complex.I * L * x / 2) • transfer L N c x)) :=
  ⟨fun m z => BasisAdjoint.kernel_adjoint L m z, fun N m hm K => BasisAdjoint.placement_adjoint' L N m hm K,
    fun N c z => BasisAdjoint.transfer_adjoint' L N c z, fun N c x => BasisAdjoint.T_selfAdjoint L N c x⟩

end QuantumNLS.RootPlacementAdjointSpec

open Lean in
#eval show CoreM Unit from do
  for n in [``QuantumNLS.RootPlacementAdjointSpec.spec_def048, ``QuantumNLS.RootPlacementAdjointSpec.spec_rootPlacement,
      ``QuantumNLS.RootPlacementAdjointSpec.spec_adjoint] do
    let ax ← Lean.collectAxioms n
    IO.println s!"{n} axioms: {ax}"
