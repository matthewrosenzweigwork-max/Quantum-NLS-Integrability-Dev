import QuantumNLS.BethePhysicalTransfer
import QuantumNLS.HighMomentsRank
import QuantumNLS.RootOverlapLimit

/-!
# DEF-048: normalized quantum transfer and ordered kernels
(`periodic_basis.tex` `basis:eq:plus`/`basis:eq:transfer`, `ROOT_spectral_measure.tex`
`eq:root-kernels`, `eq:root-symbol`; `DEFINITIONS_LEDGER.md:1174`)

> The ordered kernels `K_{r,z}` are the symmetric compressions of the two alternating-simplex integral kernels
> in `eq:root-kernels`. At coupling `κ/N`, the normalized transfer is
> `S_N(z) = (1+e^{izL}) Id + Σ_{r=1}^N κ^r (N)_r N^{-r} U_{N,r}(K_{r,z})`. For a unit `L²` profile, its scalar
> product symbol is the series `eq:root-symbol` on `Im z > κ`. The on-shell identity `eq:root-quantum-input` is a
> proved quantum input, not an additional definition.

Reuse (read-only) of the frozen physical Bethe modules:
* `K̃⁺_{r,z}(x;y) = 1_{L>x₁>y₁>⋯>x_r>y_r>0} e^{iz Σ(x_a−y_a)}` and
  `K̃⁻_{r,z}(x;y) = 1_{L>y₁>x₁>⋯>y_r>x_r>0} e^{izL − iz Σ(y_a−x_a)}` are `BetheTransferKernelAdjoint.rawPlus` /
  `rawMinus` (strict alternating chambers `PlusOrder`, `MinusOrder`), realized as the bounded integral operators
  `BetheTransferOperators.plusKernel/minusKernel/rawOperator` on `L²(𝕋_L^r)`;
* `K_{r,z} = P_r(K̃⁺ + K̃⁻)P_r` is `BethePhysicalTransfer.physicalKernel L r z`, a bounded kernel on
  `Sym^r L²(𝕋_L)` (`orderedKernel` below; the pairing with the raw operator is `inner_orderedKernel`);
* `U_{N,r}` is `KernelDefinition.genericU_N_r` (DEF-009) and the falling factorial convention is
  `HighMomentsRank.fallR N r = (N)_r/N^r`.

Realized here:
* `normalizedTransfer L κ N z`, the literal `S_N(z)`;
* `normalizedTransfer_eq_transfer`: it equals Sol's `BethePhysicalTransfer.transfer L N (κ/N) z` (coupling `κ/N`);
* `normalizedTransfer_eq_Xop`: it is the operator `X_N` of the PROP-008 high-moment lemma for
  `A_0 = 1 + e^{izL}`, `A_r = κ^r K_{r,z}` (`HighMomentsRank.Xop`);
* `normalizedTransfer_adjoint`: `S_N(z)^* = e^{-iL \bar z} S_N(\bar z)` (from Sol's adjoint identity);
* `productSymbol L κ u z = 1 + e^{izL} + Σ_{r≥1} κ^r ⟨u^{⊗r}, K_{r,z} u^{⊗r}⟩` (the series `eq:root-symbol`, as a
  `tsum` over `r ≥ 1`) and `productSymbol_eq_xlim` (it is `HighMomentsRank.xlim` for the same data).

Not part of the definition and not proved here: the on-shell eigenvalue identity `eq:root-quantum-input`, and the
absolute/locally uniform convergence of the series on `Im z > κ`, which rests on the sharp kernel bound
`‖K_{r,z}‖ ≤ 2 (Im z)^{-r}` of `lem:root-placement` (R-FFA8D3F2; it is not available in the frozen modules, whose
raw-operator bound is cruder).  The `tsum` is the series whenever it converges.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.NormalizedTransfer

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
open QuantumNLS.BethePhysicalTransfer QuantumNLS.HighMomentsRank

variable (L : ℝ) [Fact (0 < L)]

/-- The ordered kernel `K_{r,z} = P_r(K̃⁺_{r,z} + K̃⁻_{r,z})P_r` on `Sym^r L²(𝕋_L)`. -/
def orderedKernel (r : ℕ) (z : ℂ) : BoundedSymmetricKernel (L2T L) r :=
  physicalKernel L r z

/-- `K_{r,z}` is the compression of the raw alternating-simplex integral operator (`rawPlus + rawMinus`). -/
theorem inner_orderedKernel (r : ℕ) (z : ℂ) (f g : SymSector ℂ (L2T L) r) :
    ⟪f, orderedKernel L r z g⟫_ℂ =
      ⟪positionInclusion L r f,
        QuantumNLS.BetheTransferOperators.rawOperator L r z (positionInclusion L r g)⟫_ℂ :=
  inner_physicalKernel L r z f g

/-- **The normalized quantum transfer** `S_N(z) = (1+e^{izL}) Id + Σ_{r=1}^N κ^r (N)_r N^{-r} U_{N,r}(K_{r,z})`
on `Sym^N L²(𝕋_L)` (`U_{N,r}` = `genericU_N_r`, `(N)_r/N^r` = `fallR N r`). -/
def normalizedTransfer (κ : ℝ) (N : ℕ) (z : ℂ) :
    SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N :=
  (1 + Complex.exp (Complex.I * z * L)) • ContinuousLinearMap.id ℂ _ +
    ∑ j : Fin N, (((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ) •
      genericU_N_r N (j.val + 1) j.2 (orderedKernel L (j.val + 1) z)

/-- `S_N(z)` is the physical transfer of the frozen Bethe modules at coupling `κ/N`. -/
theorem normalizedTransfer_eq_transfer (κ : ℝ) (N : ℕ) (z : ℂ) :
    normalizedTransfer L κ N z = transfer L N (κ / N) z := by
  unfold normalizedTransfer transfer
  have hexp : Complex.exp (Complex.I * z * L) = Complex.exp (Complex.I * L * z) := by
    rw [mul_right_comm]
  rw [hexp, Fin.sum_univ_succ (n := N)]
  have h0 : transferTerm L N (κ / N) z 0 = 0 := by simp [transferTerm]
  rw [h0, zero_add]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold transferTerm
  have hpos : 0 < (Fin.succ j).val := by simp
  rw [if_pos hpos, totalPlacement_eq_genericU]
  congr 1
  simp only [Fin.val_succ, fallR]
  push_cast
  rw [div_pow]
  ring

/-- `S_N(z)` is the operator `X_N` of the high-moment lemma for `A_0 = 1+e^{izL}`, `A_r = κ^r K_{r,z}`. -/
theorem normalizedTransfer_eq_Xop (κ : ℝ) (N : ℕ) (z : ℂ) :
    normalizedTransfer L κ N z =
      Xop (1 + Complex.exp (Complex.I * z * L))
        (fun r => ((κ ^ r : ℝ) : ℂ) • orderedKernel L r z) N := by
  unfold normalizedTransfer Xop
  congr 1
  rw [Finset.sum_range (fun j => ((fallR N (j + 1) : ℝ) : ℂ) • placed
    (fun r => ((κ ^ r : ℝ) : ℂ) • orderedKernel L r z) N (j + 1))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold placed
  rw [dif_pos (show (j : ℕ) + 1 ≤ N from j.2), QuantumNLS.RootOverlapLimit.genericU_smul,
    smul_smul]
  congr 1
  push_cast
  ring

/-- The adjoint of the normalized transfer (via the frozen physical adjoint identity). -/
theorem normalizedTransfer_adjoint (κ : ℝ) (N : ℕ) (z : ℂ) :
    (normalizedTransfer L κ N z).adjoint =
      QuantumNLS.BetheTransferKernelAdjoint.adjointPhase L z • normalizedTransfer L κ N (conj z) := by
  rw [normalizedTransfer_eq_transfer, normalizedTransfer_eq_transfer]
  exact transfer_adjoint L N _ z

/-! ### The scalar product symbol -/

/-- The `r`-th term `κ^r ⟨u^{⊗r}, K_{r,z} u^{⊗r}⟩` of the product symbol series. -/
def symbolTerm (κ : ℝ) (u : L2T L) (z : ℂ) (r : ℕ) : ℂ :=
  ((κ ^ r : ℝ) : ℂ) * kernelProductSymbol (orderedKernel L r z) u

/-- **The scalar product symbol** `s(z;u) = 1 + e^{izL} + Σ_{r≥1} κ^r ⟨u^{⊗r}, K_{r,z} u^{⊗r}⟩`
(`eq:root-symbol`; the sum is over `r ≥ 1`). -/
def productSymbol (κ : ℝ) (u : L2T L) (z : ℂ) : ℂ :=
  1 + Complex.exp (Complex.I * z * L) + ∑' j : ℕ, symbolTerm L κ u z (j + 1)

theorem kernelProductSymbol_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {r : ℕ} (c : ℂ) (A : BoundedSymmetricKernel H r) (u : H) :
    kernelProductSymbol (c • A) u = c * kernelProductSymbol A u := by
  simp [kernelProductSymbol, inner_smul_right]

/-- The series is `xlim` of the high-moment lemma for the same data. -/
theorem productSymbol_eq_xlim (κ : ℝ) (u : L2T L) (z : ℂ) :
    productSymbol L κ u z =
      xlim u (1 + Complex.exp (Complex.I * z * L))
        (fun r => ((κ ^ r : ℝ) : ℂ) • orderedKernel L r z) := by
  unfold productSymbol xlim symbolTerm aa
  simp only [kernelProductSymbol_smul]

#print axioms normalizedTransfer_eq_transfer
#print axioms normalizedTransfer_eq_Xop
#print axioms normalizedTransfer_adjoint
#print axioms productSymbol_eq_xlim

end QuantumNLS.NormalizedTransfer
