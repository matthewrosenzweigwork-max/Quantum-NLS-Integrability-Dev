import QuantumNLS.Local013PowerSeries
import QuantumNLS.Local013CommutatorSeries

/-!
# LOCAL-013 `reset:principal-calculus` (`source-text/chapters/local/quantum_periods.tex:118-129`)

Printed statement. "Convergent families are closed under products and norm-convergent scalar power
series whose absolute kernel norms lie strictly inside their convergence disks, after reducing the
radius if necessary. Products have product symbols. If `H_N, B_N` are convergent families with a
uniform radius strictly greater than `R > 1`, then `iN[H_N, B_N]` is a convergent family on every
radius `r < R`, and its symbol is `{b,h}` for `ω = 2 Im⟨·,·⟩`. The Hamiltonian and the test may
have complex coefficients; brackets are extended complex bilinearly."

Realized objects (all frozen, read-only): DEF-042 `KernelConvergence.ConvergesOnRadius` and
`KernelConvergence.symbol`; DEF-050 `RadiusBound.radiusBound` and `RadiusBound.represented`;
LOCAL-011 chosen product lists `chosenProductKernelList` and commutator lists
`positiveOverlapCommutatorList`; DEF-015 `SymplecticBracket.pbC` (complex bilinear extension of
`{F,G} = dF[X_G]`, `ω = 2 Im⟨·,·⟩`). Kernels are arbitrary bounded operators on `Sym^p H`
(complex coefficients, no self-adjointness).

`local013_principal_calculus` is the single theorem; its three conjuncts are the three printed
clauses:
1. products (radius `R ≥ 1`): the chosen product lists converge on `R`, represent `A_N B_N`, and
   the product symbol is `a b` on `‖v‖² < R`;
2. power series: if `A` converges on `R`, `1 ≤ r ≤ R` (radius reduction) and the absolute kernel
   norms satisfy `‖A_N‖_r ≤ M < ρ` with `Σ ‖c_k‖ ρ^k < ∞`, then `f(A)_N = Σ c_k A_N^k`
   converges on `r`, represents `Σ c_k (A_N)^k`, and has symbol `Σ c_k a^k` on `‖v‖² < r`;
3. commutators: if `H, B` converge on `R₀ > R > 1`, then for every `0 ≤ r < R` the LOCAL-011
   commutator lists of `iN[H_N, B_N]` converge on `r`, and the symbol is `{b, h}` on `‖v‖² < r`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Filter Topology
open QuantumNLS.KernelDefinition QuantumNLS.KernelConvergence QuantumNLS.LocalPlacement
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011 QuantumNLS.SymplecticBracket
  QuantumNLS.Local013ProductSymbol QuantumNLS.Local013ProductLimit QuantumNLS.Local013PowerSeries
  QuantumNLS.Local013CommutatorLimit QuantumNLS.Local013CommutatorSeries

namespace QuantumNLS.Local013Main

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
/-- **LOCAL-013 (`reset:principal-calculus`).** -/
theorem local013_principal_calculus :
    -- (1) closure under products, with product symbols
    (∀ {R : ℝ}, 1 ≤ R → ∀ {A B : ∀ N : ℕ, KernelList (H := H) N}
        {Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p},
        ConvergesOnRadius R A Alim → ConvergesOnRadius R B Blim →
        ConvergesOnRadius R (fun N => chosenProductKernelList N (A N) (B N))
            (prodLim Alim Blim) ∧
          (∀ N, QuantumNLS.RadiusBound.represented (chosenProductKernelList N (A N) (B N)) =
            (QuantumNLS.RadiusBound.represented (A N)).comp
              (QuantumNLS.RadiusBound.represented (B N))) ∧
          ∀ v : H, ‖v‖ ^ 2 < R →
            symbol (prodLim Alim Blim) v = symbol Alim v * symbol Blim v) ∧
    -- (2) closure under norm-convergent scalar power series, after reducing the radius
    (∀ {R r M ρ : ℝ} {c : ℕ → ℂ} {A : ∀ N : ℕ, KernelList (H := H) N}
        {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p},
        1 ≤ r → r ≤ R → ConvergesOnRadius R A Alim → 0 ≤ M →
        (∀ N, QuantumNLS.RadiusBound.radiusBound r (A N) ≤ M) → M < ρ →
        Summable (fun k => ‖c k‖ * ρ ^ k) →
        ConvergesOnRadius r (psList c A) (psLim c Alim) ∧
          (∀ N, QuantumNLS.RadiusBound.represented (psList c A N) =
            ∑' k, c k • (QuantumNLS.RadiusBound.represented (A N)) ^ k) ∧
          ∀ v : H, ‖v‖ ^ 2 < r →
            symbol (psLim c Alim) v = ∑' k, c k * (symbol Alim v) ^ k) ∧
    -- (3) commutators: `iN[H_N, B_N]` converges on every `r < R` with symbol `{b, h}`
    (∀ {R₀ R : ℝ} {Hf B : ∀ N : ℕ, KernelList (H := H) N}
        {Hlim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p},
        1 < R → R < R₀ → ConvergesOnRadius R₀ Hf Hlim → ConvergesOnRadius R₀ B Blim →
        ∀ r : ℝ, 0 ≤ r → r < R →
          ConvergesOnRadius r (fun N => positiveOverlapCommutatorList N (Hf N) (B N))
              (commLim Hlim Blim) ∧
            (∀ N, QuantumNLS.RadiusBound.represented
                (positiveOverlapCommutatorList N (Hf N) (B N)) =
              ((Complex.I : ℂ) * (N : ℂ)) •
                ((QuantumNLS.RadiusBound.represented (Hf N)).comp
                    (QuantumNLS.RadiusBound.represented (B N)) -
                  (QuantumNLS.RadiusBound.represented (B N)).comp
                    (QuantumNLS.RadiusBound.represented (Hf N)))) ∧
            ∀ v : H, ‖v‖ ^ 2 < r →
              symbol (commLim Hlim Blim) v = pbC (symbol Blim) (symbol Hlim) v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R hR A B Alim Blim hA hB
    obtain ⟨h1, h2, h3⟩ := product_converges hR hA hB
    exact ⟨h1, h2, fun v hv => h3 v hv.le⟩
  · intro R r M ρ c A Alim hr hrR hA hM0 hM hMρ hc
    have hAr := QuantumNLS.TerraMultiRound15LocalPartial.convergence_radius_reduction
      (by linarith) hrR hA
    obtain ⟨h1, h2, h3⟩ := powerSeries_converges hr hAr hM0 hM hMρ hc
    exact ⟨h1, h2, fun v hv => h3 v hv.le⟩
  · intro R₀ R Hf B Hlim Blim hR1 hRR₀ hH hB r hr0 hrR
    have hR₀1 : 1 < R₀ := lt_trans hR1 hRR₀
    set r' : ℝ := max r 1 with hr'
    have hr'1 : 1 ≤ r' := le_max_right _ _
    have hr'R₀ : r' < R₀ := max_lt (by linarith) hR₀1
    have hrr' : r ≤ r' := le_max_left _ _
    obtain ⟨hc, hrep⟩ := commutator_converges hr'1 hr'R₀ hH hB
    refine ⟨QuantumNLS.TerraMultiRound15LocalPartial.convergence_radius_reduction hr0 hrr' hc,
      hrep, fun v hv => ?_⟩
    obtain ⟨_, hHs, _, _, _⟩ := kernel_convergence (by linarith) hH
    obtain ⟨_, hBs, _, _, _⟩ := kernel_convergence (by linarith) hB
    exact symbol_commLim hR₀1 hHs hBs v (by linarith)

end QuantumNLS.Local013Main

#print axioms QuantumNLS.Local013Main.local013_principal_calculus
