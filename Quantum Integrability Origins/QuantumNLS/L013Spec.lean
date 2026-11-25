import QuantumNLS.Local013Main
/-! integrator-authored trusted spec for LOCAL-013 reset:principal-calculus (review record r24 FULL): headline statement(s) copied verbatim from Local013Main (QuantumNLS.Local013Main). -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Filter Topology
open QuantumNLS.KernelDefinition QuantumNLS.KernelConvergence QuantumNLS.LocalPlacement
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011 QuantumNLS.SymplecticBracket
  QuantumNLS.Local013ProductSymbol QuantumNLS.Local013ProductLimit QuantumNLS.Local013PowerSeries
  QuantumNLS.Local013CommutatorLimit QuantumNLS.Local013CommutatorSeries
namespace QuantumNLS.L013Spec
open QuantumNLS.Local013Main
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 8000000 in
theorem local013_principal_calculus_spec :
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
  exact QuantumNLS.Local013Main.local013_principal_calculus 

end QuantumNLS.L013Spec
#print axioms QuantumNLS.L013Spec.local013_principal_calculus_spec
