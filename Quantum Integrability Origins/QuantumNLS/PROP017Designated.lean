import Mathlib
import QuantumNLS.PROP017UniformN

/-!
# PROP-017, designated-cut and ε-uniform form (part (a)), and the physical remainder (part (b))

Source: `source/chapters/propagation/window_reconstruction.tex:21-31` (model items 1-2, designated cuts
`a_ℓ = (2ℓ+1)π/L`) and `:92-104` (`Q7A:prop:packet`). integrator dispatch after Terra r127: replace the
all-cuts alias `PROP017Eps` (which assumes the support gap and discriminant bound at EVERY large real cut)
by the designated-cut form. Formalization only; no status change.

## (a) Designated-cut, ε-uniform statement

`PROP017UniformN.prop017_uniform` (frozen `f5974b78`, reviewed Terra r22/r24) quantifies the support gap and
`|D| ≥ d₀` ONLY at the designated cuts: `hcut : ∀ l, l0 ≤ l → (support gap at ±cutSeq L l) ∧ (|D| ≥ d₀ on
Γ_{cutSeq L l})`, with `cutSeq L l = (2l+1)π/L`. Its quantifier order is `∃ ρ, R₀, r` then `∃ N₀` before
`∀ ε` (ε-uniform threshold), so the ε-indexed event `EN μ q R a ρ h η₀ ε b` may be specialized along a
varying ε. The bounds are the printed ones (`eq:bad`, `eq:allroots`, `eq:Gneighbor`, `eq:derivative`).

Re-exported here without a new proof:
* `prop017_designated` : the designated-cut, ε-uniform proposition.
* `prop017_designated_diagonal` : its diagonal corollary along `ε_N = N^{−γ}`, `R_N = N^θ`,
  `a_N = cutN L θ N` (designated cut), under `3γ + θ < 1` and `1 < 2pθ`.

## (b) Physical application: what remains (NOT assembled)

The round-19 readiness map (`review records/haiku_prop017_physical_inputs_round19.md`) found that no physical input
has a Lean referent. The following are required by the physical event and projection and are NOT constructed:

1. **Born law `P_{N,u}`** on root configurations `Fin N → ℝ` (the Bethe spectral resolution of `u^{⊗N}`). It
   needs the complete Bethe orthonormal basis (R-8E4D05E7, open). Without it there is no measurable root
   vector `q : Ω → Fin N → ℝ` with law `P_{N,u}`.
2. **Limit measure `μ_{κ,u}`** (`thm:root-spectral-density`, not in Lean). It gives the moments (`hmom`), the
   support gap at the designated cuts, and the referents of `G` and `D`.
3. **Quantum tail input** `E_{N,u}[N^{−1} Σ_j 1_{|q_j|>R}] ≤ C_p R^{−2p} + D_p/(N R)` for every `p`
   (`Q7A:eq:tail`), and **mean-square input** `E|G_N − G|²(x+iy) ≤ C/(N y²)` (`Q7A:eq:ms`): both need (1).
4. **Physical event and projection** `𝓔_{N,ε}` and `P^g_N` are defined from (1)-(3). They are NOT assembled here,
   because no object in (1)-(3) exists to instantiate `prop017_designated` at the physical data.

So the physical application stays a remainder. The designated-cut theorem applies to any classical measure
`μ` and any root law `q` satisfying the printed hypotheses; the physical instance is not supplied.
-/

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.PROP017Designated

/-- **PROP-017, designated-cut, ε-uniform (part (a)).** The reviewed `PROP017UniformN` proposition. -/
alias prop017_designated := QuantumNLS.PROP017UniformN.prop017_uniform

/-- **Diagonal corollary (part (a)).** Along `ε_N = N^{−γ}` with designated cuts (`PROP017UniformN`). -/
alias prop017_designated_diagonal := QuantumNLS.PROP017UniformN.prop017_diagonal

end QuantumNLS.PROP017Designated

/-! Axiom audit (PROP-017 designated-cut re-export). -/
#print axioms QuantumNLS.PROP017Designated.prop017_designated
#print axioms QuantumNLS.PROP017Designated.prop017_designated_diagonal
