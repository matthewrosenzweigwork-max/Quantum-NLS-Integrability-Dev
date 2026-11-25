import QuantumNLS.R52CFScalar
import QuantumNLS.R52CFCompact

/-!
# R-52CF5DA1 stage 14a: the second printed clause, uniformly on the profile class

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101): "On the same profile class each fixed intensive
count has a strong scalar limit `I_n(u)`, uniformly." Proof: "Finally the `L²` closure of the smooth unit `H¹` ball
of radius `R` is compact. Cover it by the fixed rough-center neighborhoods above and take a finite subcover. Taking
maxima of the finitely many constants ... proves the asserted uniform convergence."

**`clause2`**: for every `R`, every label `n` and every `ε > 0` there is `N₀` such that for all `N ≥ N₀` and every
smooth unit profile `u` with DEF-002 `H¹` norm at most `R` (stage 7 `profileClass`),
`‖(M_{N,n}/N - I_n(u)) u^{⊗N}‖ ≤ ε` (`M_{N,n}/N` = the accepted PROP-010 normalized count `B`, `I_n` = `mass`).
Ingredients: stage 11b `scalar_local` at every point of the compact closure, stage 7 `closure_compact` and
`uniform_of_local`.  No hypothesis is added; all inherited modules are read-only.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open Set Filter Topology

namespace QuantumNLS.R52CFClause2

open PhysicalTensor (L2T)
open RootMassInvolutionR8 (mass)

variable (L : ℝ) [Fact (0 < L)] {κ : ℝ}

/-- **Clause 2 of `prop:audit-finite-count-propagation`.** -/
theorem clause2 (hκ : 0 < κ) (R : ℝ) (n : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N → ∀ u ∈ R52CFCompact.profileClass L R,
      ‖(Prop010ContourBindingR11.B L hκ hN n - ((mass hκ n u : ℝ) : ℂ) •
        (1 : BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N))
        (HighMomentsOps.wvec N u)‖ ≤ ε := by
  obtain ⟨hK, hunit⟩ := R52CFCompact.closure_compact (L := L) R
  let P : ℕ → L2T L → Prop := fun N v => ∀ hN : 0 < N, ‖v‖ = 1 →
    ‖(Prop010ContourBindingR11.B L hκ hN n - ((mass hκ n v : ℝ) : ℂ) •
      (1 : BetheCoefficientTransform.HN L N →L[ℂ] BetheCoefficientTransform.HN L N))
      (HighMomentsOps.wvec N v)‖ ≤ ε
  obtain ⟨N₀, hN₀⟩ := R52CFCompact.uniform_of_local hK P (fun x hx => by
    obtain ⟨U, hU, hloc⟩ := R52CFScalar.scalar_local L hκ x (hunit x hx) n
    obtain ⟨N₁, h₁⟩ := hloc ε hε
    exact ⟨U, hU, N₁, fun N hN v hv hN' hv1 => h₁ N hN' hN v hv hv1⟩)
  refine ⟨N₀, fun N hN hNN u hu => ?_⟩
  exact hN₀ N hNN u (subset_closure hu) hN hu.2.1

end QuantumNLS.R52CFClause2

#print axioms QuantumNLS.R52CFClause2.clause2
