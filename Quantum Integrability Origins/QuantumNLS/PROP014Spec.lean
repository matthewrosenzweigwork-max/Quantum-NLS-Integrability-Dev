import QuantumNLS.FunctionalLinearizationVarying
/-! integrator-authored trusted spec for PROP-014 lem:A4-functional-linearization (spectral_calculus.tex:497), under
VERIFIED SCOPED OWNER APPROVAL scope (2): the explicit operator-norm Bochner formulation with its measurable-family
hypotheses is accepted; those hypotheses must be PROVED in each physical application; no general-equivalence claim.
Frozen single-family form: commuting quadratures Φ_n(x_j) of a continuous functional calculus on compact K_n ⊆ Q, smooth F
on U ⊇ Q, deviation ‖(Φ_n(x_j) − b_j)ψ_n‖ ≤ δ_n → 0, commutator ‖[Φ_n(x_j), J_n]‖ ≤ C_J/N_n, derivative bounds ≤ M to
order m: b ∈ Q and sup_{|t|≤T} |difference of evolved expectations| ≤ C0·(C1·M)·T·C_J·δ_n. -/
namespace PROP014Spec
open QuantumNLS QuantumNLS.FunctionalLinearization NormedSpace ComplexConjugate MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff

theorem spec (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
        [∀ n, CompleteSpace (H n)]
        (K : ℕ → Set (EuclideanSpace ℝ (Fin d))) [∀ n, CompactSpace (K n)]
        (hKQ : ∀ n, K n ⊆ Q)
        (Φ : ∀ n, C(K n, ℂ) →⋆ₐ[ℂ] (H n →L[ℂ] H n))
        (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ContDiffOn ℝ ∞ F U)
        (b : EuclideanSpace ℝ (Fin d))
        (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) (ψ : ∀ n, H n) (hψ : ∀ n, ‖ψ n‖ = 1)
        (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
        (hψδ : ∀ n j, ‖(Φ n (coordC j) - ((b j : ℝ) : ℂ) • (1 : H n →L[ℂ] H n)) (ψ n)‖ ≤ δ n)
        (J : ∀ n, H n →L[ℂ] H n) {CJ : ℝ} (hCJ : 0 ≤ CJ)
        (hJ : ∀ n j, ‖Φ n (coordC j) * J n - J n * Φ n (coordC j)‖ ≤ CJ / N n)
        {M : ℝ} (hM0 : 0 ≤ M)
        (hFb : ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i F x‖ ≤ M)
        {T : ℝ} (hT : 0 ≤ T) (n : ℕ),
        b ∈ Q ∧
        (⨆ t : Set.Icc (-T) T,
          ‖⟪evol (HnlK (Φ n) F (N n)) t (ψ n), J n (evol (HnlK (Φ n) F (N n)) t (ψ n))⟫_ℂ -
            ⟪evol (HlinK (Φ n) F b (N n)) t (ψ n),
              J n (evol (HlinK (Φ n) F b (N n)) t (ψ n))⟫_ℂ‖) ≤
          C0 * (C1 * M) * T * CJ * δ n  :=
  functional_linearization_varying d

end PROP014Spec
#print axioms PROP014Spec.spec
