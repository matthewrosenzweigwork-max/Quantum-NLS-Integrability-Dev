import QuantumNLS.LocalSpectralReduced
/-! integrator-authored trusted spec for DEF-049 (DEFINITIONS_LEDGER.md def:report-49; sec:local-spectral,
spectral_reduction.tex analytic-coordinate subsection), parametric (well-posedness/radius/analyticity are theorem
conclusions, not asserted). On L²(0,L;ℂ²): D_σ = {f ∈ H¹ : f(L) = σ f(0)} (H¹ = absolutely continuous with L²
derivative); 𝓛_u = 2i diag(1,−1)∂_x + [[0, −2i√κ ū],[2i√κ u, 0]] on D_σ (as a graph); at the free value 2πn/L the
parity is (−1)^n (free eigenfunctions χ_{n,j} ∈ D_{(−1)^n}, eigenvalue p_n, parity unique); Riesz projection
P_n(u) = (2πi)⁻¹∮_{|z−p_n|=r}(z−𝓛_u)⁻¹dz; normalized rank-two compression on PH ≅ ℂ² via E = (χ_{n,1},χ_{n,2}):
C_n = E*P_n(u)E, U_n = P_n(u) E C_n^{-1/2} with the binomial series on ℂ² under the explicit smallness ‖C_n − 1‖ < 1
(proved summable), B_n = p_n 1 + U_n^*((2πi)⁻¹∮(z−p_n)(z−𝓛_u)⁻¹dz)U_n. -/
namespace DEF049Spec
open QuantumNLS QuantumNLS.LocalSpectral MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem spec :
    (∀ (L : ℝ) (σ : ℤˣ) (f : H2 L), f ∈ domain L σ ↔
      ∃ g h, ((f : ℝ → E2) =ᵐ[μI L] g ∧ MemLp h 2 (μI L) ∧
        ∀ x ∈ Set.Icc 0 L, g x = g 0 + ∫ s in (0 : ℝ)..x, h s) ∧ g L = (((σ : ℤ) : ℂ)) • g 0) ∧
    (∀ (L κ : ℝ) (u : ℝ → ℂ) (σ : ℤˣ) (p : H2 L × H2 L), p ∈ LuGraph L κ u σ ↔
      ∃ g h, IsH1Rep L p.1 g h ∧ g L = (((σ : ℤ) : ℂ)) • g 0 ∧
        (p.2 : ℝ → E2) =ᵐ[μI L] fun x => (2 * Complex.I) • vec2 (h x 0) (-(h x 1)) +
          vec2 (-(2 * Complex.I) * (Real.sqrt κ : ℂ) * conj (u x) * g x 1)
            ((2 * Complex.I) * (Real.sqrt κ : ℂ) * u x * g x 0)) ∧
    (∀ (m : ℤ), parity m = if Even m then 1 else -1) ∧
    (∀ (L : ℝ), 0 < L → ∀ (κ : ℝ) (m : ℤ) (j : Fin 2), chi L m j ∈ domain L (parity m) ∧
      (chi L m j, ((2 * Real.pi * m / L : ℝ) : ℂ) • chi L m j) ∈ LuGraph L κ (fun _ => 0) (parity m)) ∧
    (∀ (L : ℝ), 0 < L → ∀ (m : ℤ) (j : Fin 2) (σ' : ℤˣ),
      chiFun L m j L = (((σ' : ℤˣ) : ℤ) : ℂ) • chiFun L m j 0 → σ' = parity m) ∧
    (∀ (L : ℝ), 0 < L → ∀ (n : ℤ) (i j : Fin 2), ⟪chi L n i, chi L n j⟫_ℂ = if i = j then 1 else 0) ∧
    (∀ (L κ : ℝ) (u : ℝ → ℂ) (σ : ℤˣ) (n : ℤ) (r : ℝ), rieszProj L κ u σ n r =
      ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • circleIntegral (fun z => resolvent L κ u σ z) ((pm L n : ℂ)) r) ∧
    (∀ (L κ : ℝ) (u : ℝ → ℂ) (n : ℤ) (r : ℝ), compressionMatrix L κ u n r =
      (ContinuousLinearMap.adjoint (embed L n)) ∘L (perturbedProj L κ u n r) ∘L (embed L n)) ∧
    (∀ (L κ : ℝ) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) (h : SmallCompression L κ u n r),
      HasSum (fun k : ℕ => (invSqrtCoeff k : ℂ) • (compressionMatrix L κ u n r - 1) ^ k)
        (invSqrtCompression L κ u n r h) ∧
      normalizedIsometry2 L κ u n r h =
        (perturbedProj L κ u n r) ∘L (embed L n) ∘L (invSqrtCompression L κ u n r h) ∧
      reducedMatrix2 L κ u n r h = (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2 +
        (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ u n r h)) ∘L
          (((2 * Real.pi * Complex.I)⁻¹ : ℂ) • circleIntegral
            (fun z => (z - (pm L n : ℂ)) • resolvent L κ u (parity n) z) ((pm L n : ℂ)) r) ∘L
          (normalizedIsometry2 L κ u n r h)) := by
  refine ⟨fun L σ f => Iff.rfl, fun L κ u σ p => Iff.rfl, fun m => rfl,
    fun L hL κ m j => ⟨chi_mem_domain hL m j, free_eigen hL κ m j⟩,
    fun L hL m j σ' h => parity_unique hL m j σ' h, fun L hL n i j => inner_chi hL n i j,
    fun L κ u σ n r => rfl, fun L κ u n r => rfl,
    fun L κ u n r h => ⟨hasSum_invSqrtCompression L κ u n r h, rfl, rfl⟩⟩

end DEF049Spec
#print axioms DEF049Spec.spec
