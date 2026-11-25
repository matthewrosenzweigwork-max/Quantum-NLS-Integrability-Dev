import QuantumNLS.TransferProductCorrection

/-! integrator-authored trusted spec for R-509F3C0C `stat:lem:product-correction`
(intrinsic/plane_foundations.tex:358). For any real tuple, G_N(z) = N⁻¹ Σ_j (z − q_j)⁻¹, f_z(u) =
e^{iκu} + e^{izL} e^{−iκu}, and S_N(z) is the exact two-product transfer expression at coupling κ/N
(ROOT_spectral_measure.tex eq:root-quantum-input). Then S_N(z) = f_z(G_N) − (κ²/(2N)) f_z(G_N) G_N'(z)
+ O_K(N⁻²), uniformly over all real tuples and all z in a fixed compact K ⊂ {Im z > 0}, with
G_N'(z) = −N⁻¹ Σ (z − q_j)⁻². Every object is written out here. -/

open Complex

namespace QuantumNLS.R509Spec

def Spec : Prop :=
  ∀ (κ L : ℝ) (K : Set ℂ), IsCompact K → (∀ z ∈ K, 0 < z.im) →
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q : Fin N → ℝ, ∀ z ∈ K,
      let G : ℂ := (N : ℂ)⁻¹ * ∑ j, (z - (q j : ℂ))⁻¹
      let f : ℂ := exp (I * κ * G) + exp (I * z * L) * exp (-(I * κ * G))
      ‖((∏ j, (1 + I * κ / (N * (z - (q j : ℂ))))) +
            exp (I * z * L) * ∏ j, (1 - I * κ / (N * (z - (q j : ℂ))))) -
          (f - (κ ^ 2 / (2 * N)) * f * (-(N : ℂ)⁻¹ * ∑ j, ((z - (q j : ℂ)) ^ 2)⁻¹))‖ ≤
        C / (N : ℝ) ^ 2

theorem spec : Spec := by
  intro κ L K hK hKup
  obtain ⟨C, N₀, h⟩ := QuantumNLS.TransferProductCorrection.product_correction_literal κ L hK hKup
  exact ⟨C, N₀, fun N hN q z hz => h N hN q z hz⟩

end QuantumNLS.R509Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R509Spec.spec
  IO.println s!"R509Spec.spec axioms: {ax}"
