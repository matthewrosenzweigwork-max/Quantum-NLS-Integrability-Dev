import QuantumNLS.Local020Final
/-! integrator-authored trusted spec for LOCAL-020 prop:reset-spectral-covariance (terra_review r210 FULL ACCEPT): headline statement(s) copied verbatim from Local020Final (QuantumNLS.Local020Final). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology ComplexConjugate BoundedContinuousFunction
open QuantumNLS.LocalSpectral
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (Pkg gcoef)
open QuantumNLS.Fourier (modeLp)
open QuantumNLS.RootIndexedMasses (masses)
namespace QuantumNLS.L020Spec
open QuantumNLS.Local020Final
variable {L κ r : ℝ} [Fact (0 < L)]
open QuantumNLS.Local020Fin1 (Dat)

set_option maxHeartbeats 8000000 in
theorem reset_spectral_covariance_spec (hκ : 0 < κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
        -- the family `g_n = gcoef · b_n` (polar-normalized Riesz reduction) and the exact-mass factors `r_n = rr_n`
        (∀ n : ℤ, Pkg L κ r ρ C n (a n) (b n)) ∧
        AnalyticOnNhd ℝ rr (ball (0 : L2T L) ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          (masses hκ u).1 n = ‖gcoef L κ * b n u‖ ^ 2 * rr u n) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, 1 / 2 < rr u n ∧ rr u n < 3 / 2) ∧
        -- covariances of `g_n`
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          (∀ y : ℝ, gcoef L κ * b n (QuantumNLS.BornTranslation.trans y u) =
            Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * (gcoef L κ * b n u)) ∧
          (∀ k : ℤ, gcoef L κ * b n (QuantumNLS.RootMassBoostSymbol.boost k u) = gcoef L κ * b (n - k) u) ∧
          gcoef L κ * b n (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) = gcoef L κ * b (-n) u ∧
          gcoef L κ * b n (star u) = conj (gcoef L κ * b (-n) u) ∧
          (∀ φ : ℝ, gcoef L κ * b n (Complex.exp ((φ : ℂ) * Complex.I) • u) =
            Complex.exp ((φ : ℂ) * Complex.I) * (gcoef L κ * b n u))) ∧
        -- index permutations of `r_n`; unchanged by translations and common phase
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          (∀ y : ℝ, rr (QuantumNLS.BornTranslation.trans y u) n = rr u n) ∧
          (∀ k : ℤ, rr (QuantumNLS.RootMassBoostSymbol.boost k u) n = rr u (n - k)) ∧
          rr (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = rr u (-n) ∧
          rr (star u) n = rr u (-n) ∧
          (∀ φ : ℝ, rr (Complex.exp ((φ : ℂ) * Complex.I) • u) n = rr u n)) ∧
        -- `ζ_n = g_n √r_n` has precisely the Fourier covariances
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          (∀ y : ℝ, zeta L κ b rr (QuantumNLS.BornTranslation.trans y u) n =
            Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * zeta L κ b rr u n) ∧
          (∀ k : ℤ, zeta L κ b rr (QuantumNLS.RootMassBoostSymbol.boost k u) n = zeta L κ b rr u (n - k)) ∧
          zeta L κ b rr (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = zeta L κ b rr u (-n) ∧
          zeta L κ b rr (star u) n = conj (zeta L κ b rr u (-n)) ∧
          (∀ φ : ℝ, zeta L κ b rr (Complex.exp ((φ : ℂ) * Complex.I) • u) n =
            Complex.exp ((φ : ℂ) * Complex.I) * zeta L κ b rr u n)) ∧
        -- in particular `ζ_n(C R u) = conj ζ_n(u)`
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          zeta L κ b rr (QuantumNLS.ResetNormalizationUniqueness.Cphys L u) n = conj (zeta L κ b rr u n)) ∧
        -- `ζ = 𝓕` on every single Fourier plane `u = c e_k`
        (∀ (k : ℤ) (c : ℂ), ‖c‖ < ρ → ∀ n : ℤ,
          zeta L κ b rr (c • modeLp L k) n =
            QuantumNLS.Fourier.coeff L (((c • modeLp L k : L2T L)) : AddCircle L → ℂ) n) ∧
        -- scaling `ζ_κ(s u) = s ζ_{κ s²}(u)` on common domains (against every LOCAL-007 family at coupling `κ s²`)
        (∀ s : ℝ, 0 < s → ∀ (hκ₂ : 0 < κ * s ^ 2) (ρ₂ C₂ : ℝ), 0 < ρ₂ → 0 ≤ C₂ →
          ∀ (a₂ : ℤ → L2T L → ℝ) (b₂ : ℤ → L2T L → ℂ) (rr₂ : L2T L → (ℤ →ᵇ ℝ)),
            (∀ n : ℤ, Pkg L (κ * s ^ 2) r ρ₂ C₂ n (a₂ n) (b₂ n)) →
            AnalyticOnNhd ℝ rr₂ (ball (0 : L2T L) ρ₂) →
            (∀ u ∈ ball (0 : L2T L) ρ₂, ∀ n : ℤ,
              (masses hκ₂ u).1 n = ‖gcoef L (κ * s ^ 2) * b₂ n u‖ ^ 2 * rr₂ u n) →
            ∀ u : L2T L, ‖u‖ < ρ₂ → s * ‖u‖ < ρ → ∀ n : ℤ,
              gcoef L κ * b n ((s : ℂ) • u) = (s : ℂ) * (gcoef L (κ * s ^ 2) * b₂ n u) ∧
              rr ((s : ℂ) • u) n = rr₂ u n ∧
              zeta L κ b rr ((s : ℂ) • u) n = (s : ℂ) * zeta L (κ * s ^ 2) b₂ rr₂ u n) := by
  exact QuantumNLS.Local020Final.reset_spectral_covariance hκ hr hr2

end QuantumNLS.L020Spec
#print axioms QuantumNLS.L020Spec.reset_spectral_covariance_spec
