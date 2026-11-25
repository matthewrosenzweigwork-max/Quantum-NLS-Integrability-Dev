import QuantumNLS.Local023Final
/-! integrator-authored trusted spec for LOCAL-023 thm:reset-open-transform (terra_review r216 FULL ACCEPT): headline statement(s) copied verbatim from Local023Final (QuantumNLS.Local023). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory BoundedContinuousFunction
namespace QuantumNLS.L023Spec
open QuantumNLS.Local023
open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 modeLp)
open QuantumNLS.Local021 QuantumNLS.Local021R
open QuantumNLS.LocalSpectral (pm)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.ResetNormalizationUniqueness (IsStronglySymplecticOn Cphys)

set_option maxHeartbeats 8000000 in
theorem reset_open_transform_spec (L : ℝ) [Fact (0 < L)] :
    ∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧
    ∃ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L),
      (∀ (κ : ℝ) (hκ : 0 < κ),
        -- (a) `Φ_κ : B_δ(L²) → B_δ(ℓ²)` is a real-analytic diffeomorphism, `δ = d/√κ`
        AnalyticOnNhd ℝ (Φ κ) (ball (0 : L2T L) (d / Real.sqrt κ)) ∧
        AnalyticOnNhd ℝ (Ψ κ) (ball (0 : K) (d / Real.sqrt κ)) ∧
        MapsTo (Φ κ) (ball (0 : L2T L) (d / Real.sqrt κ)) (ball (0 : K) (d / Real.sqrt κ)) ∧
        MapsTo (Ψ κ) (ball (0 : K) (d / Real.sqrt κ)) (ball (0 : L2T L) (d / Real.sqrt κ)) ∧
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), Ψ κ (Φ κ u) = u) ∧
        (∀ y ∈ ball (0 : K) (d / Real.sqrt κ), Φ κ (Ψ κ y) = y) ∧
        -- (b) the procedure: the LOCAL-020 families exist at coupling `κ`; on each of them the constructed LOCAL-017/LOCAL-021 data have all printed
        --     properties and `Φ = S⁻¹ ∘ ζ` of the procedure equals `Φ_κ` on the common domain
        (∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
            Fam020 L κ (Real.pi / L) ρ C hκ a b rr) ∧
        (∀ (ρ C : ℝ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
          0 < ρ → 0 ≤ C → Fam020 L κ (Real.pi / L) ρ C hκ a b rr →
          ∃ S : Setting L κ (Real.pi / L) hκ, S.ρ = ρ ∧ S.C = C ∧ S.a = a ∧ S.b = b ∧ S.rr = rr ∧
            SettingProps S ∧
            ∀ u : L2T L, ‖u‖ < S.rM → Real.sqrt κ * ‖u‖ < d → S.Phi u = Φ κ u) ∧
        -- (c) `|Φ_κ(u)_n|² = I_n^{(κ)}(u)`
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ n : ℤ, ‖Φ κ u n‖ ^ 2 = (masses hκ u).1 n) ∧
        -- (d) `‖Φ_κ(u)‖² = ‖u‖²`
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ‖Φ κ u‖ ^ 2 = ‖u‖ ^ 2) ∧
        -- (e) `DΦ_κ(0) = 𝓕`
        (∀ h : L2T L, fderiv ℝ (Φ κ) 0 h = fourierL2 L h) ∧
        -- (f) `2 Im ⟨DΦ_κ(u)h, DΦ_κ(u)k⟩ = 2 Im ⟨h, k⟩`
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ h k : L2T L,
          2 * (inner ℂ (fderiv ℝ (Φ κ) u h) (fderiv ℝ (Φ κ) u k)).im = 2 * (inner ℂ h k).im) ∧
        -- (g) bounded invertible differentials, with `D(Φ_κ⁻¹)(Φ_κ(u))` the inverse, and the printed quadratic bound
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∃ e : L2T L ≃L[ℝ] K,
          ⇑e = ⇑(fderiv ℝ (Φ κ) u) ∧ HasFDerivAt (Ψ κ) (e.symm : K →L[ℝ] L2T L) (Φ κ u) ∧
          ‖fderiv ℝ (Φ κ) u - Setting.Fcl L‖ +
            ‖(e.symm : K →L[ℝ] L2T L) - ((Setting.Fcle L).symm : K →L[ℝ] L2T L)‖ ≤ CL * κ * ‖u‖ ^ 2) ∧
        -- (h) Fourier covariances: translations, integral boosts, reflection, conjugation, common phase, conjugation-reflection
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ n : ℤ,
          (∀ y : ℝ, Φ κ (QuantumNLS.BornTranslation.trans y u) n =
            Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * Φ κ u n) ∧
          (∀ k : ℤ, Φ κ (QuantumNLS.RootMassBoostSymbol.boost k u) n = Φ κ u (n - k)) ∧
          Φ κ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = Φ κ u (-n) ∧
          Φ κ (star u) n = conj (Φ κ u (-n)) ∧
          (∀ φ : ℝ, Φ κ (Complex.exp ((φ : ℂ) * Complex.I) • u) n =
            Complex.exp ((φ : ℂ) * Complex.I) * Φ κ u n) ∧
          Φ κ (Cphys L u) n = conj (Φ κ u n)) ∧
        -- (i) `Φ_κ` is the ordinary Fourier transform on every Fourier plane
        (∀ (k : ℤ) (c : ℂ), ‖c‖ < d / Real.sqrt κ →
          Φ κ (c • modeLp L k) = fourierL2 L (c • modeLp L k)) ∧
        -- (j) uniqueness among canonical exact-modulus charts on a common ball, by `DΦ(0) = 𝓕` and `Φ(conj u(−·)) = conj Φ(u)`
        (∀ r0 : ℝ, 0 < r0 → r0 ≤ d / Real.sqrt κ → ∀ Ψ' : L2T L → K,
          IsStronglySymplecticOn (ball (0 : L2T L) r0) (ball (0 : K) r0) Ψ' →
          AnalyticOnNhd ℝ Ψ' (ball (0 : L2T L) r0) →
          (∀ u ∈ ball (0 : L2T L) r0, ∀ n : ℤ, ‖Ψ' u n‖ ^ 2 = (masses hκ u).1 n) →
          (∀ h : L2T L, fderiv ℝ Ψ' 0 h = fourierL2 L h) →
          (∀ u ∈ ball (0 : L2T L) r0, Ψ' (Cphys L u) = star (Ψ' u)) →
          ∀ u ∈ ball (0 : L2T L) r0, Ψ' u = Φ κ u)) ∧
      -- (k) scaling `Φ_κ(su) = sΦ_{κs²}(u)`
      (∀ (κ : ℝ), 0 < κ → ∀ s : ℝ, 0 < s → ∀ u : L2T L, ‖u‖ < d / Real.sqrt (κ * s ^ 2) →
        Φ κ (s • u) = s • Φ (κ * s ^ 2) u) ∧
      -- (l) the full `C¹` Fourier limit as `κ ↓ 0` on every fixed bounded `L²` ball
      (∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ < κ0 →
        ∀ u : L2T L, ‖u‖ < ρ0 → ‖u‖ < d / Real.sqrt κ ∧
          ‖Φ κ u - Setting.Fcl L u‖ ≤ ε ∧ ‖fderiv ℝ (Φ κ) u - Setting.Fcl L‖ ≤ ε) := by
  exact QuantumNLS.Local023.reset_open_transform L

end QuantumNLS.L023Spec
#print axioms QuantumNLS.L023Spec.reset_open_transform_spec
