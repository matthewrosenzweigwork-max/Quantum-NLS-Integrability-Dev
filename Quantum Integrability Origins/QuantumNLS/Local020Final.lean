import Mathlib
import QuantumNLS.Local007Statement
import QuantumNLS.Local020Fin1
import QuantumNLS.Local020Fin2
import QuantumNLS.Local020Mass
import QuantumNLS.ResetNormalizationBinding

/-! LOCAL-020 `prop:reset-spectral-covariance` (`local_covariance.tex:23`): the single named theorem
`reset_spectral_covariance`.

Printed statement.  The family `g_n = √L b_n/(2i√κ)` from the polar-normalized Riesz reduction has exactly the covariances
`g_n(τ_y u) = e^{ip_n y} g_n(u)`, `g_n(B_k u) = g_{n-k}(u)`, `g_n(R u) = g_{-n}(u)`, `g_n(C u) = conj g_{-n}(u)` and
`g_n(e^{iφ}u) = e^{iφ} g_n(u)`; the analytic exact-mass factors `r_n` have the corresponding index permutations and are unchanged
by translations and common phase; hence `ζ_n = g_n √r_n` has precisely the Fourier covariances, in particular
`ζ_n(CRu) = conj ζ_n(u)`; `ζ` agrees with the ordinary Fourier transform on every single Fourier plane; and
`ζ_κ(su) = s ζ_{κ s²}(u)` for `s > 0` on common domains.

Formalization.  `L > 0`, `κ > 0` and a contour radius `0 < r < 2π/L` are the hypotheses of the accepted LOCAL-003
(reduction) and LOCAL-007 (exact factor).  The family is the LOCAL-003/LOCAL-007 data `(a_n, b_n, rr)` on a ball `‖u‖ < ρ`:
`Pkg` is the printed LOCAL-003 conjunction (`B_n = [[a_n, conj b_n],[b_n, a_n]]` for the polar-normalized reduced matrix
`reducedMatrix2`, its eigenvalue/resolvent structure and the estimates on `g_n = gcoef · b_n`), `rr` is real analytic with
`I_n(u) = |g_n(u)|² rr_n(u)` (`I_n` the literal physical indexed masses of R-950BFB30) and `1/2 < rr_n < 3/2`.  The scaling clause
is quantified over every other LOCAL-007 family at the coupling `κ s²` (on the common domain), so that no relation between
the two families is assumed beyond their defining properties. -/

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

namespace QuantumNLS.Local020Final

variable {L κ r : ℝ} [Fact (0 < L)]

/-- `ζ_n(u) = g_n(u) √(r_n(u))` with `g_n = gcoef · b_n`. -/
def zeta (L κ : ℝ) [Fact (0 < L)] (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)) (u : L2T L) (n : ℤ) : ℂ :=
  gcoef L κ * b n u * ((Real.sqrt (rr u n) : ℝ) : ℂ)

open QuantumNLS.Local020Fin1 (Dat)

theorem reset_spectral_covariance (hκ : 0 < κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
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
  have hL : 0 < L := Fact.out
  obtain ⟨ρ0, hρ0, C, hC, a, b, rr, hpk, hrr, hmass, hbd, -⟩ :=
    QuantumNLS.Local007Statement.reset_exact_factor hκ hr hr2
  obtain ⟨ρN, hρN, hmc⟩ := QuantumNLS.Local020Mass.mass_covariance hκ hr hr2
  set Λ : ℝ := 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set ρ : ℝ := min (min ρ0 ρN) (min (1 / (C + 1)) (r / (2 * (Λ + 1)))) with hρdef
  have hρpos : 0 < ρ := lt_min (lt_min hρ0 hρN) (lt_min (by positivity) (by positivity))
  have hρ0le : ρ ≤ ρ0 := (min_le_left _ _).trans (min_le_left _ _)
  have hρNle : ρ ≤ ρN := (min_le_left _ _).trans (min_le_right _ _)
  have hρC : ρ ≤ 1 / (C + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hρr : ρ ≤ r / (2 * (Λ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : ball (0 : L2T L) ρ ⊆ ball (0 : L2T L) ρ0 := ball_subset_ball hρ0le
  have hsmall : C * ρ ^ 2 < 1 := by
    have h3 : ρ * (C + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hρC
    nlinarith [sq_nonneg ρ, mul_nonneg hρpos.le hC]
  have hΛρ : Λ * ρ < r := by
    have h3 : ρ * (2 * (Λ + 1)) ≤ r := by rwa [le_div_iff₀ (by positivity)] at hρr
    nlinarith
  have D : Dat L κ r ρ C hκ a b rr :=
    { pkg := fun n => (hpk n).mono hρ0le le_rfl
      hC0 := hC
      hρ := hρpos
      ana := hrr.mono hsub
      mass := fun u hu n => hmass u (hsub hu) n
      pos := fun u hu n => by have := (hbd u (hsub hu) n).1; linarith
      small := hsmall }
  have hRC : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
      (masses hκ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u)).1 n = (masses hκ u).1 (-n) ∧
      (masses hκ (star u)).1 n = (masses hκ u).1 (-n) := fun u hu n =>
    hmc D.pkg u (by rwa [min_eq_left hρNle]) n
  have hzcov : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
      (∀ y : ℝ, zeta L κ b rr (QuantumNLS.BornTranslation.trans y u) n =
        Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * zeta L κ b rr u n) ∧
      (∀ k : ℤ, zeta L κ b rr (QuantumNLS.RootMassBoostSymbol.boost k u) n = zeta L κ b rr u (n - k)) ∧
      zeta L κ b rr (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = zeta L κ b rr u (-n) ∧
      zeta L κ b rr (star u) n = conj (zeta L κ b rr u (-n)) ∧
      (∀ φ : ℝ, zeta L κ b rr (Complex.exp ((φ : ℂ) * Complex.I) • u) n =
        Complex.exp ((φ : ℂ) * Complex.I) * zeta L κ b rr u n) := by
    intro u hu n
    obtain ⟨g1, g2, g3, g4, g5⟩ := QuantumNLS.Local020Fin1.g_cov D hu n
    obtain ⟨r1, r2, r3, r4, r5⟩ := QuantumNLS.Local020Fin1.rr_covariance D hRC hu n
    refine ⟨fun y => ?_, fun k => ?_, ?_, ?_, fun φ => ?_⟩
    · unfold zeta; rw [g1 y, r1 y]; ring
    · unfold zeta; rw [g2 k, r2 k]
    · unfold zeta; rw [g3, r3]
    · unfold zeta; rw [g4, r4]; simp only [map_mul, Complex.conj_ofReal]
    · unfold zeta; rw [g5 φ, r5 φ]; ring
  refine ⟨ρ, hρpos, C, hC, a, b, rr, D.pkg, D.ana, D.mass, fun u hu n => hbd u (hsub hu) n,
    fun u hu n => QuantumNLS.Local020Fin1.g_cov D hu n,
    fun u hu n => QuantumNLS.Local020Fin1.rr_covariance D hRC hu n, hzcov, ?_, ?_, ?_⟩
  · intro u hu n
    have hRu : QuantumNLS.ResetNormalizationUniqueness.reflectR L u ∈ ball (0 : L2T L) ρ := by
      rw [mem_ball_zero_iff, LinearIsometry.norm_map]; exact mem_ball_zero_iff.1 hu
    have h1 := (hzcov _ hRu n).2.2.2.1
    have h2 := (hzcov u hu (-n)).2.2.1
    rw [neg_neg] at h2
    show zeta L κ b rr (star (QuantumNLS.ResetNormalizationUniqueness.reflectR L u)) n = _
    rw [h1, h2]
  · intro k c hc n
    exact QuantumNLS.Local020Fin2.plane_zeta D (by nlinarith [hΛρ]) k c hc n
  · intro s hs hκ₂ ρ₂ C₂ hρ₂ hC₂ a₂ b₂ rr₂ hP₂ hana₂ hmass₂ u hu₂ hsu n
    obtain ⟨e1, e2⟩ := QuantumNLS.Local020Fin2.scale_clause D hs hκ₂ hρ₂ hC₂ hP₂ hana₂ hmass₂ hu₂ hsu n
    refine ⟨e1, e2, ?_⟩
    unfold zeta
    rw [e1, e2]; ring

end QuantumNLS.Local020Final

#print axioms QuantumNLS.Local020Final.reset_spectral_covariance
