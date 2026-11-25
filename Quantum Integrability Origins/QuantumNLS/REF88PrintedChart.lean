import Mathlib
import QuantumNLS.GlobalCompatFinalR47a
import QuantumNLS.REF88Chart

/-!
# REF88PrintedChart: the printed chart hypotheses of R-EF8C2837 and the continuity of `Φ` and `Φ⁻¹`

Source: `source-text/chapters/global/physical_cubic.tex:28-36`:
"Fix `L,κ>0`.  Assume that `Φ_κ : L²(𝕋_L;ℂ) → ℓ²(ℤ;ℂ)` is a global real-analytic strong symplectic
diffeomorphism and `|Φ_κ(u)_n|² = I_n^{(κ)}(u)`.  Assume it has the local normalization of Theorem
`thm:reset-open-transform`."

`PrintedChart hκ Φ` records exactly those hypotheses.  "The local normalization of Theorem
`thm:reset-open-transform`" is formalized as its printed normalization: the Fourier derivative at zero
and the conjugation-reflection identity (`reset-open-transform`: "uniquely determined among canonical
exact-modulus charts on a common ball by its Fourier derivative and the conjugation-reflection identity
`Φ_κ(\\overline{u(-·)}) = \\overline{Φ_κ(u)}`").  By the uniqueness clause of the accepted R-CA92819A
(`GlobalCompatR47a.global_compatibility`, used read-only), any such `Φ` is the canonical global chart
`Φ_κ`; hence `Φ` and `Φ⁻¹` are continuous (`printedChart_continuity`) and the full-field scaling
`Φ_κ(su) = sΦ_{κs²}(u)` holds for the canonical family (`printedChart_canonical`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.REF88PrintedChart

open QuantumNLS.StrongSymplectic QuantumNLS.REF88Chart
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.GlobalCompatR47a QuantumNLS.RootIndexedMasses
open QuantumNLS.ResetNormalizationUniqueness (Cphys)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The printed hypotheses of `thm:global-physical-dynamics` on the chart. -/
structure PrintedChart (hκ : 0 < κ) (Φ : L2T L → K) : Prop where
  symp : IsStronglySymplectic Φ
  analytic : ∀ u, AnalyticAt ℝ Φ u
  moduli : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (masses hκ u).1 n
  fourier : ∀ v, fderiv ℝ Φ 0 v = QuantumNLS.Fourier.fourierL2 L v
  conj : ∀ u, Φ (Cphys L u) = star (Φ u)

/-- Any chart with the printed hypotheses is the canonical global chart of R-CA92819A; consequently it
and its inverse are continuous, and the canonical family obeys the full-field scaling identity. -/
theorem printedChart_canonical (hκ : 0 < κ) {Φ : L2T L → K} (hΦ : PrintedChart hκ Φ) :
    ∃ (Φc : ℝ → L2T L → K) (Ψc : ℝ → K → L2T L), Φ = Φc κ ∧
      Continuous (Φc κ) ∧ Continuous (Ψc κ) ∧ (∀ u, Ψc κ (Φc κ u) = u) ∧ (∀ z, Φc κ (Ψc κ z) = z) ∧
      (∀ κ' : ℝ, 0 < κ' → ∀ s : ℝ, 0 < s → ∀ u : L2T L, Φc κ' (s • u) = s • Φc (κ' * s ^ 2) u) := by
  obtain ⟨d, CL, hd, hCL, Φl, Ψl, hl, ⟨Φc, Ψc, hf⟩, hall⟩ := global_compatibility L
  obtain ⟨hκC, hscale, -⟩ := hall Φc Ψc hf
  obtain ⟨-, -, -, -, -, -, -, huniq, -, -, hcont, hcontΨ, hleft, hright⟩ := hκC κ hκ
  have hG : Φ = Φc κ := huniq Φ hΦ.symp hΦ.analytic hΦ.moduli hΦ.fourier hΦ.conj
  exact ⟨Φc, Ψc, hG, hcont, hcontΨ, hleft, hright, fun κ' hκ' s hs u => hscale κ' hκ' s hs u⟩

theorem printedChart_continuity (hκ : 0 < κ) {Φ : L2T L → K} (hΦ : PrintedChart hκ Φ) :
    Continuous Φ ∧ Continuous (chartInv hΦ.symp) := by
  obtain ⟨Φc, Ψc, hG, hcont, hcontΨ, hleft, hright, -⟩ := printedChart_canonical hκ hΦ
  refine ⟨hG ▸ hcont, ?_⟩
  have hinv : chartInv hΦ.symp = Ψc κ := by
    funext z
    have h1 : Φ (chartInv hΦ.symp z) = z := chartInv_right hΦ.symp z
    have h2 : Φ (Ψc κ z) = z := by rw [hG]; exact hright z
    have h3 := chartInv_left hΦ.symp (chartInv hΦ.symp z)
    rw [h1] at h3
    have h4 := chartInv_left hΦ.symp (Ψc κ z)
    rw [h2] at h4
    rw [← h3, h4]
  rw [hinv]; exact hcontΨ

#print axioms printedChart_canonical
#print axioms printedChart_continuity

end QuantumNLS.REF88PrintedChart
