import Mathlib
import QuantumNLS.Prop025OParams

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O2:
the final step "eq:MP-total-error ⇒ eq:MP-main" (mixed_propagation.tex:664-710).

`main_of_total`: there is one constant `C` (depending only on `d`, the cut slack `c = 2π/L`,
the packet constants `C_p, D_p, C_b` and the comparison constant `C_k`) such that, for every
`N ≥ 1`, every cut `2R ≤ a ≤ 2R + c`, and all reals, the printed total error bound
`lhs ≤ 2e_N + C_k[√(η^I_N + η^g_N) + ρ^I_N + W_a/N + W_aΔ_N + N^{-1/4}W_a^7 + a^{-1/4}]`
implies the printed main bound `lhs ≤ 2e_N + C ζ_{I,N} + C N^{-1/[224(d+1)]}` with
`ζ_{I,N} = √η^I_N + ρ^I_N`.  `zeta_tendsto`: `ζ_{I,N} → 0` when `η^I_N, ρ^I_N → 0`;
`zeta_empty`: `ζ = 0` for empty `I` (`η^I = ρ^I = 0`). -/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace QuantumNLS.Prop025OFinal
open Prop025OParams

/-- The printed growing-window discarded mass, eq:MP-growing-mass with eq:MP-parameters. -/
def etaG (d : ℕ) (Cp Dp Cb N a : ℝ) : ℝ :=
  Cp * N * ((N ^ alpha d) ^ (2 * (28 * (d+1) + 1)))⁻¹ + Dp * (N ^ alpha d)⁻¹ +
    Cb * (1 + a) / (N * (N ^ (-(1/8 : ℝ))) ^ 3)

/-- `W_a = (1+a)^{d+1}`. -/
def W (d : ℕ) (a : ℝ) : ℝ := (1 + a) ^ (d+1)

/-- `Δ_N = ε + R^{-b} + N^{-1}` with `ε = N^{-1/8}`, `R = N^α`, `b = d+2`. -/
def Delta (d : ℕ) (N : ℝ) : ℝ := N ^ (-(1/8 : ℝ)) + ((N ^ alpha d) ^ (d+2))⁻¹ + N⁻¹

/-- The bracket of eq:MP-total-error. -/
def totalBracket (d : ℕ) (Cp Dp Cb N a ηI ρI : ℝ) : ℝ :=
  Real.sqrt (ηI + etaG d Cp Dp Cb N a) + ρI + W d a / N + W d a * Delta d N +
    N ^ (-(1/4 : ℝ)) * W d a ^ 7 + a ^ (-(1/4 : ℝ))

/-- `ζ_{I,N} = √η^I_N + ρ^I_N`. -/
def zeta (ηI ρI : ℝ) : ℝ := Real.sqrt ηI + ρI

/-- **eq:MP-total-error ⇒ eq:MP-main.** -/
theorem main_of_total (d : ℕ) (hd : 2 ≤ d) (c Cp Dp Cb Ck : ℝ) (hc : 0 ≤ c) (hCp : 0 ≤ Cp)
    (hDp : 0 ≤ Dp) (hCb : 0 ≤ Cb) (hCk : 0 ≤ Ck) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N → ∀ a : ℝ, 2 * N ^ alpha d ≤ a →
      a ≤ 2 * N ^ alpha d + c → ∀ lhs e ηI ρI : ℝ, 0 ≤ ηI → 0 ≤ ρI →
      lhs ≤ 2 * e + Ck * totalBracket d Cp Dp Cb N a ηI ρI →
      lhs ≤ 2 * e + C * zeta ηI ρI + C * N ^ (-(1 / (224 * ((d : ℝ) + 1)))) := by
  obtain ⟨C0, hC0, hrate⟩ := total_rate d hd c Cp Dp Cb hc hCp hDp hCb
  refine ⟨Ck * (1 + C0), by positivity, ?_⟩
  intro N hN a ha1 ha2 lhs e ηI ρI hηI hρI hlhs
  have hN0 : 0 < N := by linarith
  have ha0 : 0 ≤ a := by
    have := (Real.rpow_pos_of_pos hN0 (alpha d)).le
    linarith
  have hG0 : 0 ≤ etaG d Cp Dp Cb N a := by unfold etaG; positivity
  have hsq : Real.sqrt (ηI + etaG d Cp Dp Cb N a) ≤
      Real.sqrt ηI + Real.sqrt (etaG d Cp Dp Cb N a) := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hηI, Real.sq_sqrt hG0, Real.sqrt_nonneg ηI,
      Real.sqrt_nonneg (etaG d Cp Dp Cb N a)]
  have hr := hrate N hN a ha1 ha2
  have hq : 0 ≤ N ^ (-(alpha d / 4)) := (Real.rpow_pos_of_pos hN0 _).le
  have hB : totalBracket d Cp Dp Cb N a ηI ρI ≤
      zeta ηI ρI + C0 * N ^ (-(alpha d / 4)) := by
    unfold totalBracket zeta etaG W Delta
    unfold etaG at hsq
    linarith
  have hexp : N ^ (-(alpha d / 4)) = N ^ (-(1 / (224 * ((d : ℝ) + 1)))) := by
    rw [alpha_four]
  have hz : 0 ≤ zeta ηI ρI := by unfold zeta; positivity
  calc lhs ≤ 2 * e + Ck * totalBracket d Cp Dp Cb N a ηI ρI := hlhs
    _ ≤ 2 * e + Ck * (zeta ηI ρI + C0 * N ^ (-(alpha d / 4))) := by gcongr
    _ ≤ 2 * e + Ck * (1 + C0) * zeta ηI ρI +
          Ck * (1 + C0) * N ^ (-(1 / (224 * ((d : ℝ) + 1)))) := by
        rw [← hexp]
        nlinarith [mul_nonneg hCk hz, mul_nonneg hCk hq, mul_nonneg (mul_nonneg hCk hC0) hz,
          mul_nonneg hCk (mul_nonneg hC0 hq)]

/-- `ζ_{I,N} → 0` from eq:MP-fixed-mass and eq:MP-fixed-deviation. -/
theorem zeta_tendsto (ηI ρI : ℕ → ℝ) (hη : Tendsto ηI atTop (𝓝 0)) (hρ : Tendsto ρI atTop (𝓝 0)) :
    Tendsto (fun N => zeta (ηI N) (ρI N)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => Real.sqrt (ηI N)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hη
    rw [Real.sqrt_zero] at h
    exact h
  simpa [zeta] using h1.add hρ

/-- For empty `I` the printed choice `η^I = ρ^I = 0` gives `ζ = 0`. -/
theorem zeta_empty : zeta 0 0 = 0 := by simp [zeta]

end QuantumNLS.Prop025OFinal

#print axioms QuantumNLS.Prop025OFinal.main_of_total
#print axioms QuantumNLS.Prop025OFinal.zeta_tendsto
