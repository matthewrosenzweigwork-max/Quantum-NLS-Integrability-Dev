import QuantumNLS.Extrapolation
/-!
Trusted statement for PROP-016 `Q7A:lem:extrap`, written by the integrator (not the prover) from
`source/chapters/propagation/window_reconstruction.tex:70–86`, under the section's standing model hypotheses (lines 18–31):
eq:ms at the nodes (`hvar`), classical moments (`hμint`), support distance δ from the cut centre (`hsupp`), roots a random
vector (`hq`). Spec definitions are written here from mathlib primitives. Uniformity is encoded by the quantifier order: the constants
C_m, C_{m,p} are chosen after m, p, η₀, δ, ρ, h, H, the eq:ms constant and μ, and BEFORE Ω, N, the roots, R and a.
The `+` cut is centre a; the `−` cut is the same statement at centre −a (|a| ≥ 2R covers both signs), as the source treats them separately.
-/
open MeasureTheory

namespace P16
noncomputable def G (μ : Measure ℝ) (z : ℂ) : ℂ := ∫ x, 1 / (z - (x : ℂ)) ∂μ
noncomputable def GN {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ := (1 / (N : ℂ)) * ∑ j, 1 / (z - (q j : ℂ))
noncomputable def node (a η0 : ℝ) (m : ℕ) (j : Fin (m + 1)) : ℂ :=
  (a : ℂ) + (((η0 + 1 + ((j : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I
def rect (a ρ h : ℝ) : Set ℂ := {z | |z.re - a| ≤ 2 * ρ ∧ |z.im| ≤ h + 2 * ρ}
noncomputable def maxErr (μ : Measure ℝ) {N : ℕ} (q : Fin N → ℝ) (a η0 : ℝ) (m : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun k : Fin (m + 1) => ‖G μ (node a η0 m k) - GN q (node a η0 m k)‖
end P16
open P16

def Prop016Spec : Prop :=
  ∀ (m p : ℕ) (η0 δ ρ h H Cvar : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ],
    0 < η0 → 0 < ρ → ρ < δ / 4 → η0 < h → h + 4 * ρ < H →
    Integrable (fun x : ℝ => x ^ (2 * p)) μ →
    ∃ Cm Cmp : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {N : ℕ} (_ : 0 < N) (q : Ω → Fin N → ℝ) (_ : Measurable q) (R a : ℝ),
      0 < R → 2 * H ≤ R → 2 * (η0 + 1 + m) ≤ R → 2 * R ≤ |a| →
      (∀ᵐ x ∂μ, δ ≤ |x - a|) →
      (∀ k : Fin (m + 1), ∫ ω, ‖G μ (node a η0 m k) - GN (q ω) (node a η0 m k)‖ ^ 2 ∂P
          ≤ Cvar / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2)) →
      -- (D) eq:extrap on the event max_j |q_j| ≤ R, pointwise on the rectangle (equivalently its sup)
      (∀ ω, (∀ j, |q ω j| ≤ R) → ∀ z ∈ rect a ρ h,
          ‖G μ z - GN (q ω) z‖ ≤ Cm * maxErr μ (q ω) a η0 m + Cm * (1 / R ^ (m + 2)) + Cmp * (1 / R ^ (2 * p))) ∧
      -- (P) probability that the RIGHT side exceeds C_m ε + C_m R^{-m-2} + C_{m,p} R^{-2p}, roots in [-R,R]
      (∀ ε : ℝ, 0 < ε → P.real {ω | (∀ j, |q ω j| ≤ R) ∧
          Cm * ε + Cm * (1 / R ^ (m + 2)) + Cmp * (1 / R ^ (2 * p))
            < Cm * maxErr μ (q ω) a η0 m + Cm * (1 / R ^ (m + 2)) + Cmp * (1 / R ^ (2 * p))}
          ≤ Cm / ((N : ℝ) * ε ^ 2))

theorem prop016_spec : Prop016Spec := by
  intro m p η0 δ ρ h H Cvar μ _ hη0 hρ hρδ hηh hH hμint
  refine ⟨QuantumNLS.Extrapolation.srcCm η0 H Cvar m, QuantumNLS.Extrapolation.srcCmp η0 H δ ρ m μ p, ?_⟩
  intro Ω _ P _ N hN q hq R a hR hRH hRH1 hcut hsupp hvar
  have hf := QuantumNLS.Extrapolation.prop016_final_rhs P hN q hq μ m η0 δ ρ h H R a p hη0 hρ hρδ hηh hH hR
    hRH hRH1 hcut hμint hsupp Cvar hvar
  refine ⟨?_, hf.2⟩
  intro ω hω z hz
  have hle : ∀ k : Fin (m + 1), ‖G μ (node a η0 m k) - GN (q ω) (node a η0 m k)‖ ≤ maxErr μ (q ω) a η0 m :=
    fun k => Finset.le_sup' (fun k : Fin (m + 1) => ‖G μ (node a η0 m k) - GN (q ω) (node a η0 m k)‖)
      (Finset.mem_univ k)
  have h0 : 0 ≤ maxErr μ (q ω) a η0 m := le_trans (norm_nonneg _) (hle 0)
  exact hf.1 ω hω _ h0 hle z hz

#print axioms prop016_spec
