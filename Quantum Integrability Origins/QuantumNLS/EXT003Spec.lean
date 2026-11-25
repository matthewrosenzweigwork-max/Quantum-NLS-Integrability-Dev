import QuantumNLS.LocalL4Contraction
/-! integrator-authored trusted spec for EXT-003 (ROOT_L2_extension.tex:1–19, the quoted Bourgain local L⁴ input),
proved internally by the integrator-authorized Route Y (elementary L⁴/Christ–Kiselev; documented deviation from
Bourgain X^{0,b}). For each R ≥ 0: τ_R > 0, B_R, A_R such that on every J = (α,β] with 0 < β−α ≤ τ_R and any data time a,
the cubic Duhamel equation u(t) = U(t−a)f − 2iκ ∫_a^t U(t−s)(|u|²u)(s) ds (a.e. slices; integral = DD1 duality
Duhamel map, which agrees with the ordinary integral when defined, R-02871DC6) has for ‖f‖₂ ≤ R a solution in
L⁴(J×𝕋_L) with ‖u‖₄ ≤ B_R, unique among such; A_R-Lipschitz from the L² ball into L⁴; plus the C_tL² stability
and size bounds. Any L > 0, any real κ (coefficient 2κ). -/
namespace EXT003Spec
open QuantumNLS QuantumNLS.LocalL4Contraction QuantumNLS.DuhamelDuality QuantumNLS.L4StrichartzL2
  QuantumNLS.L4Strichartz MeasureTheory

theorem spec (L : ℝ) [Fact (0 < L)] :
    -- the equation, literally
    (∀ (κ : ℝ), cNLS κ = -(2 * (κ : ℂ) * Complex.I)) ∧
    (∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (c : ℂ) (a : ℝ) (f : HL L)
      (u : Lp ℂ 4 (μJ (L := L) α β)),
      IsDuhamel hαβ hlen c a f u ↔ ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
        (fun x => u (t, x)) =ᵐ[volume] (evol f (t - a) + c • V hαβ hlen (cub u) a t : HL L)) ∧
    (∀ (α β : ℝ) (u : Lp ℂ 4 (μJ (L := L) α β)),
      (cub u : ℝ × AddCircle L → ℂ) =ᵐ[μJ α β] fun p => ((‖u p‖ ^ 2 : ℝ) : ℂ) * u p) ∧
    -- EXT-003 as quoted
    (∀ (κ R : ℝ), 0 ≤ R →
    ∃ τ B A : ℝ, 0 < τ ∧ τ ≤ 1 ∧ τ ≤ TL L ∧ 0 ≤ B ∧ 0 ≤ A ∧
      ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L), α < β → β ≤ α + τ → ∀ a : ℝ,
        (∀ f : HL L, ‖f‖ ≤ R →
          ∃ u : Lp ℂ 4 (μJ (L := L) α β), ‖u‖ ≤ B ∧ IsDuhamel hαβ hlen (cNLS κ) a f u) ∧
        (∀ (f : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖u‖ ≤ B → ‖v‖ ≤ B →
          IsDuhamel hαβ hlen (cNLS κ) a f u → IsDuhamel hαβ hlen (cNLS κ) a f v → u = v) ∧
        (∀ (f g : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖g‖ ≤ R → ‖u‖ ≤ B →
          ‖v‖ ≤ B → IsDuhamel hαβ hlen (cNLS κ) a f u → IsDuhamel hαβ hlen (cNLS κ) a g v →
            ‖u - v‖ ≤ A * ‖f - g‖) ∧
        (∀ (f g : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖g‖ ≤ R → ‖u‖ ≤ B →
          ‖v‖ ≤ B → IsDuhamel hαβ hlen (cNLS κ) a f u → IsDuhamel hαβ hlen (cNLS κ) a g v →
            ∀ t : ℝ, ‖Dcurve hαβ hlen (cNLS κ) a f u t - Dcurve hαβ hlen (cNLS κ) a g v t‖ ≤
              (1 + 6 * |κ| * CL L * B ^ 2 * A) * ‖f - g‖) ∧
        (∀ (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖u‖ ≤ B → ∀ t : ℝ,
          ‖Dcurve hαβ hlen (cNLS κ) a f u t‖ ≤ R + 2 * |κ| * CL L * B ^ 3) ) := by
  refine ⟨fun κ => rfl, fun α β hαβ hlen c a f u => Iff.rfl, fun α β u => coeFn_cub u,
    fun κ R hR => ext003_local_input κ R hR⟩

end EXT003Spec
#print axioms EXT003Spec.spec
