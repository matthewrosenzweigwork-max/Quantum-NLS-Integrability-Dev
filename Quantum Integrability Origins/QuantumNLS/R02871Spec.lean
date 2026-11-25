import QuantumNLS.DuhamelDualityLocal
/-! integrator-authored trusted spec for R-02871DC6 lem:root-L4-duality (ROOT_L2_extension.tex:20).
U(t) = e^{it∂²} (Fourier multiplier e^{-it(2πn/L)²}), T_L = L²/(2π), C_L = (2T_L/L)^{1/4}.
For J = (α,β] of length ≤ T_L: ‖U(·)f‖_{L⁴(J×𝕋_L)} ≤ C_L‖f‖₂ (with slices U(t)f).
For F ∈ L^{4/3}(J×𝕋_L), a ∈ J: V(t) = ∫_a^t U(t−s)F(s)ds defined by duality (⟨h,S F⟩ = ∫ conj(U(s)h) F),
V ∈ C(J;L²), sup‖V(t)‖ ≤ C_L‖F‖_{4/3}; agrees with the ordinary (Bochner, oriented) integral whenever the
latter is defined (integrable + slice-identified on the interval between a and t). -/
namespace R02871Spec
open QuantumNLS QuantumNLS.L4Strichartz QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality
  QuantumNLS.DuhamelDualityLocal QuantumNLS.LocalWellPosedness QuantumNLS.Fourier MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

theorem spec (L : ℝ) [Fact (0 < L)] :
    TL L = L ^ 2 / (2 * Real.pi) ∧ CL L = (2 * TL L / L) ^ (4⁻¹ : ℝ) ∧
    (∀ (f : HL L) (t : ℝ) (n : ℤ), fourierL2 L (evol f t) n =
      Complex.exp (-(Complex.I * ((t * (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ))) * fourierL2 L f n) ∧
    -- eq:root-L4-free
    (∀ (f : HL L) {α β : ℝ}, α ≤ β → β ≤ α + TL L →
      ∃ u : Lp ℂ 4 (μJ (L := L) α β), ‖u‖ ≤ (2 * TL L / L) ^ (4⁻¹ : ℝ) * ‖f‖ ∧
        ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)), (fun x => u (t, x)) =ᵐ[volume] (evol f t : AddCircle L → ℂ)) ∧
    -- eq:root-L4-dual
    (∀ {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (F : Lp ℂ (4 / 3) (μJ (L := L) α β)),
      (∀ a t, V hαβ hlen F a t = evol (Sop hαβ hlen F a t) t) ∧
      (∀ a t, α ≤ a → α ≤ t → ∀ h : HL L, ⟪h, Sop hαβ hlen F a t⟫_ℂ = ∫ p, conj (freeL4 α β h p) *
        ((Set.Ioc a t ×ˢ Set.univ).indicator F p - (Set.Ioc t a ×ˢ Set.univ).indicator F p) ∂(μJ α β)) ∧
      (∀ a, Continuous (V hαβ hlen F a)) ∧
      (∀ a t, ‖V hαβ hlen F a t‖ ≤ CL L * ‖F‖) ∧
      (∀ (Fc : ℝ → HL L) {a t : ℝ}, MeasureTheory.IntegrableOn Fc (Set.uIoc a t) →
        (∀ᵐ s ∂(volume.restrict (Set.uIoc a t)), (fun x => F (s, x)) =ᵐ[volume] (Fc s : AddCircle L → ℂ)) →
        a ∈ Set.Icc α β → t ∈ Set.Icc α β →
        V hαβ hlen F a t = ∫ s in a..t, evol (Fc s) (t - s))) := by
  refine ⟨rfl, rfl, fun f t n => fourierL2_evol f t n, ?_, ?_⟩
  · intro f α β hαβ hlen
    obtain ⟨u, -, -, hu, hs⟩ := L4_free f hαβ hlen
    exact ⟨u, hu, hs⟩
  · intro α β hαβ hlen F
    exact ⟨fun a t => rfl, fun a t ha ht h => inner_Sop hαβ hlen F ha ht h,
      fun a => continuous_V hαβ hlen F a, fun a t => norm_V_le hαβ hlen F a t,
      fun Fc a t hFc hsl ha ht => V_eq_integral_local hαβ hlen F Fc hFc hsl ha ht⟩

end R02871Spec
#print axioms R02871Spec.spec
