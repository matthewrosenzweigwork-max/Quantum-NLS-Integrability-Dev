import QuantumNLS.CorrelationTaylor

/-! integrator-authored trusted spec for REG-006 `CC:G04:correlation`
(regularity/integer_moments.tex:159-173). Fix L > 0, integers k ≥ 1 and q ≥ 2 (q = m + 2). For
f_1, …, f_q ∈ H^k (the realized DEF-002 space `H02 L k`, via the alias `Hk`) put
C(h) = ∫_{𝕋_L} ∏_j f_j(x + h_j) dx, h ∈ ℝ^q. Then:
(1) C ∈ C^{2k}(ℝ^q);
(2) every partial derivative of total order ≤ 2k is bounded, uniformly in h, by C_{k,q,L} ∏_j ‖f_j‖_{H^k}
    (partials = iterated Fréchet derivative applied to coordinate basis vectors; the constant is chosen
    before f);
(3) its Taylor polynomial at zero of any degree 0 ≤ d ≤ 2k, P_d(h) = Σ_{j≤d} (1/j!) D^jC(0)(h,…,h)
    (P_0 = C(0)), has remainder o(|h|^d) as h → 0 (|h| Euclidean, |h|^0 = 1), and the remainder is bounded
    for all h by C_{k,q,L,d} |h|^d ∏_j ‖f_j‖_{H^k}.
(The continuous extension of differential monomials at l.196-199 is proof commentary; Terra r87.) -/

open Filter Topology MeasureTheory
open QuantumNLS.TranslatedCorrelation

namespace QuantumNLS.REG006Spec

variable {L : ℝ} [Fact (0 < L)]

noncomputable def sC {q k : ℕ} (f : Fin q → Hk L k) (h : Fin q → ℝ) : ℂ :=
  ∫ x, ∏ j, (f j).val (x + ((h j : ℝ) : AddCircle L)) ∂(volume : Measure (AddCircle L))

noncomputable def sE {q : ℕ} (h : Fin q → ℝ) : ℝ := Real.sqrt (∑ j, h j ^ 2)

noncomputable def sP {q : ℕ} (C : (Fin q → ℝ) → ℂ) (d : ℕ) (h : Fin q → ℝ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1), ((Nat.factorial j : ℝ)⁻¹) • iteratedFDeriv ℝ j C 0 (fun _ : Fin j => h)

def Spec (L : ℝ) [Fact (0 < L)] : Prop :=
  ∀ (m k : ℕ), 1 ≤ k →
    (∀ f : Fin (m + 2) → Hk L k, ContDiff ℝ ((2 * k : ℕ) : WithTop ℕ∞) (sC f)) ∧
    (∃ K : ℝ, ∀ (f : Fin (m + 2) → Hk L k) (d : ℕ), d ≤ 2 * k → ∀ (js : Fin d → Fin (m + 2)) h,
      ‖iteratedFDeriv ℝ d (sC f) h (fun i => Pi.single (js i) (1 : ℝ))‖ ≤ K * ∏ j, ‖f j‖) ∧
    (∀ f : Fin (m + 2) → Hk L k, Tendsto (fun h => sC f h - sC f 0) (𝓝 0) (𝓝 0)) ∧
    (∃ K : ℝ, ∀ (f : Fin (m + 2) → Hk L k) h, ‖sC f h - sC f 0‖ ≤ K * ∏ j, ‖f j‖) ∧
    (∀ d : ℕ, 1 ≤ d → d ≤ 2 * k →
      (∀ f : Fin (m + 2) → Hk L k,
        (fun h => sC f h - sP (sC f) d h) =o[𝓝 0] (fun h => sE h ^ d)) ∧
      (∃ K : ℝ, ∀ (f : Fin (m + 2) → Hk L k) h,
        ‖sC f h - sP (sC f) d h‖ ≤ K * sE h ^ d * ∏ j, ‖f j‖))

theorem spec : Spec L := by
  intro m k hk
  have hq : 2 ≤ m + 2 := by omega
  set K0 : ℝ := (max 1 (2 * Real.pi / L)) ^ (2 * k) * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) *
      (((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) *
        (QuantumNLS.CorrelationConstrainedSumGen.Ckc k) ^ (m + 2)) *
      ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ ^ (m + 2) with hK0
  refine ⟨fun f => CorrelationDerivatives.contDiff_Cfun hk f, ⟨K0, fun f d hd js h => ?_⟩,
    fun f => (correlation_checkpoint hq hk f).2.2.2.1,
    ⟨2 * L * QuantumNLS.Fourier.cL L ^ (m + 2), fun f h => (correlation_checkpoint hq hk f).2.2.2.2 h⟩,
    fun d hd1 hd2 => ?_⟩
  · exact CorrelationDerivatives.partial_derivative_bound hk f hd js h
  · obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    refine ⟨fun f => CorrelationTaylor.taylor_remainder_isLittleO hk f hd2,
      ⟨2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * K0), fun f h => ?_⟩⟩
    have := CorrelationTaylor.taylor_remainder_bound hk f hd2 h
    calc ‖sC f h - sP (sC f) (n + 1) h‖ ≤ 2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) *
          CorrelationTaylor.Bfull f) * CorrelationTaylor.eucl h ^ (n + 1) := this
      _ = 2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * K0) * sE h ^ (n + 1) * ∏ j, ‖f j‖ := by
          simp only [CorrelationTaylor.Bfull, hK0, CorrelationTaylor.eucl, sE]; ring

end QuantumNLS.REG006Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.REG006Spec.spec
  IO.println s!"REG006Spec.spec axioms: {ax}"
