import QuantumNLS.HighContours

/-! integrator-authored trusted spec for R-93DEB242 `QG:cor:high-contours`
(core/QUANTUM_GAUGE_COMPONENTS.tex:226-243, ω = 2π/L, c = κ/N, energy bound N⁻¹Σq² ≤ E as in
QG:prop:high-root-localization). Fix L, κ, E > 0. There is a label threshold R ("after increasing R_E")
such that for every N, every on-shell configuration with N⁻¹ Σ q_j² ≤ E and every label m with |m| > R,
writing S_m = {z : |Re z − ωm| < ω/4, |Im z| < ω/4}, Γ_m = ∂S_m and U_m = {z : dist(z, Γ_m) < ω/32}
(the width-ω/32 neighbourhood):
(1) every root stays at distance ≥ d = ω/8 from every point of U_m;
(2) the roots inside Γ_m (in S_m) are exactly those with label m;
(3) for every integer s ≥ 1 and z ∈ U_m: N⁻¹ Σ_j |z − q_j|^{−s} ≤ (4/|ωm|)^s + 4E/(d^s |ωm|²);
(4) for s ≥ 2 these bounds are summable over |m| > M with tail O_{E,s}(1/M).
(The printed "positively oriented" plays no role in any stated clause.) -/

namespace QuantumNLS.R93DESpec

noncomputable def ω (L : ℝ) : ℝ := 2 * Real.pi / L

def S (L : ℝ) (m : ℤ) : Set ℂ := {z | |z.re - ω L * m| < ω L / 4 ∧ |z.im| < ω L / 4}

def U (L : ℝ) (m : ℤ) : Set ℂ := {z | ∃ w ∈ frontier (S L m), dist z w < ω L / 32}

noncomputable def bnd (L E : ℝ) (s : ℕ) (m : ℤ) : ℝ :=
  (4 / |ω L * m|) ^ s + 4 * E / ((ω L / 8) ^ s * |ω L * m| ^ 2)

def Spec : Prop :=
  (∀ (L κ E : ℝ), 0 < L → 0 < κ → 0 < E →
    ∃ R : ℝ, ∀ (N : ℕ) (n : Fin N → ℤ) (q : Fin N → ℝ),
      StrictMono q → Monotone n →
      (∀ j, L * q j = 2 * Real.pi * n j +
        2 * ∑ l ∈ Finset.univ.erase j, Real.arctan ((κ / N) / (q j - q l))) →
      (N : ℝ)⁻¹ * ∑ j, q j ^ 2 ≤ E →
      ∀ m : ℤ, R < |(m : ℝ)| →
        (∀ z ∈ U L m, ∀ j, ω L / 8 ≤ ‖z - q j‖) ∧
        (∀ j, ((q j : ℂ) ∈ S L m ↔ n j = m)) ∧
        (∀ s : ℕ, 1 ≤ s → ∀ z ∈ U L m,
          (N : ℝ)⁻¹ * ∑ j, (‖z - q j‖ ^ s)⁻¹ ≤ bnd L E s m)) ∧
  (∀ (L E : ℝ), 0 < L → 0 < E → ∀ s : ℕ, 2 ≤ s →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, 1 ≤ M →
      Summable (fun m : ℤ => if (M : ℝ) < |(m : ℝ)| then bnd L E s m else 0) ∧
      ∑' m : ℤ, (if (M : ℝ) < |(m : ℝ)| then bnd L E s m else 0) ≤ K / (M : ℝ))

theorem spec : Spec := by
  refine ⟨fun L κ E hL hκ hE => ?_, fun L E hL hE s hs => HighContours.moment_bound_summable hL hE hs⟩
  obtain ⟨R, -, h⟩ := HighContours.high_contours hL hκ E hE
  refine ⟨R, fun N n q hq hn hB hEn m hm => ?_⟩
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    refine ⟨fun _ _ j => j.elim0, fun j => j.elim0, fun s _ z _ => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
    have hω : 0 < ω L := by unfold ω; have := Real.pi_pos; positivity
    unfold bnd
    exact add_nonneg (pow_nonneg (div_nonneg (by norm_num) (abs_nonneg _)) _)
      (div_nonneg (by linarith) (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (abs_nonneg _) _)))
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
    exact h N n q ⟨div_pos hκ hN0, hq, hn, fun j => hB j⟩ hEn m hm

end QuantumNLS.R93DESpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R93DESpec.spec
  IO.println s!"R93DESpec.spec axioms: {ax}"
