import QuantumNLS.RootDisplacement

/-! integrator-authored trusted spec for R-CED0D2FC `adj:lem:total-displacement`
(quantitative/response_auxiliaries.tex:9), in DEF-006's increasing corrected-label convention (Terra
R62: ACCEPT under that convention). Replace one occurrence of a by b in a sorted corrected-label tuple
n (giving sorted n'). Q(s) is ANY family solving the corrected logarithmic Bethe equations
L Q_i + 2 Σ_{j≠i} arctan((Q_i − Q_j)/c) = 2π(n_i + s(n'_i − n_i) + i − (N−1)/2) (fractional labels).
Then on [0,1]: Q̇_j ≥ 0 (a < b), resp. ≤ 0 (b < a); Σ_j Q̇_j = ω(b − a); and Σ_j |Q_j(1) − Q_j(0)| =
ω|b − a|, with ω = 2π/L. -/

open Finset

namespace QuantumNLS.RCED0Spec

def Interp (L c : ℝ) {N : ℕ} (n n' : Fin N → ℤ) (Q : ℝ → Fin N → ℝ) : Prop :=
  ∀ s i, L * Q s i + 2 * ∑ j ∈ univ.erase i, Real.arctan ((Q s i - Q s j) / c) =
    2 * Real.pi * ((n i : ℝ) + s * ((n' i : ℝ) - n i) + (i.val : ℝ) - ((N : ℝ) - 1) / 2)

def Spec : Prop :=
  ∀ (N : ℕ) (L c : ℝ), 0 < L → 0 < c → ∀ (n n' : Fin N → ℤ), Monotone n → Monotone n' →
    ∀ (a b : ℤ) (k : Fin N), n k = a →
    (∃ σ : Equiv.Perm (Fin N), ∀ i, n' (σ i) = Function.update n k b i) →
    ∀ Q : ℝ → Fin N → ℝ, Interp L c n n' Q →
      (a < b → (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j, 0 ≤ deriv Q s j)) ∧
      (b < a → (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j, deriv Q s j ≤ 0)) ∧
      (a ≠ b → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∑ j, deriv Q s j = 2 * Real.pi / L * ((b : ℝ) - a)) ∧
      (a ≠ b → ∑ j, |Q 1 j - Q 0 j| = 2 * Real.pi / L * |(b : ℝ) - a|)

theorem spec : Spec := by
  intro N L c hL hc n n' hn hn' a b k hk hrep Q hQ
  open QuantumNLS.RootDisplacement in
  have hQe : Q = fracRoots L c (realLabels n) (labelIncrement n n') := by
    funext s
    apply QuantumNLS.BetheSmooth.eq_root hL hc
    funext i
    rw [QuantumNLS.BetheAdmission.logMap_erase, hQ s i]
    simp only [forcingPath, logLabel, labelAt, realLabels, labelIncrement]
  have h0 : Q 0 = QuantumNLS.BetheSmooth.roots L n c := by
    rw [hQe]; exact QuantumNLS.RootDisplacement.fracRoots_zero L c n _
  have h1 : Q 1 = QuantumNLS.BetheSmooth.roots L n' c := by
    rw [hQe]; exact QuantumNLS.RootDisplacement.fracRoots_one L c n n'
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨-, -, -, hd, hs, hsum⟩ :=
      QuantumNLS.RootDisplacement.total_displacement_increase hL hc hn hn' hab hk hrep
    refine ⟨fun _ => hQe ▸ hd, fun h => absurd h (not_lt.2 hab.le), fun _ => hQe ▸ hs, fun _ => ?_⟩
    rw [h0, h1, hsum, abs_of_nonneg (by exact_mod_cast (sub_nonneg.2 hab.le))]
  · subst hab
    exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _),
      fun h => absurd rfl h, fun h => absurd rfl h⟩
  · obtain ⟨-, -, -, hd, hs, hsum⟩ :=
      QuantumNLS.RootDisplacement.total_displacement_decrease hL hc hn hn' hab hk hrep
    exact ⟨fun h => absurd h (not_lt.2 hab.le), fun _ => hQe ▸ hd, fun _ => hQe ▸ hs,
      fun _ => by rw [h0, h1, hsum]⟩

end QuantumNLS.RCED0Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.RCED0Spec.spec
  IO.println s!"RCED0Spec.spec axioms: {ax}"
