import QuantumNLS.IndividualRootBound

/-! integrator-authored trusted spec for REG-002 `CC:individual-root-bound`
(regularity/root_confinement.tex:59-80). Written independently of OnShellSpacing:
(A) N ≥ 1, L, c > 0, q strictly increasing, p nondecreasing, L(q_j − p_j) = 2 Σ_{k≠j} arctan(c/(q_j − q_k))
    (principal arctan) ⇒ max_j |q_j − p_j| ≤ 2√(c(N−1)/L)   (stated ∀ j; equivalent for N ≥ 1).
(B) CC:mean-field-root-bound: for an ordered repulsive Bethe configuration with nondecreasing bosonic
    integer labels n_j and c = κ/N, i.e. q strictly increasing with
    L(q_j − 2πn_j/L) = 2 Σ_{k≠j} arctan((κ/N)/(q_j − q_k)), one has |q_j − 2πn_j/L| ≤ 2√((κ/L)(1 − 1/N)).
(C) the same bound for the accepted R-4C8D7C9E roots `BetheSmooth.roots L n (κ/N)` with n monotone. -/

namespace QuantumNLS.REG002Spec

def Spec : Prop :=
  (∀ (N : ℕ), 1 ≤ N → ∀ (L c : ℝ), 0 < L → 0 < c → ∀ (q p : Fin N → ℝ), StrictMono q → Monotone p →
    (∀ j, L * (q j - p j) = 2 * ∑ k ∈ Finset.univ.erase j, Real.arctan (c / (q j - q k))) →
    ∀ j, |q j - p j| ≤ 2 * Real.sqrt (c * ((N : ℝ) - 1) / L)) ∧
  (∀ (N : ℕ), 1 ≤ N → ∀ (L κ : ℝ), 0 < L → 0 < κ → ∀ (n : Fin N → ℤ) (q : Fin N → ℝ),
    StrictMono q → Monotone n →
    (∀ j, L * (q j - 2 * Real.pi * (n j : ℝ) / L) =
      2 * ∑ k ∈ Finset.univ.erase j, Real.arctan ((κ / N) / (q j - q k))) →
    ∀ j, |q j - 2 * Real.pi * (n j : ℝ) / L| ≤ 2 * Real.sqrt ((κ / L) * (1 - 1 / (N : ℝ)))) ∧
  (∀ (N : ℕ), 1 ≤ N → ∀ (L κ : ℝ), 0 < L → 0 < κ → ∀ (n : Fin N → ℤ), Monotone n →
    ∀ j, |QuantumNLS.BetheSmooth.roots L n (κ / (N : ℝ)) j - 2 * Real.pi * (n j : ℝ) / L| ≤
      2 * Real.sqrt ((κ / L) * (1 - 1 / (N : ℝ))))

theorem spec : Spec := by
  refine ⟨fun N hN L c hL hc q p hq hp hE j =>
      QuantumNLS.IndividualRootBound.individual_root_bound hN hL hc q p hq hp hE j, ?_,
    fun N hN L κ hL hκ n hn j => QuantumNLS.IndividualRootBound.mean_field_root_bound_roots hN hL hκ n hn j⟩
  intro N hN L κ hL hκ n q hq hn hE j
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : L ≠ 0 := hL.ne'
  have hc : 0 < κ / N := div_pos hκ hN0
  have h := QuantumNLS.IndividualRootBound.individual_root_bound hN hL hc q
    (fun i => 2 * Real.pi * (n i : ℝ) / L) hq
    (fun a b hab => by
      have := hn hab
      have h' : (n a : ℝ) ≤ n b := by exact_mod_cast this
      have hpi : 0 ≤ 2 * Real.pi / L := div_nonneg (by positivity) hL.le
      have := mul_le_mul_of_nonneg_left h' hpi
      simp only
      calc 2 * Real.pi * (n a : ℝ) / L = 2 * Real.pi / L * n a := by ring
        _ ≤ 2 * Real.pi / L * n b := this
        _ = 2 * Real.pi * (n b : ℝ) / L := by ring) hE j
  have e : κ / N * ((N : ℝ) - 1) / L = κ / L * (1 - 1 / (N : ℝ)) := by
    field_simp
  rw [e] at h
  exact h

end QuantumNLS.REG002Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.REG002Spec.spec
  IO.println s!"REG002Spec.spec axioms: {ax}"
