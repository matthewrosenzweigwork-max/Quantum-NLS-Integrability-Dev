import QuantumNLS.BetheZeroLimitLiteral

/-! integrator-authored trusted spec for R-CD2257D0 `basis:lem:zero` (periodic_basis.tex:164-170).
Vocabulary as in the frozen R-4C8D7C9E spec: n ∈ 𝔑_N (antitone integers), I_j = n_j + ρ_j with
ρ_j = (N+1−2j)/2, and the printed (logbethe) system. q(n,c) is ANY family solving the printed system
for every c > 0 (unique by R-4C8D7C9E). Claim: as c ↓ 0, q(n,c) → (2π/L) n, and for j < k
(q_j − q_k)/c → +∞ (also when n_j = n_k). Zero-based indices. -/

open Filter Topology

namespace QuantumNLS.RCD22Spec

noncomputable def specI {N : ℕ} (n : Fin N → ℤ) (j : Fin N) : ℝ :=
  (n j : ℝ) + ((N : ℝ) + 1 - 2 * ((j : ℕ) + 1 : ℝ)) / 2

def specBethe {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (q : Fin N → ℝ) : Prop :=
  ∀ j : Fin N, L * q j + 2 * ∑ k ∈ Finset.univ.erase j, Real.arctan ((q j - q k) / c) =
    2 * Real.pi * specI n j

def Spec : Prop :=
  ∀ (N : ℕ) (L : ℝ), 0 < L → ∀ n : Fin N → ℤ, Antitone n →
    ∀ Q : ℝ → (Fin N → ℝ), (∀ c : ℝ, 0 < c → specBethe L c n (Q c)) →
      Tendsto Q (𝓝[>] 0) (𝓝 (fun j => 2 * Real.pi / L * (n j : ℝ))) ∧
      ∀ j k : Fin N, j < k → Tendsto (fun c => (Q c j - Q c k) / c) (𝓝[>] 0) atTop

theorem spec : Spec := by
  intro N L hL n hn Q hQ
  have hi : ∀ j : Fin N, specI n j = (n j : ℝ) + ((N : ℝ) - 1) / 2 - (j.val : ℝ) := by
    intro j; unfold specI; push_cast; ring
  have heq : ∀ c : ℝ, 0 < c → Q c = BetheSmooth.sourceRoots L n c := by
    intro c hc
    obtain ⟨-, hall⟩ := QuantumNLS.BetheConvexity.source_roots_spec hL hn
    obtain ⟨-, -, -, hu⟩ := hall c hc
    apply hu
    funext i
    have h := hQ c hc i
    rw [hi] at h
    simpa only [QuantumNLS.BetheAdmission.logMap_erase, BetheSmooth.sourceNumbers] using h
  have hev : (fun c => BetheSmooth.sourceRoots L n c) =ᶠ[𝓝[>] 0] Q :=
    eventually_nhdsWithin_of_forall fun c hc => (heq c hc).symm
  obtain ⟨h1, h2⟩ := QuantumNLS.BetheZeroLimitLiteral.zero_limit_literal hL hn
  refine ⟨h1.congr' hev, fun j k hjk => (h2 j k hjk).congr' ?_⟩
  exact eventually_nhdsWithin_of_forall fun c hc => by simp only [heq c hc]

end QuantumNLS.RCD22Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.RCD22Spec.spec
  IO.println s!"RCD22Spec.spec axioms: {ax}"
