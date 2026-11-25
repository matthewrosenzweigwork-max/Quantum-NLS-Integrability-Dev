import QuantumNLS.AdjacentResponse
import QuantumNLS.RC54DSpec

/-! integrator-authored trusted spec for R-9D98846E `CC:F01:response` (root_response/F01.tex:40-66).
Occupation vectors are DEF-006 arrays (`MArr N`: finitely supported η : ℤ → ℕ of total N); the ordered Bose
labels and ordered roots are the accepted DEF-006 / R-4C8D7C9E objects (`correctedInt (labelsEquivArr.symm η)`,
`arrRoots`). For η with η_b ≥ 1 and any m with m_ℓ = η_ℓ − [ℓ=b] + [ℓ=a], q = roots(η), q̃ = roots(m),
C_k = Σ_{ℓ≤k} η_ℓ, B = ∫₀¹ DT(q + t(q̃ − q)) dt (RC54DSpec.sB, written independently), and the rank vector
Σ_{k=b}^{a−1} e_{C_k} with repeated ranks kept (1-based rank C_k ↔ index i with i+1 = C_k):
(a > b) q̃ − q = 2π B⁻¹ Σ e_{C_k} ≥ 0; ‖q̃ − q‖₁ = 2π(a−b)/L; Q₂(m) − Q₂(η) = 2π Σ_k [B⁻¹(q+q̃)]_{C_k};
at every rank C_k both old and new labels lie in [b,a].
(a < b) q̃ − q = −2π B⁻¹ Σ_{k=a}^{b−1} e_{C^m_k} (interchanged configurations; the same B), all roots
decrease, ‖q̃ − q‖₁ = 2π|a−b|/L. -/

open scoped Matrix

namespace QuantumNLS.R9D98Spec

open QuantumNLS.BetheLabels

def sC {N : ℕ} (η : MArr N) (k : ℤ) : ℕ := ∑ l ∈ η.1.support.filter (· ≤ k), η.1 l

noncomputable def sRank {N : ℕ} (η : MArr N) (b a : ℤ) (i : Fin N) : ℝ :=
  ∑ k ∈ Finset.Ico b a, (if (i.val : ℤ) + 1 = sC η k then 1 else 0)

noncomputable def lab {N : ℕ} (η : MArr N) : Fin N → ℤ := correctedInt (labelsEquivArr.symm η)

def IsTransfer {N : ℕ} (η m : MArr N) (b a : ℤ) : Prop :=
  ∀ l, (m.1 l : ℤ) = η.1 l - (if l = b then 1 else 0) + (if l = a then 1 else 0)

def Spec : Prop :=
  ∀ (N : ℕ) (L c : ℝ), 0 < L → 0 < c → ∀ (η m : MArr N) (b a : ℤ), 1 ≤ η.1 b → IsTransfer η m b a →
    (b < a →
      let q := arrRoots L c η; let qt := arrRoots L c m; let B := RC54DSpec.sB L c q qt
      qt - q = (2 * Real.pi) • (B⁻¹ *ᵥ sRank η b a) ∧ (∀ i, q i ≤ qt i) ∧
      ∑ i, |qt i - q i| = 2 * Real.pi / L * (a - b) ∧
      ∑ i, qt i ^ 2 - ∑ i, q i ^ 2 =
        2 * Real.pi * ∑ k ∈ Finset.Ico b a, ∑ i : Fin N,
          (if (i.val : ℤ) + 1 = sC η k then (B⁻¹ *ᵥ (q + qt)) i else 0) ∧
      (∀ k ∈ Finset.Ico b a, ∀ i : Fin N, (i.val : ℤ) + 1 = sC η k →
        b ≤ lab η i ∧ lab η i ≤ a ∧ b ≤ lab m i ∧ lab m i ≤ a)) ∧
    (a < b →
      let q := arrRoots L c η; let qt := arrRoots L c m; let B := RC54DSpec.sB L c q qt
      qt - q = -((2 * Real.pi) • (B⁻¹ *ᵥ sRank m a b)) ∧ (∀ i, qt i ≤ q i) ∧
      ∑ i, |qt i - q i| = 2 * Real.pi / L * |a - b|)

theorem transfer_eq {N : ℕ} (η m : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b) (h : IsTransfer η m b a) :
    m = AdjacentResponse.transfer η hb a := by
  apply Subtype.ext
  ext l
  have h1 := h l
  have h2 := AdjacentResponse.transfer_apply η hb a l
  exact_mod_cast h1.trans h2.symm

theorem spec : Spec := by
  intro N L c hL hc η m b a hb ht
  obtain rfl := transfer_eq η m hb ht
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · simp only
    rw [RC54DSpec.sB_eq L hc]
    exact AdjacentResponse.adjacent_response hL hc η hb hab
  · simp only
    rw [RC54DSpec.sB_eq L hc]
    exact AdjacentResponse.reverse_response hL hc η hb hab

end QuantumNLS.R9D98Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R9D98Spec.spec
  IO.println s!"R9D98Spec.spec axioms: {ax}"
