import QuantumNLS.ExternalConfinement

/-! integrator-authored trusted spec for R-52E511D4 `CC:F04:external-confinement`
(root_response/F04.tex:36-52). K ≥ 1, c > 0, L > 0 (F04 standing assumption), H : ℝ → ℝ continuous with
H(y) − H(x) ≥ L(y − x) for y ≥ x; t_1 < ⋯ < t_K and ν_1 ≤ ⋯ ≤ ν_K with
H(t_i) − 2 Σ_{j≠i} arctan(c/(t_i − t_j)) = 2πν_i. Then H is onto (and one-to-one, so H⁻¹ is defined),
and every p with H(p) = 2πν_i (i.e. p_i = H⁻¹(2πν_i)) satisfies |t_i − p_i| ≤ 4√(cK/L). -/

namespace QuantumNLS.R52E5Spec

def Spec : Prop :=
  ∀ (K : ℕ), 1 ≤ K → ∀ (L c : ℝ), 0 < L → 0 < c → ∀ (H : ℝ → ℝ), Continuous H →
    (∀ x y, x ≤ y → H y - H x ≥ L * (y - x)) →
    ∀ (t ν : Fin K → ℝ), StrictMono t → Monotone ν →
    (∀ i, H (t i) - 2 * ∑ j ∈ Finset.univ.erase i, Real.arctan (c / (t i - t j)) = 2 * Real.pi * ν i) →
    Function.Surjective H ∧ Function.Injective H ∧
      ∀ i (p : ℝ), H p = 2 * Real.pi * ν i → |t i - p| ≤ 4 * Real.sqrt (c * K / L)

theorem spec : Spec := fun _K hK _L _c hL hc _H hHc hH _t _ν ht hν heq =>
  QuantumNLS.ExternalConfinement.external_confinement hK hL hc hHc (fun x y hxy => hH x y hxy) ht hν heq

end QuantumNLS.R52E5Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R52E5Spec.spec
  IO.println s!"R52E5Spec.spec axioms: {ax}"
