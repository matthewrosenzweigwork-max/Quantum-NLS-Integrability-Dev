import QuantumNLS.GaudinResponse

/-! integrator-authored trusted spec for DEF-051 "Gaudin response matrix"
(DEFINITIONS_LEDGER.md DEF-051; root_response/F01.tex CC:F01:smooth, CC:F01:jacobian). For a real root array q
and c > 0 the Gaudin matrix B is pinned by its printed action
(Bv)_i = L v_i + Σ_{j≠i} 2c (c² + (q_i − q_j)²)⁻¹ (v_i − v_j),
it is the Jacobian at q of the logarithmic Bethe map T_i(x) = L x_i + 2 Σ_{j≠i} arctan((x_i − x_j)/c),
and (for L, c > 0) it is positive definite and the response vector B⁻¹q is the unique solution of B f = q. -/

open scoped Matrix

namespace QuantumNLS.DEF051Spec

noncomputable def sT {N : ℕ} (L c : ℝ) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  L * x i + 2 * ∑ j ∈ Finset.univ.erase i, Real.arctan ((x i - x j) / c)

def Spec : Prop :=
  ∀ (N : ℕ) (L c : ℝ) (q : Fin N → ℝ),
    (∀ (v : Fin N → ℝ) (i : Fin N), (GaudinResponse.gaudinMatrix L c q *ᵥ v) i =
      L * v i + ∑ j ∈ Finset.univ.erase i, 2 * c * (c ^ 2 + (q i - q j) ^ 2)⁻¹ * (v i - v j)) ∧
    (0 < c → HasFDerivAt (sT L c)
      (Matrix.toLin' (GaudinResponse.gaudinMatrix L c q)).toContinuousLinearMap q) ∧
    (0 < L → 0 < c → (GaudinResponse.gaudinMatrix L c q).PosDef ∧
      GaudinResponse.responseVec L c q = (GaudinResponse.gaudinMatrix L c q)⁻¹ *ᵥ q ∧
      ∀ f, GaudinResponse.gaudinMatrix L c q *ᵥ f = q ↔ f = GaudinResponse.responseVec L c q)

theorem spec : Spec := fun N L c q =>
  ⟨fun v i => GaudinResponse.gaudinMatrix_mulVec L c q v i,
   fun hc => GaudinResponse.hasFDerivAt_Tsmooth L hc q,
   fun hL hc => ⟨GaudinResponse.gaudinMatrix_posDef hL hc q, rfl,
     fun f => GaudinResponse.responseVec_unique hL hc q f⟩⟩

end QuantumNLS.DEF051Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.DEF051Spec.spec
  IO.println s!"DEF051Spec.spec axioms: {ax}"
