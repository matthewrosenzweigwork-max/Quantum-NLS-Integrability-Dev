import QuantumNLS.Local005SourceResetD
/-! integrator-authored trusted spec for LOCAL-005 (terra_review r185 FULL ACCEPT): headline statement(s) copied verbatim from Local005SourceResetD (QuantumNLS.Local005.SourceD). -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace QuantumNLS.L005Spec
open QuantumNLS.Local005
open QuantumNLS.Local005.SourceD
open QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.ResolventWordEstimateStage2LOCAL005
variable {L r κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem reset_resolvent_word_spec (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) :
    ∃ C : ℝ, 0 < C ∧ independentSlotBounds L r κ C ∧
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ (n : ℤ) (u : ScalarInterval L), ‖u‖ < ρ →
        ∀ kind : WordKind, HasSum (sourceWord hL hκ hr hsmall kind u n)
          (sourceCompressed (κ := κ) (r := r) kind u n)) ∧
      (∀ (kind : WordKind) (u : ScalarInterval L) (n : ℤ) (k : ℕ),
        orderedSourceWord hL hκ hr hsmall kind (extendInputs (fun _ : Fin k => u)) n k =
          sourceWord hL hκ hr hsmall kind u n k) ∧
      (∀ (kind : WordKind) (u : ScalarInterval L) (n : ℤ) (k : ℕ) (a : ℝ),
        sourceWord hL hκ hr hsmall kind (a • u) n k =
          (a : ℂ) ^ k • sourceWord hL hκ hr hsmall kind u n k) ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (u : Fin k → ScalarInterval L) (kind : WordKind),
        (∀ (n : ℤ) (i j : Fin 2),
          entryFunctional n i j (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k) =
            coefficientEntry L r κ kind k (physicalInputs j u) n i j ∧
          Summable (fun q : Fin (k - 1) → ℤ =>
            ‖pathCoefficient L r κ kind j (physicalInputs j u) n q‖) ∧
          ‖entryFunctional n i j (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k)‖ ≤
            physicalMajorant L r κ kind k (extendInputs u) n) ∧
        if Odd k then
          (∀ (n : ℤ) (j : Fin 2),
            entryFunctional n j j (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k) = 0) ∧
          Summable (fun n : ℤ => physicalMajorant L r κ kind k (extendInputs u) n ^ 2) ∧
          ∑' n : ℤ, physicalMajorant L r κ kind k (extendInputs u) n ^ 2 ≤
            (C ^ k * ∏ t : Fin k, ‖u t‖) ^ 2
        else
          (∀ (n : ℤ) (i j : Fin 2), i ≠ j →
            entryFunctional n i j (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k) = 0) ∧
          ∀ n : ℤ, physicalMajorant L r κ kind k (extendInputs u) n ≤ C ^ k * ∏ t : Fin k, ‖u t‖ := by
  exact QuantumNLS.Local005.SourceD.reset_resolvent_word hL hκ hr hsmall

end QuantumNLS.L005Spec
#print axioms QuantumNLS.L005Spec.reset_resolvent_word_spec
