import QuantumNLS.Prop001Dynamics
import QuantumNLS.MarginalPureState

/-! PROP-001: actual evolved marginals and the uniform packet perturbation
bound. No convergence rate for the product initial state is assumed here. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace QuantumNLS.Prop001
open TensorCarrier PhysicalTensor TraceClass
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def marginal (A : Interactions H) (N k : ℕ) (hk : k ≤ N)
    (t : ℝ) (ψ : SymSector ℂ H N) :
    HilbertTensorPower ℂ H k →L[ℂ] HilbertTensorPower ℂ H k :=
  reducedDensityN N k hk (quantumEvolution A N t ψ : HilbertTensorPower ℂ H N)

theorem marginal_positive (A : Interactions H) (N k : ℕ) (hk : k ≤ N)
    (t : ℝ) (ψ : SymSector ℂ H N) : (marginal A N k hk t ψ).IsPositive :=
  reducedDensityN_isPositive N k hk _

theorem marginal_trace_one (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    (N k : ℕ) (hk : k ≤ N) (t : ℝ) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1)
    {ι : Type*} (b : HilbertBasis ι ℂ (HilbertTensorPower ℂ H k)) :
    traceIn b (marginal A N k hk t ψ) = 1 := by
  apply traceIn_reducedDensityN_eq_one
  change ‖quantumEvolution A N t ψ‖ = 1
  rw [quantumEvolution_norm A hA, hψ]

theorem marginal_traceNorm (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    (N k : ℕ) (hk : k ≤ N) (t : ℝ) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) :
    traceNorm (marginal A N k hk t ψ) = 1 := by
  rw [marginal, traceNorm_reducedDensityN]
  change ENNReal.ofReal (‖quantumEvolution A N t ψ‖ ^ 2) = 1
  rw [quantumEvolution_norm A hA, hψ]
  norm_num

/-- The uniform d_k≤2 bound on the actual source marginals. -/
theorem marginal_error_le_two (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    (N k : ℕ) (hk : k ≤ N) (t : ℝ) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1)
    (v : H) (hv : ‖v‖ = 1) :
    traceNorm (marginal A N k hk t ψ -
      InnerProductSpace.rankOne ℂ (htpow k v : HilbertTensorPower ℂ H k) (htpow k v)) ≤ 2 := by
  let Q := InnerProductSpace.rankOne ℂ (htpow (𝕜 := ℂ) k v : HilbertTensorPower ℂ H k)
    (htpow (𝕜 := ℂ) k v)
  have hQ : traceNorm Q = 1 := by
    have h := traceNorm_reducedDensityN N k hk (htpow N v : HilbertTensorPower ℂ H N)
    rw [reducedDensityN_htpow, hv] at h
    simpa [Q, norm_htpow, hv] using h
  have hneg : traceNorm (-Q) = 1 := by
    rw [← neg_one_smul ℂ Q, traceNorm_smul, hQ]
    simp
  calc
    _ = traceNorm (marginal A N k hk t ψ + -Q) := by rw [sub_eq_add_neg]
    _ ≤ traceNorm (marginal A N k hk t ψ) + traceNorm (-Q) := traceNorm_add_le _ _
    _ = 2 := by rw [marginal_traceNorm A hA N k hk t ψ hψ, hneg]; norm_num

/-- Eq. A2-packet-stability for the literal finite generator, for any two
normalized symmetric-sector initial states and every real time. -/
theorem packet_stability (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    (N k : ℕ) (hk : k ≤ N) (t : ℝ) (ψ φ : SymSector ℂ H N)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (marginal A N k hk t ψ - marginal A N k hk t φ) ≤
      ENNReal.ofReal (2 * ‖ψ - φ‖) := by
  have h := MarginalPureState.traceNorm_reducedDensityN_sub_le N k hk
    (quantumEvolution A N t ψ : HilbertTensorPower ℂ H N)
    (quantumEvolution A N t φ : HilbertTensorPower ℂ H N)
  have hd : ‖(quantumEvolution A N t ψ : HilbertTensorPower ℂ H N) -
      (quantumEvolution A N t φ : HilbertTensorPower ℂ H N)‖ = ‖ψ - φ‖ := by
    change ‖quantumEvolution A N t ψ - quantumEvolution A N t φ‖ = ‖ψ - φ‖
    rw [← map_sub, quantumEvolution_norm A hA]
  have hnψ : ‖(quantumEvolution A N t ψ : HilbertTensorPower ℂ H N)‖ = 1 := by
    change ‖quantumEvolution A N t ψ‖ = 1
    rw [quantumEvolution_norm A hA, hψ]
  have hnφ : ‖(quantumEvolution A N t φ : HilbertTensorPower ℂ H N)‖ = 1 := by
    change ‖quantumEvolution A N t φ‖ = 1
    rw [quantumEvolution_norm A hA, hφ]
  simpa only [marginal, hd, hnψ, hnφ, one_add_one_eq_two, mul_comm] using h

theorem product_packet_stability (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (N k : ℕ) (hk : k ≤ N)
    (t : ℝ) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (u : H) (hu : ‖u‖ = 1) :
    traceNorm (marginal A N k hk t ψ - marginal A N k hk t (productVector N u)) ≤
      ENNReal.ofReal (2 * ‖ψ - productVector N u‖) :=
  packet_stability A hA N k hk t ψ (productVector N u) hψ
    (by rw [productVector_norm, hu, one_pow])

/-- The perturbed marginal differs from any chosen comparison operator by
at most the actual product-state error plus twice the initial vector error.
This is an unconditional triangle inequality, not a hypothesis of propagation. -/
theorem perturbed_comparison (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (N k : ℕ) (hk : k ≤ N)
    (t : ℝ) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (u : H) (hu : ‖u‖ = 1)
    (Q : HilbertTensorPower ℂ H k →L[ℂ] HilbertTensorPower ℂ H k) :
    traceNorm (marginal A N k hk t ψ - Q) ≤
      traceNorm (marginal A N k hk t (productVector N u) - Q) +
        ENNReal.ofReal (2 * ‖ψ - productVector N u‖) := by
  have h := traceNorm_add_le
    (marginal A N k hk t ψ - marginal A N k hk t (productVector N u))
    (marginal A N k hk t (productVector N u) - Q)
  rw [sub_add_sub_cancel] at h
  exact h.trans (by
    rw [add_comm]
    exact add_le_add_right (product_packet_stability A hA N k hk t ψ hψ u hu) _)

/-- Real trace-norm version of the final packet comparison, with
finiteness proved from the actual density operators. -/
theorem perturbed_product_comparison_real (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (N k : ℕ) (hk : k ≤ N)
    (t : ℝ) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (traceNorm (marginal A N k hk t ψ -
      InnerProductSpace.rankOne ℂ (htpow k v : HilbertTensorPower ℂ H k) (htpow k v))).toReal ≤
    (traceNorm (marginal A N k hk t (productVector N u) -
      InnerProductSpace.rankOne ℂ (htpow k v : HilbertTensorPower ℂ H k) (htpow k v))).toReal +
      2 * ‖ψ - productVector N u‖ := by
  let Q := InnerProductSpace.rankOne ℂ (htpow (𝕜 := ℂ) k v : HilbertTensorPower ℂ H k)
    (htpow (𝕜 := ℂ) k v)
  have hfin : traceNorm (marginal A N k hk t (productVector N u) - Q) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (marginal_error_le_two A hA N k hk t (productVector N u)
        (by rw [productVector_norm, hu, one_pow]) v hv)
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩)
    (perturbed_comparison A hA N k hk t ψ hψ u hu Q)
  simpa only [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (show 0 ≤ 2 * ‖ψ - productVector N u‖ by positivity)] using h

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.marginal_positive
#print axioms QuantumNLS.Prop001.marginal_trace_one
#print axioms QuantumNLS.Prop001.marginal_traceNorm
#print axioms QuantumNLS.Prop001.marginal_error_le_two
#print axioms QuantumNLS.Prop001.packet_stability
#print axioms QuantumNLS.Prop001.product_packet_stability
#print axioms QuantumNLS.Prop001.perturbed_comparison
#print axioms QuantumNLS.Prop001.perturbed_product_comparison_real
