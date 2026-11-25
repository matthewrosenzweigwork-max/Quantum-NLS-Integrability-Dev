import LiebLiniger.FixedPeriod.Quantum.WickSourcePowers
import Mathlib.Tactic.Ring

/-! Actual pure rank-one sector normal order. Source-only extraction from e459,
with two proof-only repairs for the actual e459 lines 298 and 337 diagnostics.
The exact source powers parent must be fully qualified before any check. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

private theorem q2024_sector_inner_smul_left (n : ℕ) (a : ℂ)
    (x y : SymmetricSector μ n) :
    inner ℂ (a • x) y = (starRingEnd ℂ) a * inner ℂ x y := by
  change inner ℂ (a • (x : ProductL2 μ (Fin n))) (y : ProductL2 μ (Fin n)) = _
  exact inner_smul_left (𝕜 := ℂ) _ _ _

private theorem q2024_sector_inner_smul_right (n : ℕ) (a : ℂ)
    (x y : SymmetricSector μ n) :
    inner ℂ x (a • y) = a * inner ℂ x y := by
  change inner ℂ (x : ProductL2 μ (Fin n)) (a • (y : ProductL2 μ (Fin n))) = _
  exact inner_smul_right (𝕜 := ℂ) _ _ _

private theorem sourcePower_cast_pure {m n : ℕ} (heq : m = n) (u : Lp ℂ 2 μ) :
    symmetricSectorCast μ heq (pureSymmetricTensor μ m u) = pureSymmetricTensor μ n u := by
  subst n
  rfl

/-- Actual p annihilations followed by actual q creations, with precisely the
source sector conventions and k spectator particles. -/
def sourceWickPureRankNormalOrder (epsilon : ℝ) (h g : Lp ℂ 2 μ) (p q k : ℕ) :
    SymmetricSector μ (p + k) →L[ℂ] SymmetricSector μ (q + k) :=
  (symmetricSectorCast μ (Nat.add_comm k q)).toLinearIsometry.toContinuousLinearMap ∘L
    sourceWickCreationPower μ epsilon h k q ∘L
    sourceWickAnnihilationPower μ epsilon g k p ∘L
    (symmetricSectorCast μ (Nat.add_comm p k)).toLinearIsometry.toContinuousLinearMap

/-- The actual normal-ordered physical product has the SAME polarized matrix
coefficient as the independently constructed source pure-rank-one Wick map. -/
theorem sourceWickPureRankNormalOrder_pairing (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (h g v u : Lp ℂ 2 μ) (p q k : ℕ) :
    inner ℂ (pureSymmetricTensor μ (q + k) v)
      (sourceWickPureRankNormalOrder μ epsilon h g p q k
        (pureSymmetricTensor μ (p + k) u)) =
      (LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ) *
        ((inner ℂ v h ^ q * inner ℂ g u ^ p) * inner ℂ v u ^ k) := by
  change inner ℂ (pureSymmetricTensor μ (q + k) v)
    (symmetricSectorCast μ (Nat.add_comm k q)
      ((sourceWickAnnihilationPower μ epsilon h k q).adjoint
        (sourceWickAnnihilationPower μ epsilon g k p
          (symmetricSectorCast μ (Nat.add_comm p k)
            (pureSymmetricTensor μ (p + k) u))))) = _
  rw [sourcePower_cast_pure]
  have hv := sourcePower_cast_pure μ (Nat.add_comm k q) v
  rw [← hv, (symmetricSectorCast μ (Nat.add_comm k q)).inner_map_map,
    ContinuousLinearMap.adjoint_inner_right,
    sourceWickAnnihilationPower_pure μ epsilon hepsilon,
    sourceWickAnnihilationPower_pure μ epsilon hepsilon,
    q2024_sector_inner_smul_left μ k, q2024_sector_inner_smul_right μ k]
  simp only [map_mul, map_pow, Complex.conj_ofReal, inner_conj_symm,
    inner_pureSymmetricTensor, smul_eq_mul]
  have hc : (sourceWickPowerCoefficient epsilon k p : ℂ) *
      (sourceWickPowerCoefficient epsilon k q : ℂ) =
        (LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ) := by
    exact_mod_cast sourceWickPowerCoefficient_mul epsilon hepsilon k p q
  rw [← hc]
  ring

/-- GENUINE actual source-Wick pure rank-one normal ordering, complete sectors:
Wick_epsilon(|h^q><g^p|) = q actual source creations after p actual source
annihilations, with k spectators and all p/q/k=0 cases retained. -/
theorem wickSectorAdded_pure_rankOne_eq_source_normal_order (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (h g : Lp ℂ 2 μ) (p q k : ℕ) :
    wickSectorAdded μ epsilon
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ q h)
          (pureSymmetricTensor μ p g)) k =
      sourceWickPureRankNormalOrder μ epsilon h g p q k := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  change inner ℂ (pureSymmetricTensor μ (q + k) v)
    ((LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ) •
      unscaledWickAdded μ
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ q h)
          (pureSymmetricTensor μ p g)) k (pureSymmetricTensor μ (p + k) u)) = _
  rw [q2024_sector_inner_smul_right μ (q + k),
    unscaledWickAdded_pairing, sourceWickPureRankNormalOrder_pairing μ epsilon hepsilon]
  simp only [wickKernelPolarized, InnerProductSpace.rankOne_apply,
    q2024_sector_inner_smul_right μ, inner_pureSymmetricTensor, smul_eq_mul]
  ring
end LiebLiniger.FixedPeriod.Quantum
end
