import Mathlib
import QuantumNLS.ValuesTailBias
import QuantumNLS.ValuesTailMarkov
import QuantumNLS.ValuesTailIdentify

/-!
# R-CB4CC6EE (`values:lem:tail`), B5: the barycentric tail bound

Final named theorem `QuantumNLS.ValuesTail.values_tail`, with the printed quantifiers: for every integer
`p ≥ 1` there is `C_p` (independent of the unit smooth profile, of `N`, of `R`); for every unit smooth
periodic profile `φ = smoothL2 hf` there is `C_{p,φ}` (independent of the limiting measure `μ`, which is
forced to equal `M_{κ,φ}` by `ValuesTailIdentify.limit_eq_Mmeas`); and for all `N ≥ 1` and `R ≥ 2η₀`,

  `E L_N(|t| > R) ≤ C_{p,φ} R^{-2p} + C_p/(N R)`,

where `E L_N(|t|>R) = ∫ (empirical measure of m)(|t|>R) dBorn(m)` (the Born average).

Proof: Markov step `ValuesTailMarkov.tail_le_two_pow_mul_filter` applied pointwise in the Born index,
the Born-averaged filter bias `ValuesTailBias.born_filter_bias`, and the moment bound
`ValuesTailMarkov.integral_filter_le` with the finite `2p`th moment `ValuesTailIdentify.integrable_moment_of_limit`.
Nothing here is accepted; review pending.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace QuantumNLS.ValuesTail

open QuantumNLS.ClassicalCharges QuantumNLS.CauchyUniqueness QuantumNLS.FullMass
open QuantumNLS.SmoothScalarMomentsAsymptotic QuantumNLS.SmoothScalarMomentsCauchy
open QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.ValuesTailMarkov (filterF tail_le_two_pow_mul_filter integral_filter_le filterF_nonneg filterF_le_one)
open QuantumNLS.ValuesTailBias (empMeas integrable_of_bdd born_filter_bias)
open QuantumNLS.ValuesTailIdentify (limit_eq_Mmeas integrable_moment_of_limit)

variable {L : ℝ} [Fact (0 < L)]

/-- **B5: barycentric tail bound (`values:lem:tail`, R-CB4CC6EE).** -/
theorem values_tail {κ : ℝ} (hκ : 0 < κ) (p : ℕ) (hp : 1 ≤ p) :
    ∃ Cp : ℝ, ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (hu : ‖smoothL2 hf‖ = 1),
      ∃ Cpf : ℝ, ∀ μ : ProbabilityMeasure ℝ,
        QuantumNLS.BulkResponseActual.IsLimitingRapidityMeasure L κ hκ (smoothL2 hf) hu μ →
        ∀ (N : ℕ) (hN : 0 < N) (R : ℝ), 2 * max (4 * κ) (Real.log 16 / L) ≤ R →
          (∫ m : QuantumNLS.BetheLabels.MArr N, (empMeas L κ N m).real {t : ℝ | R < |t|}
              ∂(QuantumNLS.EmpiricalRapidity.bornMeasure
                  (QuantumNLS.BulkResponseActual.physBasis L hκ N) (smoothL2 hf) hu))
            ≤ Cpf / R ^ (2 * p) + Cp / (N * R) := by
  obtain ⟨D, hD⟩ := born_filter_bias (L := L) hκ p
  refine ⟨2 ^ p * D, fun f hf hu => ⟨2 ^ p * (∫ t : ℝ, |t| ^ (2 * p) ∂(Mmeas κ (smoothL2 hf))),
    fun μ hμ N hN R hR2 => ?_⟩⟩
  obtain ⟨β, hβ⟩ : ∃ β : Measure (QuantumNLS.BetheLabels.MArr N),
      β = QuantumNLS.EmpiricalRapidity.bornMeasure
        (QuantumNLS.BulkResponseActual.physBasis L hκ N) (smoothL2 hf) hu := ⟨_, rfl⟩
  have hβP : IsProbabilityMeasure β := by
    rw [hβ]
    infer_instance
  rw [← hβ]
  have hη : 0 < max (4 * κ) (Real.log 16 / L) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hR : 0 < R := by linarith
  have hmom : Integrable (fun t : ℝ => |t| ^ (2 * p)) (μ : Measure ℝ) :=
    integrable_moment_of_limit hκ hf hu hμ (2 * p)
  have hBias := (abs_le.mp (hD N hN (smoothL2 hf) hu μ hμ R hR2)).2
  have hMark := integral_filter_le hR (μ : Measure ℝ) hmom
  -- the Born-average problem is stated with the bias for `μ` itself; identify `μ = M_{κ,φ}`
  rw [limit_eq_Mmeas hκ hf hu hμ] at hBias hMark
  rw [← hβ] at hBias
  have hpt : ∀ m : QuantumNLS.BetheLabels.MArr N,
      (empMeas L κ N m).real {t : ℝ | R < |t|} ≤
        2 ^ p * ∫ t : ℝ, filterF p R t ∂(empMeas L κ N m) :=
    fun m => tail_le_two_pow_mul_filter hR (empMeas L κ N m)
  have hF_bd : ∀ m : QuantumNLS.BetheLabels.MArr N,
      |∫ t : ℝ, filterF p R t ∂(empMeas L κ N m)| ≤ 1 := by
    intro m
    have h := norm_integral_le_of_norm_le_const (μ := empMeas L κ N m)
      (f := fun t : ℝ => filterF p R t) (C := 1)
      (ae_of_all _ (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (filterF_nonneg p R t)]
        exact filterF_le_one p hR t))
    rw [Real.norm_eq_abs] at h
    simpa using h
  have intR : ∀ g : QuantumNLS.BetheLabels.MArr N → ℝ, (∀ m, |g m| ≤ 1) → Integrable g β :=
    fun g hg => Integrable.of_bound (C := 1) Measurable.of_discrete.aestronglyMeasurable
      (ae_of_all _ (fun m => by rw [Real.norm_eq_abs]; exact hg m))
  have hint1 : Integrable (fun m : QuantumNLS.BetheLabels.MArr N =>
      (empMeas L κ N m).real {t : ℝ | R < |t|}) β :=
    intR (fun m => (empMeas L κ N m).real {t : ℝ | R < |t|})
      (fun m => le_trans (le_of_eq (abs_of_nonneg measureReal_nonneg)) measureReal_le_one)
  have hint2 : Integrable (fun m : QuantumNLS.BetheLabels.MArr N =>
      ∫ t : ℝ, filterF p R t ∂(empMeas L κ N m)) β :=
    intR (fun m => ∫ t : ℝ, filterF p R t ∂(empMeas L κ N m)) hF_bd
  calc (∫ m : QuantumNLS.BetheLabels.MArr N, (empMeas L κ N m).real {t : ℝ | R < |t|} ∂β)
      ≤ ∫ m : QuantumNLS.BetheLabels.MArr N,
          2 ^ p * ∫ t : ℝ, filterF p R t ∂(empMeas L κ N m) ∂β :=
        integral_mono hint1 (hint2.const_mul _) hpt
    _ = 2 ^ p * ∫ m : QuantumNLS.BetheLabels.MArr N,
          ∫ t : ℝ, filterF p R t ∂(empMeas L κ N m) ∂β := integral_const_mul _ _
    _ ≤ 2 ^ p * ((∫ t : ℝ, |t| ^ (2 * p) ∂(Mmeas κ (smoothL2 hf))) / (R ^ 2) ^ p +
          D / (N * R)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = (2 ^ p * ∫ t : ℝ, |t| ^ (2 * p) ∂(Mmeas κ (smoothL2 hf))) / R ^ (2 * p) +
          2 ^ p * D / (N * R) := by
        rw [← pow_mul]
        ring

end QuantumNLS.ValuesTail

#print axioms QuantumNLS.ValuesTail.values_tail
