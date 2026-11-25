import Mathlib
import QuantumNLS.StrongLimit
import QuantumNLS.QuantileCore

/-!
# R-8F7E0394 (`CC:F03:deterministic`): the theorem for `BulkResponseData`

`strong_limit_bulk`: for the standing data `D : BulkResponseData` (`BulkMeasure`, i.e. `CC:F03:core` hypotheses and the printed finite second moment, `L, κ > 0`),
any ordered (indeed any) real arrays `q^{(N)}` whose step quantiles `Q_N` converge to `Q` in `L²(0,1)` and the step functions `F_N` of the solutions of `B_N v = q`:
`‖F_N − F‖₂ → 0` where `F` is the unique solution of `D.IsResponse` (`BulkResponseRiesz`), and the discrete nonlocal energies converge to `𝓔(F)`.
The measurable representative `qm D.μ` of `bulkQuantile D.μ` is used (they agree a.e.); the atomlessness of `μ` enters only through `{Q t = Q s}` being null.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace QuantumNLS.StrongLimitBulk

open QuantumNLS.BulkResponseRiesz (mu2 isBulkResponse_congr hasFiniteSecondMoment_of_moment)
open QuantumNLS.QuantileForm (uI formEnergy_congr quantile_ae_qm)
open QuantumNLS.QuantileTransport (qm map_qm measurable_qm)
open QuantumNLS.BulkResponseForm (BulkResponseData bulkQuantile IsSmoothQuantilePullback IsFormCore
  IsBulkResponse formDomain L2Unit formEnergy)
open QuantumNLS.StepIntegrals (stepF stepL2)
open QuantumNLS.FiniteResponse (Bop)
open QuantumNLS.GLowerBound (ENint)

theorem isFormCore_congr {L κ : ℝ} {Q Q' : ℝ → ℝ} (hQ : Q =ᵐ[uI] Q') {S : Set L2Unit}
    (h : IsFormCore L κ Q S) : IsFormCore L κ Q' S := by
  have hE : ∀ F : ℝ → ℝ, formEnergy Q F = formEnergy Q' F := fun F =>
    formEnergy_congr hQ (Filter.EventuallyEq.refl _ _)
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun G hG => ?_, fun F hF ε hε => ?_⟩
  · have := h1 hG
    show formEnergy Q' G < ⊤
    rw [← hE]; exact this
  · have hF' : F ∈ formDomain Q := by
      show formEnergy Q F < ⊤
      rw [hE]; exact hF
    obtain ⟨G, hG, hlt⟩ := h2 F hF' ε hε
    exact ⟨G, hG, by rw [← hE]; exact hlt⟩

/-- `Q = qm μ ∈ L²(0,1)` (the printed second moment). -/
theorem memLp_qm_bulk (D : BulkResponseData) : MemLp (qm D.μ) 2 uI := by
  haveI := D.hμ.isProbability
  exact QuantumNLS.QuantileTransport.memLp_qm D.μ
    (hasFiniteSecondMoment_of_moment D.hμ.finiteSecondMoment)

/-- The `L²(0,1)` element of `Q`. -/
def Q2 (D : BulkResponseData) : L2Unit := (memLp_qm_bulk D).toLp (qm D.μ)

theorem strong_limit_bulk (D : BulkResponseData) {F : L2Unit} (hF : D.IsResponse F)
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (q : ∀ n, Fin (N n) → ℝ) (Fv : ∀ n, Fin (N n) → ℝ)
    (hFv : ∀ n, Bop D.L (D.κ / N n) (q n) (Fv n) = q n)
    (hQc : Tendsto (fun n => ‖stepL2 (q n) - Q2 D‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖stepL2 (Fv n) - F‖) atTop (𝓝 0) ∧
    Tendsto (fun n => (ENint (D.κ / N n) (stepF (N n) (q n)) (stepF (N n) (Fv n))).toReal) atTop
      (𝓝 (formEnergy (qm D.μ) F).toReal) := by
  haveI := D.hμ.isProbability
  have hQ : bulkQuantile D.μ =ᵐ[uI] qm D.μ := quantile_ae_qm D.μ
  have hQm : Measurable (qm D.μ) := measurable_qm D.μ
  have hna : ∀ a : ℝ, uI (qm D.μ ⁻¹' {a}) = 0 := fun a => by
    have h1 : uI.map (qm D.μ) = D.μ := map_qm D.μ
    have h2 := Measure.map_apply hQm (measurableSet_singleton a) (μ := uI)
    rw [h1] at h2
    rw [← h2]
    exact D.hμ.noAtoms.measure_singleton a
  have hF' : IsBulkResponse D.L D.κ (qm D.μ) F := (isBulkResponse_congr hQ).1 hF
  have hS : IsFormCore D.L D.κ (qm D.μ) {G | IsSmoothQuantilePullback (bulkQuantile D.μ) G} :=
    isFormCore_congr hQ (QuantumNLS.QuantileCore.isFormCore_bulk D.L D.κ D.hL D.hκ D.μ D.hμ)
  refine QuantumNLS.StrongLimit.strong_limit D.hL D.hκ hQm (memLp_qm_bulk D)
    (QuantumNLS.SmoothRecovery.null_eq hQm hna) hF' hS ?_ hN hNt q Fv hFv hQc
  rintro G ⟨h, hsm, hcs, hGae⟩
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hsm (by simp)
  obtain ⟨B, hB⟩ := hsm.continuous.bounded_above_of_compact_support hcs
  refine ⟨h, K, B, hK, fun x => by simpa using hB x, ?_⟩
  filter_upwards [hGae, hQ] with t h1 h2
  rw [h1]; simp [Function.comp, h2]

end QuantumNLS.StrongLimitBulk

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.StrongLimitBulk.isFormCore_congr
#print axioms QuantumNLS.StrongLimitBulk.strong_limit_bulk
