import NlsGge.Spectral.ActualPhysicalPhaseDecayingPairIntegralBound35V1
import NlsGge.Spectral.ActualInteractionDyson00PhaseRecurrence35V1
import NlsGge.Spectral.GenericRoughMatrixDysonSummability32V1
import NlsGge.Spectral.ActualPhysicalInteractionGaugeACVolterra32V3
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Every actual even00 Dyson term is bounded by the vanishing geometric coefficient to its order, uniformly on the unit interval and over ALL real frequencies. All physical field regularity and integrability are realized; this is not yet a summed-tail or full quasimomentum asymptotic. -/
theorem actualPhysicalDyson00_allFrequency_everyOrder_bound35
    (u : PhysicalL2) (x Y : ℝ) (hY : 0 < Y) :
    ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      ‖genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle))
            ((x : ℂ)+Complex.I*(Y : ℂ))) (2*k) t 0 0‖ ≤
        (‖u‖ * Real.sqrt (‖u‖^2/(4*Y))) ^ k := by
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let B := actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ))
  let A : ℝ := ‖u‖ * Real.sqrt (‖u‖^2/(4*Y))
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg u) (Real.sqrt_nonneg _)
  have hB (i j : Fin 2) : IntervalIntegrable (fun s => B s i j) volume 0 1 := by
    apply (intervalIntegrable_actualPhysicalInteractionCoefficient32 u ((x : ℂ)+Complex.I*(Y : ℂ)) i j).mono_set
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro s hs
    exact ⟨hs.1, hs.2.trans (by norm_num)⟩
  intro k
  induction k with
  | zero =>
      intro t ht
      simp only [Nat.mul_zero, genericRoughMatrixDysonTerm32, Matrix.one_apply,
        ite_true, norm_one, pow_zero]
      exact le_rfl
  | succ k ih =>
      intro t ht
      let F : ℝ → ℂ := fun r => genericRoughMatrixDysonTerm32 B (2*k) r 0 0
      have hc : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
        continuousOn_genericRoughMatrixDysonTerm32 B 1 (by norm_num) hB (2*k) 0 0
      have hb : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖F r‖ ≤ A^k := by
        intro r hr
        exact ih r hr
      have hp : ContinuousOn (complexRealOscillatoryPhase35 (2*x))
          (Set.Icc (0 : ℝ) 1) := (complexRealOscillatoryPhase_continuous35 _).continuousOn
      have hq : ContinuousOn (complexRealOscillatoryPhase35 (-2*x))
          (Set.Icc (0 : ℝ) 1) := (complexRealOscillatoryPhase_continuous35 _).continuousOn
      have hnp : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖complexRealOscillatoryPhase35 (2*x) r‖=1 :=
        fun r _ => complexRealOscillatoryPhase_norm35 _ r
      have hnq : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖complexRealOscillatoryPhase35 (-2*x) r‖=1 :=
        fun r _ => complexRealOscillatoryPhase_norm35 _ r
      have hpair := actualPhysicalPhaseDecayingPairIntegral_bound35 u Y hY
        (complexRealOscillatoryPhase35 (2*x)) (complexRealOscillatoryPhase35 (-2*x))
        F hp hq hnp hnq hc (A^k)
        (pow_nonneg hA k) hb t ht
      have hr := actualInteractionDyson00_phaseRecurrence35 U x Y k t
      have hrec : genericRoughMatrixDysonTerm32 B (2*(k+1)) t 0 0 =
          ∫ s in (0 : ℝ)..t, U s*complexRealOscillatoryPhase35 (2*x) s*
            (∫ r in (0 : ℝ)..s, (Real.exp (-2*Y*(s-r)) : ℂ)*star (U r)*(complexRealOscillatoryPhase35 (-2*x) r*F r)) := by
        simpa only [Nat.mul_add, Nat.mul_one] using! hr
      change ‖genericRoughMatrixDysonTerm32 B (2*(k+1)) t 0 0‖ ≤ A^(k+1)
      rw [hrec]
      calc
        _ ≤ (A^k*‖u‖)*Real.sqrt (‖u‖^2/(4*Y)) := hpair.2
        _ = A^(k+1) := by rw [pow_succ]; dsimp [A]; ring

end NlsGge.SpectralFoundations
end
