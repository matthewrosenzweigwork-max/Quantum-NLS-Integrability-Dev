import NlsGge.Batch37.ActualPhysicalDyson00FirstPairFourierDecay37V1
import NlsGge.Spectral.ActualPhysicalNonsingular00PairOperatorBound36V3
import NlsGge.Spectral.ActualInteractionDyson00PhaseRecurrence35V1
import NlsGge.Spectral.ComplexRealOscillatoryPhase35V1
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
/-- Every fixed positive even 00 interaction coefficient decays uniformly
in bounded nonnegative height and unit endpoint as real frequency escapes.
The first-pair estimate is propagated with the actual nonsingular pair norm
bound; no frequency decay of the whole operator norm is assumed. -/
theorem actualPhysicalDyson00_fixedOrder_uniformFourierDecay37V1
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in cocompact ℝ,
      ∀ p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀,
        ‖genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ)))
          (2*(k+1)) (p.1 : ℝ) 0 0‖ < ε := by
  induction k with
  | zero =>
    simpa only [Nat.zero_add, Nat.mul_one] using
      actualPhysicalDyson00_firstPair_uniformFourierDecay37V1 u Y₀ hY₀
  | succ k ih =>
    intro ε hε
    let η : ℝ := ε / (‖u‖^2+1)
    have hη : 0 < η := by dsimp [η]; positivity
    filter_upwards [ih η hη] with x hx
    intro p
    let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
    let z : ℂ := (x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ)
    let B := actualZsInteractionCoefficient32 U z
    let F : ℝ → ℂ := fun s => genericRoughMatrixDysonTerm32 B (2*(k+1)) s 0 0
    have hB : ∀ i j, IntervalIntegrable (fun s => B s i j) volume 0 1 := by
      intro i j
      apply (intervalIntegrable_actualPhysicalInteractionCoefficient32 u z i j).mono_set
      simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
      intro s hs
      exact ⟨hs.1, hs.2.trans (by norm_num)⟩
    have hF : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
      continuousOn_genericRoughMatrixDysonTerm32 B 1 (by norm_num) hB (2*(k+1)) 0 0
    have hFb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖F s‖ ≤ η := by
      intro s hs
      let q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ := (⟨s,hs⟩,p.2)
      simpa only [q,F,B,U,z] using (hx q).le
    have hb := (actualPhysicalNonsingular00PairOperator_bound36V3 u (p.2 : ℝ)
      p.2.property.1 (complexRealOscillatoryPhase35 (2*x))
      (complexRealOscillatoryPhase35 (-2*x)) F
      (complexRealOscillatoryPhase_continuous35 (2*x)).continuousOn
      (complexRealOscillatoryPhase_continuous35 (-2*x)).continuousOn
      (fun s _ => complexRealOscillatoryPhase_norm35 (2*x) s)
      (fun s _ => complexRealOscillatoryPhase_norm35 (-2*x) s)
      hF η hη.le hFb (p.1 : ℝ) p.1.property).2
    have hrec := actualInteractionDyson00_phaseRecurrence35 U x (p.2 : ℝ)
      (k+1) (p.1 : ℝ)
    have hnorm : ‖genericRoughMatrixDysonTerm32 B (2*(k+1)+2)
        (p.1 : ℝ) 0 0‖ ≤ η*‖u‖^2 := by
      rw [hrec]
      exact hb
    have hfinal : η*‖u‖^2 < ε := by
      dsimp [η]
      rw [div_mul_eq_mul_div]
      have hden : 0 < ‖u‖^2+1 := by positivity
      apply (div_lt_iff₀ hden).2
      nlinarith [sq_nonneg ‖u‖]
    have h := lt_of_le_of_lt hnorm hfinal
    simpa only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] using h
end NlsGge.SpectralFoundations
end
