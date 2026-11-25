import NlsGge.Ramer.General.RamerSettingMeasure
import NlsGge.Ramer.General.CameronMartinScaling

/-!
# Cameron–Martin over a `RamerSetting` (G2 goal 7)

Thin wrappers around `exists_cm_shift_positiveScoreDensity`, transported to `S.E` through the
realization `S.R` (signs as in `NlsGge.Ramer.map_add_inclE_eq_withDensity`: the `+` translation
has density `exp (S_h - ‖h‖²/2)`, where `S_h` is the `L²`-limit of the finite scores).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
open NlsGge.Pilot NlsGge.Measure

namespace NlsGge.Ramer.General

namespace RamerSetting

variable (S : RamerSetting)

theorem hcoord_eq_wCoord (h : S.H) : S.hcoord h = wCoord h := rfl

theorem map_add_incl_eq_withDensity (h : S.H) :
    ∃ Sc : Lp ℝ 2 S.γ,
      Tendsto (fun N : ℕ => cmScoreLp S.q (S.hcoord h) N) atTop (𝓝 Sc) ∧
      S.γE.map (fun x => x + S.incl h) =
        S.γE.withDensity (fun x => ENNReal.ofReal
          (Real.exp (Sc (S.coordE x) - ‖h‖ ^ 2 / 2))) := by
  obtain ⟨Sc, hS, -, -, hmap⟩ := exists_cm_shift_positiveScoreDensity S.q S.q_pos h
  refine ⟨Sc, hS, ?_⟩
  have hQ : ‖h‖ ^ 2 = ∑' n : ℤ, 2 * S.q n * ‖wCoord h n‖ ^ 2 := wCoord_norm_sq h
  rw [← hQ] at hmap
  have hScm : Measurable (Sc : (ℤ → ℂ) → ℝ) := (Lp.stronglyMeasurable Sc).measurable
  set D : (ℤ → ℂ) → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (Sc z - ‖h‖ ^ 2 / 2)) with hD
  have hDm : Measurable D := by
    simp only [hD]
    exact (Real.measurable_exp.comp (hScm.sub_const _)).ennreal_ofReal
  have hτ : Measurable (fun x : S.E => x + S.incl h) := measurable_id.add_const _
  have hsh : Measurable (fun z : ℤ → ℂ => fun n => z n + wCoord h n) :=
    Measurable.of_eval (fun n => (measurable_pi_apply n).add measurable_const)
  refine Measure.ext fun A hA => ?_
  have hRA : MeasurableSet (S.R ⁻¹' A) := S.measurable_R hA
  have hL : S.γE.map (fun x => x + S.incl h) A =
      (S.γ.map (fun z : ℤ → ℂ => fun n => z n + wCoord h n)) (S.R ⁻¹' A) := by
    rw [Measure.map_apply hτ hA, Measure.map_apply hsh hRA]
    show (S.γ.map S.R) _ = _
    rw [Measure.map_apply S.measurable_R (hτ hA)]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [S.ae_memE] with z hz
    have : S.R (fun n => z n + wCoord h n) = S.R z + S.incl h := S.R_add hz h
    simp only [Set.mem_preimage, this]
  rw [hL]
  have hmap' : S.γ.map (fun z : ℤ → ℂ => fun n => z n + wCoord h n) = S.γ.withDensity D := hmap
  rw [hmap', withDensity_apply _ hRA, withDensity_apply _ hA]
  refine Eq.trans ?_ (setLIntegral_map (μ := S.γ) hA (hDm.comp S.measurable_coordE)
    S.measurable_R).symm
  refine setLIntegral_congr_fun_ae hRA ?_
  filter_upwards [S.coordE_R_ae] with z hz _
  show D z = D (S.coordE (S.R z))
  rw [hz]

theorem quasiMeasurePreserving_add_incl (h : S.H) :
    Measure.QuasiMeasurePreserving (fun x : S.E => x + S.incl h) S.γE S.γE := by
  obtain ⟨Sc, -, hmap⟩ := S.map_add_incl_eq_withDensity h
  exact ⟨measurable_id.add_const _, by rw [hmap]; exact withDensity_absolutelyContinuous _ _⟩

end RamerSetting

end NlsGge.Ramer.General

