import NlsGge.GK38.TauGammaAnalyticMoments
import NlsGge.GK38.TauGammaCriticalTails
import NlsGge.GK38.TauGammaValueProbe
import NlsGge.GK38.TauGammaExterior
import NlsGge.GK38.Lib.EntireProductsC34a

/-! Actual canonical critical tails, nonconstant real open-gap data and the zero-mode exterior normalization. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem periodicPlusDeviation_free38 : periodicPlusDeviation38 0 = 0 := by
  apply Subtype.ext
  funext n
  change l2SequenceOf38 (fun m => lamPlus 0 m - (m : ℂ) * (Real.pi : ℂ)) n = 0
  rw [l2SequenceOf_apply38 _ (periodic_plus_summable38 0)]
  simp [lamPlus_zero38, countingCenter38]

theorem periodicMinusDeviation_free38 : periodicMinusDeviation38 0 = 0 := by
  apply Subtype.ext
  funext n
  change l2SequenceOf38 (fun m => lamMinus 0 m - (m : ℂ) * (Real.pi : ℂ)) n = 0
  rw [l2SequenceOf_apply38 _ (periodic_minus_summable38 0)]
  simp [lamMinus_zero38, countingCenter38]

theorem tauGamma_probe_free_exterior_zero_mode38 : exteriorFactor38 0 0 0 = 1 := by
  rw [exterior_eq_omitProducts38, periodicPlusDeviation_free38, periodicMinusDeviation_free38]
  have h := Lib.omitProd_zero_at_root 0
  norm_num at h
  rw [h]
  norm_num

theorem tauGamma_probe_free_exterior_negative38 : exteriorFactor38 0 (-1) (-(Real.pi : ℂ)) = 1 := by
  rw [exterior_eq_omitProducts38, periodicPlusDeviation_free38, periodicMinusDeviation_free38]
  have h := Lib.omitProd_zero_at_root (-1)
  norm_num at h
  rw [h]
  norm_num

theorem tauGamma_probe_actual_critical_quarter_tail38 :
    ∃ V : Set PotPair, V ∈ 𝓝 (realSlice (constL2 1)) ∧ V ⊆ gkW ∧ ∃ N : ℕ,
      ∀ φ ∈ V, ∀ n : ℤ, (N : ℤ) < |n| →
        ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 8 :=
  critical_uniform_tail38 _ (realSlice_mem_gkW (constL2 1)) _ (by positivity)

theorem tauGamma_probe_nonfree_exterior_at_periodic_root38 :
    exteriorFactor38 (realSlice (constL2 1)) 0 1 ≠ 0 ∧
      exteriorFactor38 (realSlice (constL2 1)) 0 (-1) ≠ 0 := by
  have hw := realSlice_mem_gkW (constL2 1)
  have hf := isolating_family38 _ hw
  obtain ⟨c, N, hg, hs⟩ := hf
  have hp := (hs.1 0).1 (right_mem_segment ℝ _ _)
  have hm := (hs.1 0).1 (left_mem_segment ℝ _ _)
  rw [realType_const_central_labels38.2] at hp
  rw [realType_const_central_labels38.1] at hm
  exact ⟨exterior_nonzero_in_disc38 _ _ _ ⟨c, N, hg, hs⟩ 0 1 hp,
    exterior_nonzero_in_disc38 _ _ _ ⟨c, N, hg, hs⟩ 0 (-1) hm⟩

end
end NlsGge.GK38
