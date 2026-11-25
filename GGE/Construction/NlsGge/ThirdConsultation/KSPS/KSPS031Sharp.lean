import Mathlib
import NlsGge.Atomic.KSPS.KSPS031
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.Atomic.KSPS.KSPS014
import NlsGge.ThirdConsultation.KSPS.KSPS015Support
import NlsGge.ThirdConsultation.KSPS.KSPS031Phase
import NlsGge.ThirdConsultation.KSPS.KSPS031SharpCore
import NlsGge.ThirdConsultation.KSPS.KSPS031SharpRL
import NlsGge.ThirdConsultation.KSPS.KSPS031SharpEndpoints

                                                                                                                                    
                                                                                                      
                                                                                                              
                                          
                                                                                                         
                                              
                                                                                                                
                                                                                         
                                                                                                           
                                                                                               
                                                                                             
                                                                                                         
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped BigOperators
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem nonresonant_WKB_coefficients_sharp
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) :
    ∃ J : ℕ, ∃ hchart : ∀ j : ℤ, J ≤ j.natAbs →
        KSPSWKB.NonresonantBranchDomain φ j (KSPSWKB.halfNode j),
      ∀ ε : ℝ, 0 < ε → ∃ J' : ℕ,
      ∀ (j : ℤ) (hj : J' ≤ j.natAbs) (hjJ : J ≤ j.natAbs),
        ‖KSPSWKB.primitive N φ
            ⟨(j, KSPSWKB.halfNode j), hchart j hjJ⟩ +
          Complex.I * (wkbPhase φ (KSPSWKB.halfNode j) +
            Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) *
              integralRiccatiLeft φ (N + 1) *
              KSPSWKB.halfNode j ^ (-((N + 1 : ℕ) : ℤ)))‖ ≤
          ε / ‖KSPSWKB.halfNode j‖ ^ (N + 1) := by
  obtain ⟨C0, J, hC0, hcoef⟩ := nonresonant_WKB_coefficients N hN φ
  refine ⟨J, fun j hj => (hcoef j hj).choose, fun ε hε => ?_⟩
  -- the real half-node sequence
  obtain ⟨a, ha_def⟩ : ∃ a : ℤ → ℝ, a = fun j : ℤ => ((j : ℝ) + 1 / 2) * Real.pi := ⟨_, rfl⟩
  have hreal : ∀ j : ℤ, KSPSWKB.halfNode j = ((a j : ℝ) : ℂ) := by
    intro j
    rw [ha_def]
    unfold KSPSWKB.halfNode
    push_cast
    ring
  have hnorm : ∀ j : ℤ, ‖((a j : ℝ) : ℂ)‖ = |a j| := fun j => by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hne : ∀ j : ℤ, ((a j : ℝ) : ℂ) ≠ 0 := by
    intro j h
    have h1 : 1 ≤ ‖KSPSWKB.halfNode j‖ :=
      NlsGge.ThirdConsultation.KSPS031Analytic.one_le_norm_halfNode_expr j
    rw [hreal j, h, norm_zero] at h1
    norm_num at h1
  have hω : Tendsto a cofinite (Bornology.cobounded ℝ) := by
    have h := NlsGge.ThirdConsultation.KSPS031SharpRL.halfNode_tendsto 1 one_ne_zero
    rw [ha_def]
    simpa using h
  have haAbs : Tendsto (fun j => |a j|) cofinite atTop := by
    rw [ha_def]
    exact NlsGge.ThirdConsultation.KSPS031SharpRL.halfNode_abs_tendsto
  -- endpoint limits along a_j
  have h0 := KSPSWKB.diag_lower_phase_tendsto hN φ a hω hne
  have h1 := KSPSWKB.diag_upper_phase_tendsto hN φ a hω hne
  have h01 := KSPSWKB.off_upper_tendsto hN φ a hω hne
  have h10 := KSPSWKB.off_lower_tendsto hN φ a hω hne
  -- phase tail along a_j
  obtain ⟨Cφ, Jφ, hCφ, htail⟩ := wkbPhase_halfNode_tail N hN φ
  have hθev : ∀ᶠ j in cofinite,
      ‖wkbPhase φ ((a j : ℝ) : ℂ) - ((a j : ℝ) : ℂ)‖ ≤ Cφ / |a j| := by
    filter_upwards [NlsGge.ThirdConsultation.KSPS031SharpRL.eventually_cofinite_of_natAbs
      (fun j : ℤ => Jφ ≤ j.natAbs) Jφ (fun j hj => hj)] with j hj
    have h := htail j hj
    rw [hreal j, hnorm j] at h
    exact h
  -- exact trace residual, coefficient and denominator control on a tail
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ k ∈ Finset.Icc 1 N,
      NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N (sobolevNorm N φ) k :=
    ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg
      (fun k hk => KSPSWKB.endpointCoefficientBound_nonneg N (sobolevNorm N φ) k hk)
  have hthrS : NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ) = 1 + S := by
    rw [hSdef]
    rfl
  have hev : ∀ᶠ j in cofinite,
      ‖wkbPhase φ ((a j : ℝ) : ℂ) - ((a j : ℝ) : ℂ)‖ ≤ Cφ / |a j| ∧
      ‖KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0‖ ≤ S / (2 * |a j|) ∧
      ‖KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0‖ ≤ S / (2 * |a j|) ∧
      (1 - KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0 * KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0)⁻¹ *
        (1 - KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0 * KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0) = 1 ∧
      ‖(1 - KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0 * KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0)⁻¹‖ ≤ 2 ∧
      discriminant φ ((a j : ℝ) : ℂ) - 2 * Complex.cos (wkbPhase φ ((a j : ℝ) : ℂ)) =
        (1 - KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0 * KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0)⁻¹ *
          (((2 * Complex.I * ((a j : ℝ) : ℂ)) ^ N)⁻¹ *
            (KSPSWKB.sourceRemainderVector φ false ⟨((a j : ℝ) : ℂ), hne j⟩ 1 0 +
              KSPSWKB.sourceRemainderVector φ true ⟨((a j : ℝ) : ℂ), hne j⟩ 1 1 -
              KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0 *
                KSPSWKB.sourceRemainderVector φ true ⟨((a j : ℝ) : ℂ), hne j⟩ 1 0 -
              KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0 *
                KSPSWKB.sourceRemainderVector φ false ⟨((a j : ℝ) : ℂ), hne j⟩ 1 1)) := by
    filter_upwards [hθev, (tendsto_atTop.1 haAbs)
      (NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ))] with j hθj hT
    have hzT : NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ) ≤
        ‖((a j : ℝ) : ℂ)‖ := by rw [hnorm j]; exact hT
    have hzS : 1 + S ≤ |a j| := by rw [← hthrS]; exact hT
    have hz1 : 1 ≤ ‖((a j : ℝ) : ℂ)‖ := by rw [hnorm j]; linarith
    have hX0 : 0 < ‖((a j : ℝ) : ℂ)‖ := by linarith
    have hthr : WKBThreshold N (sobolevNorm N φ) ((a j : ℝ) : ℂ) := ⟨hX0, hzT⟩
    have hdet := KSPSWKB.initialColumns_det_bound N (sobolevNorm N φ) φ ((a j : ℝ) : ℂ) le_rfl hthr
    have hdetv : Matrix.det (KSPSWKB.initialColumns φ ((a j : ℝ) : ℂ)) =
        1 - KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0 * KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0 := by
      simp [KSPSWKB.initialColumns, Matrix.det_fin_two]
    rw [hdetv] at hdet
    have hD : 1 - KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0 * KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hdet
      norm_num at hdet
    have hDinv : ‖(1 - KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0 *
        KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have hpos : 0 < ‖1 - KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0 *
          KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0‖ := by linarith
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith
    have hα := KSPSWKB.endpointSum_norm_le (sobolevNorm N φ) φ le_rfl false ((a j : ℝ) : ℂ) hz1
    have hβ := KSPSWKB.endpointSum_norm_le (sobolevNorm N φ) φ le_rfl true ((a j : ℝ) : ℂ) hz1
    rw [hnorm j, ← hSdef] at hα hβ
    have hid := NlsGge.ThirdConsultation.KSPS015W.disc_identity φ ⟨((a j : ℝ) : ℂ), hne j⟩
      (fun k hk => integrated_riccati_vanishing N k φ hk)
      (WKB_monodromy_entries N (sobolevNorm N φ) φ ⟨((a j : ℝ) : ℂ), hne j⟩ le_rfl hthr).2 hD
    dsimp only at hid
    exact ⟨hθj, hα, hβ, inv_mul_cancel₀ hD, hDinv, hid⟩
  -- little-o assembly
  have hlim := NlsGge.ThirdConsultation.KSPS031SharpCore.sharp_limit N a
    (fun j => wkbPhase φ ((a j : ℝ) : ℂ)) (fun j => discriminant φ ((a j : ℝ) : ℂ))
    (fun j => (1 - KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0 * KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0)⁻¹)
    (fun j => KSPSWKB.alpha φ ((a j : ℝ) : ℂ) 0) (fun j => KSPSWKB.beta φ ((a j : ℝ) : ℂ) 0)
    (fun j => KSPSWKB.sourceRemainderVector φ false ⟨((a j : ℝ) : ℂ), hne j⟩ 1 0)
    (fun j => KSPSWKB.sourceRemainderVector φ true ⟨((a j : ℝ) : ℂ), hne j⟩ 1 1)
    (fun j => KSPSWKB.sourceRemainderVector φ true ⟨((a j : ℝ) : ℂ), hne j⟩ 1 0)
    (fun j => KSPSWKB.sourceRemainderVector φ false ⟨((a j : ℝ) : ℂ), hne j⟩ 1 1)
    (integralRiccatiLeft φ (N + 1)) S Cφ hS0 hCφ haAbs hev h0 h1 h01 h10
  have hevent := NlsGge.ThirdConsultation.KSPS031SharpCore.sharp_eventually N a
    (fun j => wkbPhase φ ((a j : ℝ) : ℂ)) (fun j => discriminant φ ((a j : ℝ) : ℂ))
    (integralRiccatiLeft φ (N + 1)) Cφ haAbs hθev hlim ε hε
  obtain ⟨J', hJ'⟩ := NlsGge.ThirdConsultation.KSPS031SharpRL.natAbs_threshold_of_eventually hevent
  refine ⟨J', fun j hj hjJ => ?_⟩
  obtain ⟨hph, hbd⟩ := hJ' j hj
  try beta_reduce at hph hbd
  rw [← hreal j] at hph hbd
  have hch := primitive_chart_error_of_phase N φ j _ ((hcoef j hjJ).choose) hph
  have hX : ‖KSPSWKB.halfNode j‖ = |a j| := by rw [hreal j, hnorm j]
  rw [hX]
  exact hch.trans hbd

end
end NlsGge.ThirdConsultation.KSPS
