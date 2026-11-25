import Mathlib
import NlsGge.Atomic.KSN.KSN017Core
import NlsGge.Atomic.KSN.KSN013Asm
import NlsGge.Atomic.KSN.KSN012Sup3
import NlsGge.Atomic.KSN.KSN012Sup6
import NlsGge.ThirdConsultation.KSPS.KSPS025Host

                                                                                              
                                                                                                                  
                                                          
                                                                                                                
                                                                      
                                                                                                                
                                                                                           
                                                                                                         
                                                                                                                      
                                                                                                       
                                                                                                                       
                                                                                                                   
                                                                                              
set_option autoImplicit false

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem ksn017_natAbs_le_indexWeight (n : ℤ) :
    (n.natAbs : ℝ) ≤ NlsGge.ThirdConsultation.KSPS.indexWeight n := by
  unfold NlsGge.ThirdConsultation.KSPS.indexWeight
  rw [NlsGge.Atomic.KSN016.natAbs_cast, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- midpoint = tauN on gkW (Pro round 15 Q2), for the B3 carrier. -/
theorem ksn017_tau_eq_midpoint (x : PairScale 1) (hW : pairPotential 1 (by norm_num) x ∈ gkW) (k : ℤ) :
    tauN (pairPotential 1 (by norm_num) x) k =
      NlsGge.ThirdConsultation.KSPS.midpoint (toSobolevC x) k := by
  rw [tauN_value38 _ hW k]
  unfold NlsGge.ThirdConsultation.KSPS.midpoint NlsGge.ThirdConsultation.KSPS.periodicMinus
    NlsGge.ThirdConsultation.KSPS.periodicPlus
  rw [toPotPair_toSobolevC]
  ring

theorem ksn017_mu_eq (x : PairScale 1) (n : ℤ) :
    NlsGge.ThirdConsultation.KSPS.mu (toSobolevC x) n = muSeq (pairPotential 1 (by norm_num) x) n := by
  unfold NlsGge.ThirdConsultation.KSPS.mu
  rw [toPotPair_toSobolevC]

theorem ksn017_g_continuousOn (n : ℤ) :
    ContinuousOn (fun φ : PotPair => (deltaFactor n φ (muSeq φ n))⁻¹) sourceBetaW :=
  ((KSN002_main n).1.continuousOn).inv₀ (fun φ hφ => ((KSN002_main n).2 φ hφ).2.1)

/-- Combining the large-label estimate with a bound for the finitely many small labels. -/
theorem ksn017_finish (N : ℕ) (hN : 1 ≤ N) (C₀ Mb : ℝ) (hC₀ : 0 ≤ C₀) (hMb : 0 ≤ Mb) (n : ℤ) (g : ℂ)
    (hbig : N ≤ n.natAbs → ‖g - (-1 : ℂ) ^ n‖ ≤ C₀ / (n.natAbs : ℝ))
    (hsmall : n.natAbs < N → ‖g‖ ≤ Mb) :
    ‖g - (-1 : ℂ) ^ n‖ ≤ (C₀ + (Mb + 1) * N) / bracket n := by
  have hbp := ksn013_bracket_pos n
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hextra : 0 ≤ (Mb + 1) * N := by positivity
  by_cases h : N ≤ n.natAbs
  · have hn1 : (1 : ℝ) ≤ (n.natAbs : ℝ) := hN1.trans (by exact_mod_cast h)
    have hb : bracket n = (n.natAbs : ℝ) := by unfold bracket; exact max_eq_right hn1
    refine (hbig h).trans ?_
    rw [hb]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · push_neg at h
    have hb : bracket n ≤ N := by
      unfold bracket
      exact max_le hN1 (by exact_mod_cast h.le)
    have h1 : ‖g - (-1 : ℂ) ^ n‖ ≤ Mb + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [ksn017_neg_one_zpow_norm]
      linarith [hsmall h]
    refine h1.trans ?_
    rw [le_div_iff₀ hbp]
    have : (Mb + 1) * bracket n ≤ (Mb + 1) * N := mul_le_mul_of_nonneg_left hb (by linarith)
    linarith

/-- Local data around a point of sourceBetaW, for every H¹ bound, for the large labels. -/
theorem ksn017_local_data
    (hgap : ∀ H : ℝ, 0 ≤ H → ∃ (N : ℕ) (Γ : ℝ), ∀ x : PairScale 1, ‖x‖ ≤ H →
      pairPotential 1 (by norm_num) x ∈ gkW → ∀ k : ℤ, N ≤ k.natAbs →
        japaneseBracket k ^ 2 * ‖gamma2 (pairPotential 1 (by norm_num) x) k‖ ≤ Γ)
    (hmidU : ∀ (B₀ : ℝ) (hB₀ : 0 ≤ B₀),
      ∃ B : ℝ, 0 < B ∧
        ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1,
          NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 φ ≤ B₀ →
          ‖NlsGge.ThirdConsultation.KSPS.massCoefficient φ‖ ≤ B ∧
          ∀ k : ℤ, k ≠ 0 →
            ‖NlsGge.ThirdConsultation.KSPS.midpoint φ k - (k : ℂ) * Real.pi -
              NlsGge.ThirdConsultation.KSPS.massCoefficient φ / (k : ℂ)‖ ≤
                B / (k.natAbs : ℝ)^2)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
    ∃ O : Set PotPair, IsOpen O ∧ φ₀ ∈ O ∧ O ⊆ sourceBetaW ∧
      ∀ H : ℝ, 0 ≤ H → ∃ (N₀ : ℕ) (C₀ : ℝ), 1 ≤ N₀ ∧ 0 ≤ C₀ ∧
        ∀ x : PairScale 1, ‖x‖ ≤ H → pairPotential 1 (by norm_num) x ∈ O →
          ∀ n : ℤ, N₀ ≤ n.natAbs →
            ‖(deltaFactor n (pairPotential 1 (by norm_num) x)
                (muSeq (pairPotential 1 (by norm_num) x) n))⁻¹ - (-1 : ℂ) ^ n‖ ≤
              C₀ / (n.natAbs : ℝ) := by
  obtain ⟨O, hOo, hφO, hOsub, C, R, c, J, hgeom, hspec, hbd⟩ := ksn013_local_bounds hgap φ₀ hφ₀
  refine ⟨O, hOo, hφO, hOsub, fun H hH => ?_⟩
  obtain ⟨Aa, Γ, hbx⟩ := hbd H hH
  obtain ⟨Bmid, hBmid, hmidb⟩ := hmidU (2 * H + 1) (by positivity)
  obtain ⟨aμ, haμ, hloc⟩ := NlsGge.ThirdConsultation.KSN012U.sup6_unif_loc (2 * H + 1) (by positivity)
  obtain ⟨N₀, C₀, hN1, hC0, hcore⟩ := ksn017_core C R c J hgeom Aa Γ (Bmid + aμ)
  refine ⟨N₀, C₀, hN1, hC0, fun x hx hxO n hn => ?_⟩
  have hW : pairPotential 1 (by norm_num) x ∈ gkW := ksn013_sourceBetaW_gkW (hOsub hxO)
  have hsob : NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 (toSobolevC x) ≤ 2 * H + 1 :=
    (sobolevNorm_toSobolevC_le x).trans (by linarith)
  obtain ⟨hmass, hmid⟩ := hmidb (toSobolevC x) hsob
  obtain ⟨ha, hΓ⟩ := hbx x hx hxO
  have hmid' : ∀ k : ℤ, k ≠ 0 →
      ‖tauN (pairPotential 1 (by norm_num) x) k - (k : ℂ) * Real.pi -
        NlsGge.ThirdConsultation.KSPS.massCoefficient (toSobolevC x) / (k : ℂ)‖ ≤
          (Bmid + aμ) / (k.natAbs : ℝ) ^ 2 := by
    intro k hk
    rw [ksn017_tau_eq_midpoint x hW k]
    have hk2 : (0 : ℝ) < (k.natAbs : ℝ) ^ 2 := by
      have : (0 : ℝ) < (k.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hk
      positivity
    exact (hmid k hk).trans (div_le_div_of_nonneg_right (by linarith) hk2.le)
  have hmu' : ∀ j : ℤ, j ≠ 0 →
      ‖muSeq (pairPotential 1 (by norm_num) x) j - (j : ℂ) * Real.pi‖ ≤
        (Bmid + aμ) / (j.natAbs : ℝ) := by
    intro j hj
    have hjp : (0 : ℝ) < (j.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hj
    have h1 := (hloc (toSobolevC x) hsob j).1
    rw [ksn017_mu_eq] at h1
    refine h1.trans ?_
    calc aμ / NlsGge.ThirdConsultation.KSPS.indexWeight j ≤ aμ / (j.natAbs : ℝ) :=
          div_le_div_of_nonneg_left haμ hjp (ksn017_natAbs_le_indexWeight j)
      _ ≤ (Bmid + aμ) / (j.natAbs : ℝ) := div_le_div_of_nonneg_right (by linarith) hjp.le
  exact (hcore _ hW (hspec _ hxO) ha hΓ _ (hmass.trans (by linarith)) hmid' hmu' n hn
    ((KSN002_main n).2 _ (hOsub hxO)).1).2

/-- The KSN-017 head, conditional only on the landed M-032 conclusion and Pro's uniform midpoint producer. -/
theorem KSN017_of
    (hM032 : ∀ (w : ℤ → ℝ), NlsGge.ThirdConsultation.M.OneDerivativeWeight w → ∀ (N : ℕ) (φ : PotPair),
      φ ∈ gkW → NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤ →
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight (N : ℤ) →
      NlsGge.ThirdConsultation.MTwoMode.complexGapTailEnergy w φ N ≤
        6 * NlsGge.ThirdConsultation.MTwoMode.potentialTailEnergy w φ N +
        ENNReal.ofReal (1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 6 /
          NlsGge.Atomic.M.M054.indexWeight (N : ℤ)))
    (hmidU : ∀ (B₀ : ℝ) (hB₀ : 0 ≤ B₀),
      ∃ B : ℝ, 0 < B ∧
        ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1,
          NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 φ ≤ B₀ →
          ‖NlsGge.ThirdConsultation.KSPS.massCoefficient φ‖ ≤ B ∧
          ∀ k : ℤ, k ≠ 0 →
            ‖NlsGge.ThirdConsultation.KSPS.midpoint φ k - (k : ℂ) * Real.pi -
              NlsGge.ThirdConsultation.KSPS.massCoefficient φ / (k : ℂ)‖ ≤
                B / (k.natAbs : ℝ)^2) :
  (∀ x₀ ∈ complexDomain 1 (by norm_num),
    ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
      ∀ x ∈ U, ∀ n : ℤ,
        deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n) ≠ 0 ∧
        ‖(deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n))⁻¹ - (-1 : ℂ)^n‖ ≤ C / bracket n) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
      deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n) ≠ 0 ∧
        ‖(deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n))⁻¹ - (-1 : ℂ)^n‖ ≤ C / bracket n) := by
  have hgap := ksn013_gap_high hM032
  have hVopen : IsOpen sourceBetaW := sourceFamily.V_open
  constructor
  · intro x₀ hx₀
    obtain ⟨O, hOo, hφO, hOsub, hdat⟩ := ksn017_local_data hgap hmidU _ hx₀
    obtain ⟨N₀, C₀, hN1, hC0, hest⟩ := hdat (‖x₀‖ + 1) (by positivity)
    set φ₀ := pairPotential 1 (by norm_num) x₀ with hφ₀
    set F : Finset ℤ := Finset.Ioo (-(N₀ : ℤ)) N₀ with hF
    set V : Set PotPair := ⋂ n ∈ F, (sourceBetaW ∩
      (fun φ : PotPair => ‖(deltaFactor n φ (muSeq φ n))⁻¹‖) ⁻¹'
        Iio (‖(deltaFactor n φ₀ (muSeq φ₀ n))⁻¹‖ + 1)) with hV
    have hVo : IsOpen V := isOpen_biInter_finset (fun n _ =>
      (ksn017_g_continuousOn n).norm.isOpen_inter_preimage hVopen isOpen_Iio)
    have hφV : φ₀ ∈ V := by
      rw [hV, mem_iInter₂]
      intro n _
      exact ⟨hx₀, by simp⟩
    set Mb : ℝ := ∑ n ∈ F, (‖(deltaFactor n φ₀ (muSeq φ₀ n))⁻¹‖ + 1) with hMb
    have hMb0 : 0 ≤ Mb := Finset.sum_nonneg (fun n _ => by positivity)
    refine ⟨pairPotential 1 (by norm_num) ⁻¹' (O ∩ V) ∩ ball x₀ 1, C₀ + (Mb + 1) * N₀,
      ((hOo.inter hVo).preimage KSN012B2_main).inter isOpen_ball, ⟨⟨hφO, hφV⟩, mem_ball_self one_pos⟩,
      fun x hx => hOsub hx.1.1, by positivity, ?_⟩
    intro x hx n
    have hxS := hOsub hx.1.1
    refine ⟨((KSN002_main n).2 _ hxS).2.1, ?_⟩
    have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have h1 := norm_sub_norm_le x x₀
      have h2 := mem_ball_iff_norm.mp hx.2
      linarith
    refine ksn017_finish N₀ hN1 C₀ Mb hC0 hMb0 n _ (fun h => hest x hxn hx.1.1 n h) (fun h => ?_)
    have hnF : n ∈ F := by rw [hF, Finset.mem_Ioo]; omega
    have hxV := hx.1.2
    rw [hV, mem_iInter₂] at hxV
    have h1 := (hxV n hnF).2
    simp only [mem_preimage, mem_Iio] at h1
    refine h1.le.trans ?_
    exact Finset.single_le_sum (f := fun n => ‖(deltaFactor n φ₀ (muSeq φ₀ n))⁻¹‖ + 1)
      (fun n _ => by positivity) hnF
  · intro B hB
    obtain ⟨Kc, hK, hKsub, hKmem⟩ := ksn013_realBall_compact B hB
    have hloc := fun φ : Kc => ksn017_local_data hgap hmidU φ.1 (hKsub φ.2)
    choose O hOo hφO hOsub hdat using hloc
    choose N₀ C₀ hN1 hC0 hest using fun φ : Kc => hdat φ B hB
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun φ : Kc => O φ) hOo
      (fun φ hφ => mem_iUnion.mpr ⟨⟨φ, hφ⟩, hφO _⟩)
    set Nm : ℕ := t.sup N₀ + 1 with hNm
    set F : Finset ℤ := Finset.Ioo (-(Nm : ℤ)) Nm with hF
    have hbnd : ∀ n : ℤ, ∃ Mn : ℝ, ∀ φ ∈ Kc, ‖(deltaFactor n φ (muSeq φ n))⁻¹‖ ≤ Mn := fun n =>
      hK.exists_bound_of_continuousOn ((ksn017_g_continuousOn n).mono hKsub)
    choose Mn hMn using hbnd
    set Mb : ℝ := ∑ n ∈ F, max (Mn n) 0 with hMb
    have hMb0 : 0 ≤ Mb := Finset.sum_nonneg (fun n _ => le_max_right _ _)
    set CC : ℝ := ∑ φ ∈ t, C₀ φ with hCC
    have hCC0 : 0 ≤ CC := Finset.sum_nonneg (fun φ _ => hC0 φ)
    refine ⟨CC + (Mb + 1) * Nm, by positivity, ?_⟩
    intro x hxr hx n
    have hxK := hKmem x hxr hx
    refine ⟨((KSN002_main n).2 _ (hKsub hxK)).2.1, ?_⟩
    have hmem := ht hxK
    rw [mem_iUnion₂] at hmem
    obtain ⟨φ, hφt, hφx⟩ := hmem
    refine ksn017_finish Nm (by omega) CC Mb hCC0 hMb0 n _ (fun h => ?_) (fun h => ?_)
    · have hle : N₀ φ ≤ n.natAbs := (Finset.le_sup (f := N₀) hφt).trans (by omega)
      refine (hest φ x hx hφx n hle).trans ?_
      have hnp : (0 : ℝ) ≤ (n.natAbs : ℝ) := Nat.cast_nonneg _
      exact div_le_div_of_nonneg_right
        (Finset.single_le_sum (fun φ _ => hC0 φ) hφt) hnp
    · have hnF : n ∈ F := by rw [hF, Finset.mem_Ioo]; omega
      refine (hMn n _ hxK).trans ((le_max_left (Mn n) 0).trans ?_)
      exact Finset.single_le_sum (f := fun n => max (Mn n) 0) (fun n _ => le_max_right _ _) hnF

end
end NlsGge.ThirdConsultation.KSN
