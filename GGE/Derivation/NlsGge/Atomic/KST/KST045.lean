import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST043
import NlsGge.Atomic.KST.KST044
import NlsGge.Atomic.DM.DM047
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST045Support

/- KST-045 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST045.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-045"
   (identical in gpt6pro_followup5/7/8/9/10; no Pro round 5-12 entry touches KST-045).  No repair of the head.
   Weight hypotheses: KSTSubexponentialWeight v (full source class: v 0 >= 1, even, monotone, submultiplicative,
   log-ratio -> 0, eventually monotone log-ratio) and SlowWeight w Cw with w unbounded; not a bare class.
   Route (source Proposition 6.2(i); packet skeleton):
   (1) energy bound: rawEnergy w (F phi) < (M/2)^2 strictly (KST045S.rawEnergy_adapted_lt: KST-035 cutoff condition at
       the secondary weight 1 plus 2a+2b triangle, margin 8 ||phi||_w <= M);
   (2) norm convergence: rawEnergy (w v_eps) (F phi) -> rawEnergy w (F phi) as eps -> 0+ (KST045S.rawEnergy_cutoff_tendsto,
       Tannery on the ENNReal -> real tsum), so for small eps the half-ball condition holds; KST-043 gives SecondaryWeight
       (v_eps) for eps below a threshold;
   (3) KST-042 (KST045S.energy_of_inverse) at the secondary weight v_delta gives finite (w v_delta)-energy of phi;
   (4) KST-044 (truncated_secondary_weight_eq_product_off_finite): w v_delta = w v off a finite set, so the (w v)-energy
       is finite too (KST045S.weightedNormSq₂_lt_top_of_eventually_eq). -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST001 NlsGge.Atomic.KST002 NlsGge.Pilot
open NlsGge.Atomic.KST043 (KSTSubexponentialWeight)

namespace NlsGge.ThirdConsultation.KST

theorem kst045 (w v : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (hv : KSTSubexponentialWeight v) (φ : Potential)
    (hφ : weightedNormSq₂ w (periodicPair φ) < ⊤)
    (hmargin : 8*Real.sqrt (weightedNormSq₂ w (periodicPair φ)).toReal ≤ M)
    (hF : rawEnergy (productWeight w v)
      (adaptedCoefficients (adaptedThreshold w M) φ) < ⊤) :
  (∃ δ : ℝ, 0 < δ ∧
    SecondaryWeight (NlsGge.Atomic.DM047.secondaryCutoff v δ) ∧
    rawEnergy (productWeight w (NlsGge.Atomic.DM047.secondaryCutoff v δ))
      (adaptedCoefficients (adaptedThreshold w M) φ) ≤
        ENNReal.ofReal ((M/2)^2)) ∧
  weightedNormSq₂ (productWeight w v) (periodicPair φ) < ⊤ := by
  have hv1 : ∀ k, 1 ≤ v k := NlsGge.Atomic.KST044.subexponentialWeight_ge_one v hv
  obtain ⟨ε₀, hε₀, hsub⟩ := NlsGge.Atomic.KST043.min_exp_subexp_submultiplicative hv
  have hlim := KST045S.rawEnergy_cutoff_tendsto w v hv1
    (adaptedCoefficients (adaptedThreshold w M) φ) hF.ne
  have hlt := KST045S.rawEnergy_adapted_lt w Cw M hM hw hunbounded φ hφ hmargin
  have hev := hlim.eventually (gt_mem_nhds hlt)
  have hIoo : Set.Ioo (0 : ℝ) ε₀ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT hε₀
  obtain ⟨δ, hδE, hδI⟩ := (hev.and (show ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
    ε ∈ Set.Ioo (0 : ℝ) ε₀ from hIoo)).exists
  have hδ : 0 < δ := hδI.1
  have hveven : ∀ k : ℤ, v (-k) = v k := hv.2.1
  have hvnat : ∀ k : ℤ, v k = v (k.natAbs : ℤ) := by
    intro k
    rcases Int.natAbs_eq k with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      exact hveven _
  have hsec : SecondaryWeight (NlsGge.Atomic.DM047.secondaryCutoff v δ) := by
    refine ⟨⟨fun k => NlsGge.Atomic.KST044.secondaryCutoff_ge_one v hv δ hδ.le k,
      fun k => ?_, fun j k hjk => ?_⟩, hsub δ hδI⟩
    · unfold NlsGge.Atomic.DM047.secondaryCutoff
      rw [Int.natAbs_neg, hveven k]
    · unfold NlsGge.Atomic.DM047.secondaryCutoff
      refine min_le_min (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Nat.cast_le.2 hjk) hδ.le)) ?_
      rw [hvnat j, hvnat k]
      exact hv.2.2.1 hjk
  refine ⟨⟨δ, hδ, hsec, hδE.le⟩, ?_⟩
  have hfinδ := KST045S.energy_of_inverse w Cw M hM hw hunbounded _ hsec φ hφ hmargin hδE.le
  obtain ⟨N, hN⟩ := NlsGge.Atomic.KST044.truncated_secondary_weight_eq_product_off_finite
    w v (fun k => lt_of_lt_of_le zero_lt_one (hw.one_le k)) hv hδ
  exact KST045S.weightedNormSq₂_lt_top_of_eventually_eq _ _ _ N
    (fun k hk => (hN k hk).symm) hfinδ

end NlsGge.ThirdConsultation.KST
end
