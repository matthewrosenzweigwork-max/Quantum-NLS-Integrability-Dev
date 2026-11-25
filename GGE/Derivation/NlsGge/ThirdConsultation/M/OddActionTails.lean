import Mathlib
import NlsGge.ThirdConsultation.M.CarrierTails
import NlsGge.ThirdConsultation.M.OddActionSummable
import NlsGge.Atomic.G6.G6024
import NlsGge.ThirdConsultation.KSPS.KSPS032Support

/- MTAILS PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target NlsGge/ThirdConsultation/M/OddActionTails.lean,
   namespace NlsGge.ThirdConsultation.M. Pro round 16 §Q2 support `odd_higher_action_tails_of_tendsto` (head VERBATIM,
   followup14 PRO_DEFINITION_RESPONSE_FP80_16.md L439-509; no packet increment).
   Route (Pro L522-528): G6-024 (analyticity, hence continuity, of birkhoffSobolev m) turns H^m convergence of v j into
   h^m convergence of the Birkhoff sequences (coordinates physicalBirkhoff (physicalOfSobolev ·), birkhoffSobolev_coe);
   CarrierTails.uniform_tails gives one tail cutoff for this particular convergent sequence; the H1 norms of the fields are
   bounded (KSPS032S.H1Norm_le through the continuous linear cast to H1 and boundedness of a convergent sequence), so one
   high-label cutoff makes M-033 applicable to every term: 0 ≤ 4^m J_n ≤ molnarWeight² I_n = molnarWeight² |Φ_n|² ≤
   (2(1+2π)²)^m w_n |Φ_n|² (MOddSum.molnar_sq_le, G6028 action clause). Not a claim of uniform tails on a ball.
   Consumes no M-016 piece. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.M

theorem odd_higher_action_tails_of_tendsto
    (m : ℕ) (hm : 1 ≤ m)
    (v : ℕ → SobolevR m) (u : SobolevR m)
    (hv : Tendsto v atTop (𝓝 u)) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then
        ENNReal.ofReal ((4 : ℝ) ^ m *
          higherAction (physicalOfSobolev (v j)) n (2 * m + 1))
        else 0) < ENNReal.ofReal ε := by
  intro ε hε
  -- h^m convergence of the Birkhoff sequences
  have hcont : Continuous (NlsGge.GKDefinitionDesign.birkhoffSobolev m) :=
    continuousOn_univ.mp (NlsGge.GKDefinitionDesign.G6024 m hm).2.continuousOn
  set z : ℕ → SobolevCarrier38 (m : ℝ) := fun j => NlsGge.GKDefinitionDesign.birkhoffSobolev m (v j)
    with hzdef
  have hz : Tendsto z atTop (𝓝 (NlsGge.GKDefinitionDesign.birkhoffSobolev m u)) :=
    (hcont.tendsto u).comp hv
  have hcoord : ∀ (w : SobolevR m) (n : ℤ),
      carrierCoe38 (m : ℝ) (NlsGge.GKDefinitionDesign.birkhoffSobolev m w) n =
        (NlsGge.GKDefinitionDesign.physicalBirkhoff (physicalOfSobolev w) : ℤ → ℂ) n := by
    intro w n
    have h := congrArg (fun x : lp (fun _ : ℤ => ℂ) 2 => (x : ℤ → ℂ) n)
      (NlsGge.GKDefinitionDesign.birkhoffSobolev_coe m w)
    simp only at h
    rw [NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M] at h
    rw [← h]
    change _ = carrierCoe38 0 (carrierIncl38 (Nat.cast_nonneg m)
      (NlsGge.GKDefinitionDesign.birkhoffSobolev m w)) n
    rw [carrierCoe38_incl38]
  -- a common H1 cutoff
  set castL : SobolevR m →L[ℝ] SobolevR 1 :=
    ((physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm.toContinuousLinearEquiv :
        SobolevCarrier38 ((1 : ℕ) : ℝ) →L[ℝ] SobolevR 1).comp
      ((carrierIncl38 (Nat.cast_le.mpr hm : ((1 : ℕ) : ℝ) ≤ (m : ℝ))).comp
        ((physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv :
          SobolevR m →L[ℝ] SobolevCarrier38 (m : ℝ))) with hcastL
  have hcast : ∀ w : SobolevR m, lowerSobolevCast 1 m hm w = castL w := fun w => rfl
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto v hv).exists_norm_le
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR (v 0) ⟨0, rfl⟩)
  set c : ℝ := Real.sqrt (4 * (1 + 4 * Real.pi ^ 2)) with hc
  set B : ℝ := c * (‖castL‖ * R) with hB
  have hQ : ∀ j : ℕ, MTwoMode.H1Norm (lowerSobolevCast 1 m hm (v j)) ≤ B := by
    intro j
    have h1 := NlsGge.ThirdConsultation.KSPS032S.H1Norm_le (lowerSobolevCast 1 m hm (v j))
    have h2 : ‖lowerSobolevCast 1 m hm (v j)‖ ≤ ‖castL‖ * R := by
      rw [hcast]
      exact le_trans (castL.le_opNorm _) (mul_le_mul_of_nonneg_left (hR (v j) ⟨j, rfl⟩) (norm_nonneg _))
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
  set LH : ℕ := ⌈8 * B ^ 2⌉₊ + 1 with hLH
  -- uniform carrier tails
  set C : ℝ := (2 * (1 + 2 * Real.pi) ^ 2) ^ m with hC
  have hCpos : 0 < C := by positivity
  obtain ⟨LT, hLT⟩ := NlsGge.ThirdConsultation.MTails.uniform_tails (m : ℝ) z _ hz (ε / (2 * C))
    (by positivity)
  refine ⟨max LH LT, fun j => ?_⟩
  set L := max LH LT with hLdef
  set P := physicalOfSobolev (v j) with hPdef
  set u1 := lowerSobolevCast 1 m hm (v j) with hu1
  have hP : physicalOfSobolev u1 = P :=
    NlsGge.ThirdConsultation.MOddSum.physicalOfSobolev_lowerSobolevCast 1 m hm (v j)
  have hpt : ∀ n : ℤ,
      (if L ≤ n.natAbs then
        ENNReal.ofReal ((4 : ℝ) ^ m * higherAction P n (2 * m + 1)) else 0) ≤
      ENNReal.ofReal (C * (if L ≤ n.natAbs then
        sobolevModeWeight (m : ℝ) n * ‖carrierCoe38 (m : ℝ) (z j) n‖ ^ 2 else 0)) := by
    intro n
    by_cases hn : L ≤ n.natAbs
    · rw [if_pos hn, if_pos hn]
      apply ENNReal.ofReal_le_ofReal
      have hLn : LH ≤ n.natAbs := le_trans (le_max_left _ _) hn
      have hn0 : n ≠ 0 := by
        intro h; subst h; simp at hLn
      have hQ0 : 0 ≤ MTwoMode.H1Norm u1 := Real.sqrt_nonneg _
      have hQB := hQ j
      have habs : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have hLHr : (LH : ℝ) ≤ |(n : ℝ)| := by rw [← habs]; exact_mod_cast hLn
      have hceil : 8 * B ^ 2 ≤ (⌈8 * B ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      have hLHc : (LH : ℝ) = (⌈8 * B ^ 2⌉₊ : ℝ) + 1 := by rw [hLH]; push_cast; ring
      have hQ2 : MTwoMode.H1Norm u1 ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hQ0 hQB 2
      have hhigh : HighModeH1Threshold u1 n := by
        refine ⟨hn0, ?_⟩
        unfold NlsGge.Atomic.M.M054.indexWeight
        linarith
      obtain ⟨-, hhi⟩ := high_odd_action_comparison u1 n m hm hhigh
      rw [hP] at hhi
      have hI : action P n =
          ‖(NlsGge.GKDefinitionDesign.physicalBirkhoff P : ℤ → ℂ) n‖ ^ 2 :=
        (NlsGge.GKDefinitionDesign.G6028.1 P n).2.2
      rw [hI] at hhi
      have hzc : carrierCoe38 (m : ℝ) (z j) n =
          (NlsGge.GKDefinitionDesign.physicalBirkhoff P : ℤ → ℂ) n := hcoord (v j) n
      rw [hzc]
      have hw := NlsGge.ThirdConsultation.MOddSum.molnar_sq_le m n
      have hsw : sobolevModeWeight (m : ℝ) n = Real.rpow (japaneseBracket n) (2 * (m : ℝ)) := rfl
      rw [hsw]
      calc (4 : ℝ) ^ m * higherAction P n (2 * m + 1)
          ≤ molnarWeight m n ^ 2 *
              ‖(NlsGge.GKDefinitionDesign.physicalBirkhoff P : ℤ → ℂ) n‖ ^ 2 := hhi
        _ ≤ (C * Real.rpow (japaneseBracket n) (2 * (m : ℝ))) *
              ‖(NlsGge.GKDefinitionDesign.physicalBirkhoff P : ℤ → ℂ) n‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hw (sq_nonneg _)
        _ = C * (Real.rpow (japaneseBracket n) (2 * (m : ℝ)) *
              ‖(NlsGge.GKDefinitionDesign.physicalBirkhoff P : ℤ → ℂ) n‖ ^ 2) := by ring
    · rw [if_neg hn, if_neg hn, mul_zero, ENNReal.ofReal_zero]
  have hsum := (NlsGge.ThirdConsultation.MTails.summable_tail_terms (m : ℝ) L (z j)).mul_left C
  have hnn : ∀ n : ℤ, 0 ≤ C * (if L ≤ n.natAbs then
      sobolevModeWeight (m : ℝ) n * ‖carrierCoe38 (m : ℝ) (z j) n‖ ^ 2 else 0) :=
    fun n => mul_nonneg hCpos.le (NlsGge.ThirdConsultation.MTails.ite_term_nonneg _ L (z j) n)
  have hT := hLT j
  have hTanti := NlsGge.ThirdConsultation.MTails.tail_anti (m : ℝ) (le_max_right LH LT : LT ≤ L) (z j)
  have hT0 := NlsGge.ThirdConsultation.MTails.tail_nonneg (m : ℝ) L (z j)
  calc (∑' n : ℤ, if L ≤ n.natAbs then
        ENNReal.ofReal ((4 : ℝ) ^ m * higherAction P n (2 * m + 1)) else 0)
      ≤ ∑' n : ℤ, ENNReal.ofReal (C * (if L ≤ n.natAbs then
          sobolevModeWeight (m : ℝ) n * ‖carrierCoe38 (m : ℝ) (z j) n‖ ^ 2 else 0)) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (C * NlsGge.ThirdConsultation.MTails.tail (m : ℝ) L (z j)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum, tsum_mul_left]
        rfl
    _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε]
        have h1 : C * NlsGge.ThirdConsultation.MTails.tail (m : ℝ) L (z j) ≤ C * (ε / (2 * C)) :=
          mul_le_mul_of_nonneg_left (le_trans hTanti hT.le) hCpos.le
        have h2 : C * (ε / (2 * C)) = ε / 2 := by field_simp
        linarith

end NlsGge.ThirdConsultation.M
