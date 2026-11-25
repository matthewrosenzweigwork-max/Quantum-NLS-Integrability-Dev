import Mathlib
import NlsGge.Atomic.I.I017Core
import NlsGge.Atomic.I.I019
import NlsGge.ThirdConsultation.I.LimitLaws
import NlsGge.Birkhoff.S03Measure38c

/- I-023/I-024 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORT (no packet increment).
   Target NlsGge/Atomic/I/I023Core.lean, namespace NlsGge.ThirdConsultation.I023C.
   Pro's I-023 / I-024 route (v2 proof of A:lem:remainderconvergence, A:eq:remainderconvergence;
   Birkhoff/S03Measure38c.lean): for ANY house record Bk : BirkhoffTop38 whose cleaned inverse is the I inverse on all
   sequences (hB; discharged in the glue by actual_inverse_eq_physicalOfSequence for PDE.actualBirkhoffTop38), the
   literal I-023 and I-024 conclusions hold.
   I-023: the steps of the landed house proof remainder_tendsto_pathwise38, exposed: actions (action_cleanΦinv38),
   termwise convergence (tendsto_gapIntegral_proj38 + eventually-constant actions), and the common majorant
   C·a_n·|z_n|²·⟨n⟩^{-3/2} with C = CB of remainderSummand_dominated38 at the exhaustion's H¹ bound exists_H1_bound38
   (C depends on z and Λ, never on n or N).  remainderSummand38 = gapRemainderTermE02_38 (weight c) by
   remainderSummand38_eq_gapRemainderTerm.
   I-024: summability from the I-023 majorant; nonnegativity, finite-cutoff nonnegativity and convergence from
   remainder_tendsto_pathwise38 (the limit's nonnegativity via the standard exhaustion [-N,N]); the max in
   sequenceRemainder is inactive since the remainder is ≥ 0. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I023C

theorem tail_eq (c : ℕ → ℝ) (C : ℝ) (z : ℤ → ℂ) (n : ℤ) :
    C * (tailWeight38 c n * ‖z n‖ ^ 2) =
      C * fullWeightRate c n * ‖z n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) := by
  unfold tailWeight38
  have e : (-3 / 2 : ℝ) = -(3 / 2) := by norm_num
  rw [e]; ring

theorem stdExh_isExhaustion : IsExhaustion38 (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) :=
  ⟨fun a b hab => Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hab),
    fun n => ⟨n.natAbs, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩⟩

/-- I-023 with the inverse written as the house cleaned inverse. -/
theorem i023_house (Bk : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)
    (z : ℤ → ℂ) (hz : z ∈ Omega038 c) (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    (∀ n : ℤ, actualGapActionAllE02_38 (Bk.cleanΦinv z) n = ‖z n‖ ^ 2 ∧
      (∀ N : ℕ, actualGapActionAllE02_38 (Bk.cleanΦinv (projFin38 (Λ N) z)) n =
        if n ∈ Λ N then ‖z n‖ ^ 2 else 0) ∧
      Tendsto (fun N : ℕ => gapRemainderTermE02_38 (weight c) (Bk.cleanΦinv (projFin38 (Λ N) z)) n)
        atTop (𝓝 (gapRemainderTermE02_38 (weight c) (Bk.cleanΦinv z) n))) ∧
    ∃ C : ℝ, 0 ≤ C ∧
      Summable (fun n : ℤ => C * fullWeightRate c n * ‖z n‖ ^ 2 *
        japaneseBracket n ^ (-3 / 2 : ℝ)) ∧
      ∀ n : ℤ,
        |gapRemainderTermE02_38 (weight c) (Bk.cleanΦinv z) n| ≤
          C * fullWeightRate c n * ‖z n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) ∧
        ∀ N : ℕ, |gapRemainderTermE02_38 (weight c) (Bk.cleanΦinv (projFin38 (Λ N) z)) n| ≤
          C * fullWeightRate c n * ‖z n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) := by
  have hW := weight_continuous38 hlower hbound hupper
  have hz1 : z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := BirkhoffTop38.mem_seqSobolev38_of_Omega038 c hz 1
  have hP : ∀ N : ℕ, projFin38 (Λ N) z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := fun N =>
    finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (Λ N) z)
  have hR : ∀ (u : PhysicalL2) (n : ℤ), gapRemainderTermE02_38 (weight c) u n = remainderSummand38 c u n :=
    fun u n => (remainderSummand38_eq_gapRemainderTerm c hW u n).symm
  have hactN : ∀ (N : ℕ) (n : ℤ), actualGapActionAllE02_38 (Bk.cleanΦinv (projFin38 (Λ N) z)) n =
      if n ∈ Λ N then ‖z n‖ ^ 2 else 0 := by
    intro N n
    rw [Bk.action_cleanΦinv38 _ (hP N) n]
    by_cases hn : n ∈ Λ N
    · rw [projFin38_apply_of_mem hn]; simp only [hn, ↓reduceIte]
    · rw [projFin38_apply_of_not_mem hn]; simp only [hn, ↓reduceIte, norm_zero]; norm_num
  obtain ⟨Bd, hBd1, hBdN, hBdz⟩ := Bk.exists_H1_bound38 z hz1 hΛ
  obtain ⟨CB, hCB, hdom⟩ := Bk.remainderSummand_dominated38 lower upper c hlower hbound hupper Bd hBd1
  refine ⟨fun n => ⟨Bk.action_cleanΦinv38 z hz1 n, fun N => hactN N n, ?_⟩, CB, hCB.le, ?_, fun n => ⟨?_, fun N => ?_⟩⟩
  · simp only [hR]
    have hg := Bk.tendsto_gapIntegral_proj38 c hW z hz1 hΛ n
    have hI : ∀ᶠ N in atTop, actualGapActionAllE02_38 (Bk.cleanΦinv (projFin38 (Λ N) z)) n =
        actualGapActionAllE02_38 (Bk.cleanΦinv z) n := by
      filter_upwards [hΛ.eventually_mem n] with N hN
      rw [Bk.action_cleanΦinv38 _ (hP N), Bk.action_cleanΦinv38 _ hz1, projFin38_apply_of_mem hN]
    have hI' : Tendsto (fun N : ℕ => actualGapActionAllE02_38 (Bk.cleanΦinv (projFin38 (Λ N) z)) n)
        atTop (𝓝 (actualGapActionAllE02_38 (Bk.cleanΦinv z) n)) :=
      tendsto_const_nhds.congr' (hI.mono fun N hN => hN.symm)
    exact hg.sub (hI'.const_mul (fullWeightRate c n))
  · exact (hz.2.mul_left CB).congr (fun n => tail_eq c CB z n)
  · rw [hR, ← tail_eq]
    exact hdom z hz1 (fun h => hBdz h) n
  · rw [hR, ← tail_eq]
    refine (hdom _ (hP N) (fun h => hBdN N h) n).trans ?_
    have hw := tailWeight38_nonneg lower upper c hlower hbound hupper n
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hw) hCB.le
    by_cases hn : n ∈ Λ N
    · rw [projFin38_apply_of_mem hn]
    · rw [projFin38_apply_of_not_mem hn, norm_zero]
      simp

theorem i023_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (z : ℤ → ℂ) (hz : z ∈ goodGaussianSet c.val)
    (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    let u := physicalOfSequence z
    let uN := fun N : ℕ => physicalOfSequence (projFin38 (Λ N) z)
    (∀ n : ℤ, actualGapActionAllE02_38 u n = ‖z n‖ ^ 2 ∧
      (∀ N : ℕ, actualGapActionAllE02_38 (uN N) n =
        if n ∈ Λ N then ‖z n‖ ^ 2 else 0) ∧
      Tendsto (fun N : ℕ => gapRemainderTermE02_38 (weight c.val) (uN N) n)
        atTop (𝓝 (gapRemainderTermE02_38 (weight c.val) u n))) ∧
    ∃ C : ℝ, 0 ≤ C ∧
      Summable (fun n : ℤ => C * fullWeightRate c.val n * ‖z n‖ ^ 2 *
        japaneseBracket n ^ (-3 / 2 : ℝ)) ∧
      ∀ n : ℤ,
        |gapRemainderTermE02_38 (weight c.val) u n| ≤
          C * fullWeightRate c.val n * ‖z n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) ∧
        ∀ N : ℕ, |gapRemainderTermE02_38 (weight c.val) (uN N) n| ≤
          C * fullWeightRate c.val n * ‖z n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have h := i023_house Bk lower upper c.val hl hb' hu' z hz Λ hΛ
  simp only [hB] at h
  exact h

theorem i024_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ∀ z ∈ goodGaussianSet c.val,
      Summable (fun n : ℤ =>
        |gapRemainderTermE02_38 (weight c.val) (physicalOfSequence z) n|) ∧
      0 ≤ remainderForWeight (weight c.val) (physicalOfSequence z) ∧
      sequenceRemainder (weight c.val) z = remainderForWeight (weight c.val) (physicalOfSequence z) ∧
      ∀ Λ : ℕ → Finset ℤ, IsExhaustion38 Λ →
        (∀ N : ℕ, 0 ≤ remainderForWeight (weight c.val)
          (physicalOfSequence (projFin38 (Λ N) z))) ∧
        Tendsto (fun N : ℕ => remainderForWeight (weight c.val)
          (physicalOfSequence (projFin38 (Λ N) z))) atTop
          (𝓝 (remainderForWeight (weight c.val) (physicalOfSequence z))) := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hW := weight_continuous38 hl hb' hu'
  intro z hz
  have hz' : z ∈ Omega038 c.val := hz
  have hRW : ∀ u : PhysicalL2, remainderForWeight (weight c.val) u = remainder38 c.val u :=
    NlsGge.ThirdConsultation.I017C.remainderForWeight_eq c.val hW
  obtain ⟨-, ⟨C, -, hCs, hCb⟩⟩ := i023_house Bk lower upper c.val hl hb' hu' z hz' _ stdExh_isExhaustion
  obtain ⟨-, -, -, -, h0⟩ := Bk.remainder_tendsto_pathwise38 lower upper c.val hl hb' hu' z hz'
    stdExh_isExhaustion
  have hnn : 0 ≤ remainderForWeight (weight c.val) (physicalOfSequence z) := by
    rw [hRW, ← hB]; exact h0
  refine ⟨?_, hnn, ?_, fun Λ hΛ => ?_⟩
  · rw [← hB]
    exact Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => (hCb n).1) hCs
  · unfold sequenceRemainder
    exact max_eq_right hnn
  · obtain ⟨-, -, hlim, hN, -⟩ := Bk.remainder_tendsto_pathwise38 lower upper c.val hl hb' hu' z hz' hΛ
    simp only [hRW, ← hB]
    exact ⟨hN, hlim⟩

end NlsGge.ThirdConsultation.I023C
