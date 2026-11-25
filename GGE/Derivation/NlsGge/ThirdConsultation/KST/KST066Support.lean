import Mathlib
import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST059
import NlsGge.Atomic.KST.KST063
import NlsGge.Atomic.KST.KST064
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Birkhoff.BirkhoffInput38
import NlsGge.Definitions.PilotInterfaces
import NlsGge.GK38.Defs
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev38.SobolevCarrier38
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST061Host
import NlsGge.ThirdConsultation.KST.KST066Host

/- KST066Support PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST066Support.lean.
   SUPPORTING module (no packet increment).  Everything for KST-066 EXCEPT smoothness of finite-gap potentials:
   `KST066S.finiteGap_of_pairFiniteGap` (same-index identification lamPlus/lamMinus (realSlice u) = upper/lower gap
   endpoints, GK38.lamPlus_real), `embed_fourierSeq`, `exists_recover`, the polynomial-weight / h^s comparison, the
   doubled-cover energy formula `energy_realSlice`, `energy_finite_iff`, `approx_step` (from kst063 with eps=1), `sobolev_norm_lt`,
   and `kst066_of_smooth`, the head of KST-066 (design STATEMENTS/KST.md "## KST-066", verbatim conclusion) under the single
   explicit hypothesis `hsm : forall w, finiteGap w -> SmoothPhysical w`, which is exactly the second conjunct of the conclusion of
   the (UNLANDED, KST-060 dependent) KST-065 `kst065 (u) (hfg : finiteGap u)`.  The hypothesis is satisfiable (true by KST-065).
   This is CONDITIONAL work: it is NOT the packet theorem `kst066`. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal

namespace NlsGge.ThirdConsultation.KST

namespace KST066S

open NlsGge.Pilot NlsGge.GK38 NlsGge.Atomic.KST001 NlsGge.Atomic.KST064 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.SpectralFoundations

/-- Same-index gap identification: finite pair gaps of the real slice give `finiteGap`. -/
theorem finiteGap_of_pairFiniteGap (g : PhysicalL2) (h : pairFiniteGap (realSlice g)) :
    NlsGge.ThirdConsultation.finiteGap g := by
  unfold NlsGge.ThirdConsultation.finiteGap
  refine h.subset fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn ⊢
  unfold NlsGge.Atomic.KST059.actualGapSequence
  rw [(lamPlus_real g n).1, (lamPlus_real g n).2]
  intro h0
  apply hn
  have h1 : (actualGapUpperAllE02_38 g n : ℂ) = (actualGapLowerAllE02_38 g n : ℂ) := sub_eq_zero.mp h0
  exact (Complex.ofReal_injective h1).symm

theorem embed_fourierSeq (s : ℝ) (hs : 0 ≤ s) (u : PhysicalSobolev38 s) (n : ℤ) :
    fourierSeq38 (physicalSobolevEmbedRealExponent s hs u) n =
      carrierCoe38 s (physicalSobolevFourierEquiv38 s u) n := by
  unfold fourierSeq38 physicalSobolevEmbedRealExponent
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact congrFun (carrierCoe38_incl38 hs _) n

theorem exists_recover (s : ℝ) (hs : 0 ≤ s) (g : PhysicalL2)
    (hg : fourierSeq38 g ∈ seqSobolev38 s) :
    ∃ v : PhysicalSobolev38 s, physicalSobolevEmbedRealExponent s hs v = g ∧
      carrierCoe38 s (physicalSobolevFourierEquiv38 s v) = fourierSeq38 g := by
  refine ⟨(physicalSobolevFourierEquiv38 s).symm (carrierMk38 s (fourierSeq38 g) hg), ?_, ?_⟩
  · apply fourierSeq38_injective
    funext n
    rw [embed_fourierSeq]
    simp
  · simp

theorem sobolevModeWeight_eq (s : ℝ) (n : ℤ) :
    sobolevModeWeight s n = (1 + (n : ℝ) ^ 2) ^ s := by
  unfold sobolevModeWeight japaneseBracket
  rw [Real.sqrt_eq_rpow]
  change (((1 + (n : ℝ) ^ 2) ^ (1 / 2 : ℝ)) ^ (2 * s) : ℝ) = _
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem natAbs_two_mul (n : ℤ) : (((2 * n).natAbs : ℕ) : ℝ) = 2 * (n.natAbs : ℝ) := by
  have : (2 * n).natAbs = 2 * n.natAbs := by omega
  rw [this]; push_cast; ring

theorem intCast_sq_eq (n : ℤ) : (n : ℝ) ^ 2 = (n.natAbs : ℝ) ^ 2 := by
  rw [← sq_abs, ← Int.cast_abs, Int.abs_eq_natAbs]; simp

theorem polynomialWeight_two_mul_sq (s : ℝ) (n : ℤ) :
    polynomialWeight s (2 * n) ^ 2 = ((1 + 2 * (n.natAbs : ℝ)) ^ 2) ^ s := by
  unfold polynomialWeight
  rw [natAbs_two_mul, sq, ← Real.mul_rpow (by positivity) (by positivity), ← sq]

theorem sobolevModeWeight_le (s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    sobolevModeWeight s n ≤ polynomialWeight s (2 * n) ^ 2 := by
  rw [sobolevModeWeight_eq, polynomialWeight_two_mul_sq, intCast_sq_eq]
  apply Real.rpow_le_rpow (by positivity) _ hs
  nlinarith [Nat.cast_nonneg (α := ℝ) n.natAbs]

theorem polynomialWeight_sq_le (s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    polynomialWeight s (2 * n) ^ 2 ≤ (6 : ℝ) ^ s * sobolevModeWeight s n := by
  rw [sobolevModeWeight_eq, polynomialWeight_two_mul_sq, intCast_sq_eq,
    ← Real.mul_rpow (by norm_num) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ hs
  have h := Nat.cast_nonneg (α := ℝ) n.natAbs
  nlinarith [sq_nonneg ((n.natAbs : ℝ) - 1)]


theorem energy_realSlice (ω : ℤ → ℝ) (hE : EvenWeight ω) (g : PhysicalL2) :
    weightedNormSq₂ ω (realSlice g) =
      2 * ∑' m : ℤ, ENNReal.ofReal (ω (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2) := by
  rw [periodOne_weightedPair_norm ω (realSlice g) hE]
  unfold weightedEvenFourierNormSq
  have h1 : ∀ m : ℤ, weightedPairMode ω (2 * m)
      (physicalFourier (realSlice g).1 m, physicalFourier (realSlice g).2 m) =
      ENNReal.ofReal (ω (2 * m) ^ 2 * ‖fourierSeq38 g (-m)‖ ^ 2) +
        ENNReal.ofReal (ω (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2) := by
    intro m
    have e1 : ‖physicalFourier (realSlice g).1 m‖ = ‖fourierSeq38 g (-m)‖ := by
      rw [fourierSeq38_apply, neg_neg, norm_neg]; rfl
    have e2 : ‖physicalFourier (realSlice g).2 m‖ = ‖fourierSeq38 g m‖ := by
      rw [fourierSeq38_apply, norm_neg, realSlice_snd, NlsGge.Schur.physicalFourier_star38, norm_star]
    simp only [weightedPairMode, e1, e2]
    rw [mul_add, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
  simp_rw [h1]
  rw [ENNReal.tsum_add]
  have h2 : ∑' m : ℤ, ENNReal.ofReal (ω (2 * m) ^ 2 * ‖fourierSeq38 g (-m)‖ ^ 2) =
      ∑' m : ℤ, ENNReal.ofReal (ω (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2) := by
    rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ => ENNReal.ofReal (ω (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2))]
    refine tsum_congr fun m => ?_
    simp only [Equiv.neg_apply]
    have : ω (2 * -m) = ω (2 * m) := by rw [mul_neg]; exact hE.even _
    rw [this]
  rw [h2, two_mul]

theorem polyEven (s : ℝ) (hs : 0 ≤ s) : EvenWeight (polynomialWeight s) :=
  ⟨fun k => by
    unfold polynomialWeight
    exact Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) k.natAbs]) hs,
   fun k => by simp [polynomialWeight]⟩

theorem polyAdmissible (s : ℝ) (hs : 0 ≤ s) :
    AdmissibleWeight (polynomialWeight s) :=
  ⟨(polyEven s hs).one_le, (polyEven s hs).even, fun j k hjk => by
    unfold polynomialWeight
    exact Real.rpow_le_rpow (by positivity)
      (by have := (Nat.cast_le (α := ℝ)).2 hjk; linarith) hs⟩

theorem energy_finite_iff (s : ℝ) (hs : 0 ≤ s) (g : PhysicalL2) :
    weightedNormSq₂ (polynomialWeight s) (realSlice g) < ⊤ ↔
      fourierSeq38 g ∈ seqSobolev38 s := by
  rw [energy_realSlice _ (polyEven s hs), mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  change _ ↔ Summable (fun n : ℤ => sobolevModeWeight s n * ‖fourierSeq38 g n‖ ^ 2)
  constructor
  · intro h
    have h0 : ∑' m : ℤ, ENNReal.ofReal (polynomialWeight s (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2) ≠ ⊤ := by
      intro htop
      rw [htop] at h
      simp at h
    have h1 : ∑' m : ℤ, ENNReal.ofReal (sobolevModeWeight s m * ‖fourierSeq38 g m‖ ^ 2) ≠ ⊤ := by
      refine ne_top_of_le_ne_top h0 (ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (sobolevModeWeight_le s hs m) (sq_nonneg _)
    have h2 := ENNReal.summable_toReal h1
    refine h2.congr fun m => ?_
    exact ENNReal.toReal_ofReal (mul_nonneg (by rw [sobolevModeWeight_eq]; positivity) (sq_nonneg _))
  · intro h
    have hnn : ∀ m : ℤ, 0 ≤ sobolevModeWeight s m * ‖fourierSeq38 g m‖ ^ 2 := fun m =>
      mul_nonneg (by rw [sobolevModeWeight_eq]; positivity) (sq_nonneg _)
    have h1 : ∑' m : ℤ, ENNReal.ofReal (polynomialWeight s (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2) ≤
        ENNReal.ofReal ((6 : ℝ) ^ s) *
          ENNReal.ofReal (∑' m : ℤ, sobolevModeWeight s m * ‖fourierSeq38 g m‖ ^ 2) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hnn h, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun m => ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      calc polynomialWeight s (2 * m) ^ 2 * ‖fourierSeq38 g m‖ ^ 2
          ≤ ((6 : ℝ) ^ s * sobolevModeWeight s m) * ‖fourierSeq38 g m‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (polynomialWeight_sq_le s hs m) (sq_nonneg _)
        _ = (6 : ℝ) ^ s * (sobolevModeWeight s m * ‖fourierSeq38 g m‖ ^ 2) := by ring
    exact ENNReal.mul_lt_top (by simp) (lt_of_le_of_lt h1 (ENNReal.mul_lt_top (by simp) (by simp)))

/-- One approximation step: a finite-gap real-slice field `g` with finite polynomial energy,
within doubled-cover energy `ε²` of `ue` (consequence of KST-063). -/
theorem approx_step (s : ℝ) (hs : 0 ≤ s) (ue : PhysicalL2)
    (hue : fourierSeq38 ue ∈ seqSobolev38 s) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : PhysicalL2, pairFiniteGap (realSlice g) ∧
      weightedNormSq₂ (polynomialWeight s) (realSlice g) < ⊤ ∧
      weightedNormSq₂ (polynomialWeight s) (realSlice (g - ue)) < ENNReal.ofReal (ε ^ 2) := by
  have hsub : NlsGge.Atomic.DM046.SubmultiplicativeWeight (polynomialWeight s) :=
    (kst_sobolev_weight_equivalence s hs).1.2.2.2.1
  have hφ : weightedNormSq₂ (polynomialWeight s) (realSlice ue) < ⊤ :=
    (energy_finite_iff s hs ue).2 hue
  have hreal : RealForm 1 (realSlice ue) :=
    ⟨Or.inl rfl, by simp [realSlice_snd]⟩
  obtain ⟨ψ, hψR, hψF, hψfin, hψclose⟩ :=
    kst063 (polynomialWeight s) (polyAdmissible s hs) hsub (realSlice ue) hφ 1 hreal ε hε
  have hψ : ψ = realSlice ψ.1 := by
    refine Prod.ext rfl ?_
    have := hψR.2
    simpa [realSlice_snd] using this
  refine ⟨ψ.1, ?_, ?_, ?_⟩
  · rw [← hψ]; exact hψF
  · rw [← hψ]; exact hψfin
  · have : realSlice (ψ.1 - ue) = ψ - realSlice ue := by
      rw [map_sub, ← hψ]
    rw [this]; exact hψclose

theorem sobolev_norm_lt (s : ℝ) (hs : 0 ≤ s) (a b : PhysicalSobolev38 s) (ε : ℝ) (hε : 0 < ε)
    (hab : weightedNormSq₂ (polynomialWeight s)
      (realSlice (physicalSobolevEmbedRealExponent s hs a -
        physicalSobolevEmbedRealExponent s hs b)) < ENNReal.ofReal (ε ^ 2)) :
    ‖a - b‖ < ε := by
  set d : SobolevCarrier38 s := physicalSobolevFourierEquiv38 s (a - b) with hd
  have hnorm : ‖a - b‖ = ‖d‖ := ((physicalSobolevFourierEquiv38 s).norm_map _).symm
  have hcoe : carrierCoe38 s d = fourierSeq38 (physicalSobolevEmbedRealExponent s hs a -
      physicalSobolevEmbedRealExponent s hs b) := by
    funext n
    rw [fourierSeq38_sub, Pi.sub_apply, embed_fourierSeq, embed_fourierSeq, hd, map_sub]
    rfl
  have hsum := carrier_hasSum_norm_sq38 s d
  rw [hcoe] at hsum
  rw [energy_realSlice _ (polyEven s hs)] at hab
  have hnn : ∀ n : ℤ, 0 ≤ sobolevModeWeight s n *
      ‖fourierSeq38 (physicalSobolevEmbedRealExponent s hs a -
        physicalSobolevEmbedRealExponent s hs b) n‖ ^ 2 := fun n =>
    mul_nonneg (by rw [sobolevModeWeight_eq]; positivity) (sq_nonneg _)
  have h1 : ENNReal.ofReal (‖d‖ ^ 2) ≤
      ∑' m : ℤ, ENNReal.ofReal (polynomialWeight s (2 * m) ^ 2 *
        ‖fourierSeq38 (physicalSobolevEmbedRealExponent s hs a -
          physicalSobolevEmbedRealExponent s hs b) m‖ ^ 2) := by
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable]
    refine ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_right (sobolevModeWeight_le s hs m) (sq_nonneg _)
  have h2 : ENNReal.ofReal (‖d‖ ^ 2) < ENNReal.ofReal (ε ^ 2) := by
    refine lt_of_le_of_lt h1 (lt_of_le_of_lt ?_ hab)
    exact le_mul_of_one_le_left zero_le (by norm_num)
  rw [hnorm]
  have h3 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 h2
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h3

end KST066S

section Conditional
open Filter Topology
open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff NlsGge.Atomic.Common

/-- CONDITIONAL reduction of KST-066: everything except smoothness of finite-gap potentials,
which is the second conjunct of the (unlanded) KST-065 conclusion, supplied as a hypothesis. -/
theorem kst066_of_smooth
    (hsm : ∀ w : PhysicalL2, NlsGge.ThirdConsultation.finiteGap w →
      NlsGge.ThirdConsultation.KO.SmoothPhysical w)
    (s : ℝ) (hs : 0 ≤ s) (u : NlsGge.Atomic.Common.PhysicalSobolev38 s) :
  ∃ v : ℕ → NlsGge.Atomic.Common.PhysicalSobolev38 s,
    Tendsto v atTop (𝓝 u) ∧
    ∀ j : ℕ, let uj := NlsGge.GKDefinitionDesign.physicalSobolevEmbedRealExponent s hs (v j)
      NlsGge.ThirdConsultation.finiteGap uj ∧ pairFiniteGap (realSlice uj) ∧
      NlsGge.ThirdConsultation.KO.SmoothPhysical uj := by
  have hue : fourierSeq38 (NlsGge.GKDefinitionDesign.physicalSobolevEmbedRealExponent s hs u) ∈
      seqSobolev38 s := by
    have : fourierSeq38 (NlsGge.GKDefinitionDesign.physicalSobolevEmbedRealExponent s hs u) =
        carrierCoe38 s (physicalSobolevFourierEquiv38 s u) :=
      funext (KST066S.embed_fourierSeq s hs u)
    rw [this]; exact carrierCoe38_mem s _
  have key := fun j : ℕ => KST066S.approx_step s hs _ hue (1 / ((j : ℝ) + 1)) (by positivity)
  choose g hgF hgfin hgclose using key
  have hmem : ∀ j : ℕ, fourierSeq38 (g j) ∈ seqSobolev38 s := fun j =>
    (KST066S.energy_finite_iff s hs (g j)).1 (hgfin j)
  choose v hv1 hv2 using fun j : ℕ => KST066S.exists_recover s hs (g j) (hmem j)
  have hnorm : ∀ j : ℕ, ‖v j - u‖ < 1 / ((j : ℝ) + 1) := fun j => by
    refine KST066S.sobolev_norm_lt s hs (v j) u _ (by positivity) ?_
    rw [hv1 j]; exact hgclose j
  refine ⟨v, ?_, fun j => ?_⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun j => dist_nonneg) (fun j => by
      rw [dist_eq_norm]; exact (hnorm j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  · show NlsGge.ThirdConsultation.finiteGap (NlsGge.GKDefinitionDesign.physicalSobolevEmbedRealExponent s hs (v j)) ∧ _
    rw [hv1 j]
    exact ⟨KST066S.finiteGap_of_pairFiniteGap _ (hgF j), hgF j,
      hsm _ (KST066S.finiteGap_of_pairFiniteGap _ (hgF j))⟩

end Conditional

end NlsGge.ThirdConsultation.KST
end
