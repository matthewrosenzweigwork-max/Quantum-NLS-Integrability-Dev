import Mathlib
import NlsGge.Ramer.RamerLemma54

/-!
# R9c': Ramer Lemma 5.4 with `hTk` only eventually in `k`

Versions of `ramer_lemma_5_4` and `ramerJac_comp_mul_eq_one` whose truncation hypothesis holds only
for `k` large (`∀ᶠ k in atTop`).  The proof only uses `hTk` along subsequences `κ j → ∞`, which are
shifted past the threshold.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

section Eventually

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- `tendsto_ramerJac_headG_ae` with `hTk` only for `k ≥ k₀`, along `κ` with `k₀ ≤ κ j`. -/
theorem tendsto_ramerJac_headG_ae_ev (hs : (1 : ℝ) / 2 < s) (m : ℕ)
    (G K : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G)
    (κ : ℕ → ℕ) (hκ : StrictMono κ) (k₀ : ℕ) (hκ0 : ∀ j, k₀ ≤ κ j)
    (U : Set (FullWeightedHilbert c s))
    (hT : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs K ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, k₀ ≤ k → ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs (projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      Tendsto (fun j => ramerJac c s hs (projField m G) (TM c s hs (projField (κ j) K) x)) atTop
        (𝓝 (ramerJac c s hs (projField m G) (TM c s hs K x))) := by
  have hGm : ContDiff ℝ 2 (projField m G) := contDiff_projField m G hG
  have hae := ramerDiv_coordE_ae_eq c s hs (projField m G) hGm (fun x => headProj_idem _ _)
  have a0 := ae_on_comp hT hae
  have ak : ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), ∀ j : ℕ, x ∈ U →
      ramerDiv c s hs (projField m G) (coordE c s (TM c s hs (projField (κ j) K) x)) =
        ramerA c s (zero_le_of_half_lt hs) m (projField m G)
          (coordE c s (TM c s hs (projField (κ j) K) x)) :=
    ae_all_iff.2 fun j => ae_on_comp (hTk (κ j) (hκ0 j)) hae
  filter_upwards [a0, ak] with x h0 hk hxU
  have key : ∀ y, ramerDiv c s hs (projField m G) (coordE c s y) =
      ramerA c s (zero_le_of_half_lt hs) m (projField m G) (coordE c s y) →
      ramerJac c s hs (projField m G) y =
        ramerJE c s hs (projField m G) (ramerA c s (zero_le_of_half_lt hs) m (projField m G)) y :=
    fun y hy => by rw [ramerJac_eq, ramerJE_eq, hy]
  rw [key _ (h0 hxU)]
  exact (((continuous_ramerJE_ramerA c s hs m _ (hGm.of_le (by norm_num))).tendsto _).comp
    ((tendsto_TM_projField c s hs K x).comp hκ.tendsto_atTop)).congr
    (fun j => (key _ (hk j hxU)).symm)

/-- `ramerJac_compField_proj_ae` with `hTk` eventually. -/
theorem ramerJac_compField_proj_ae_ev (hs : (1 : ℝ) / 2 < s) (m : ℕ)
    (G K : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (hK : ContDiff ℝ 2 K)
    (U : Set (FullWeightedHilbert c s))
    (hT : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs K ⁻¹' N) = 0)
    (hTk : ∀ᶠ k in atTop, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs (projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      ramerJac c s hs (compField c s hs K (projField m G)) x =
        ramerJac c s hs (projField m G) (TM c s hs K x) * ramerJac c s hs K x := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hTk
  obtain ⟨κ₁, hκ₁, hdiv⟩ := ramerDiv_projField_subseq c s hs K hK
  set κ : ℕ → ℕ := fun j => κ₁ (j + k₀) with hκdef
  have hκ : StrictMono κ := fun a b h => hκ₁ (by omega)
  have hκ0 : ∀ j, k₀ ≤ κ j := fun j => (Nat.le_add_left k₀ j).trans (hκ₁.id_le _)
  have hdiv' : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerDiv c s hs (projField (κ j) K) z) atTop
        (𝓝 (ramerDiv c s hs K z)) :=
    hdiv.mono fun z h => h.2.comp (tendsto_add_atTop_nat k₀)
  have A := tendsto_ramerJac_compField_proj c s hs m G K hG hK κ hκ hdiv'
  have D := tendsto_ramerJac_projField_ae c s hs K hK κ hκ hdiv'
  have C := tendsto_ramerJac_headG_ae_ev c s hs m G K hG κ hκ k₀ hκ0 U hT hk₀
  have B : ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), ∀ j, x ∈ U →
      ramerJac c s hs (compField c s hs (projField (κ j) K) (projField m G)) x =
        ramerJac c s hs (projField m G) (TM c s hs (projField (κ j) K) x) *
          ramerJac c s hs (projField (κ j) K) x := by
    refine ae_all_iff.2 fun j => ?_
    exact ramerJac_compField_ae_on hs (m := max (κ j) m) (projField (κ j) K) (projField m G)
      (contDiff_projField _ K hK) (contDiff_projField _ G hG)
      (fun x => headProj_projField_of_le (le_max_left _ _) K x)
      (fun x => headProj_projField_of_le (le_max_right _ _) G x) U (hk₀ (κ j) (hκ0 j))
  filter_upwards [A, D, C, B] with x hA hD hC hB hxU
  have lim2 := (hC hxU).mul hD
  exact tendsto_nhds_unique hA (lim2.congr (fun j => (hB j hxU).symm))

/-- **Ramer Lemma 5.4, local form, with `hTk` only eventually in `k`.** -/
theorem ramer_lemma_5_4_eventually (hs : (1 : ℝ) / 2 < s) (U : Set (FullWeightedHilbert c s))
    (_hU : IsOpen U) (K G : FullWeightedHilbert c s → ActualCM c)
    (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G)
    (hT : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs K ⁻¹' N) = 0)
    (hTk : ∀ᶠ k in atTop, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs (projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      ramerJac c s hs (K + G ∘ TM c s hs K) x =
        ramerJac c s hs G (TM c s hs K x) * ramerJac c s hs K x := by
  have hF : ContDiff ℝ 2 (fun y => G (TM c s hs K y)) :=
    hG.comp (contDiff_TM c s hs K hK)
  obtain ⟨φ, hφ, hdiv⟩ := exists_common_subseq c s hs G (fun y => G (TM c s hs K y)) hG hF
  have S1 := tendsto_ramerJac_projField_ae c s hs G hG φ hφ (hdiv.mono fun z h => h.1)
  have S1' := ae_on_comp hT S1
  have S4 := tendsto_ramerJac_add_projField c s hs K (fun y => G (TM c s hs K y)) hK hF φ hφ
    (hdiv.mono fun z h => h.2)
  have E1 : ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), ∀ m : ℕ, x ∈ U →
      ramerJac c s hs (compField c s hs K (projField m G)) x =
        ramerJac c s hs (projField m G) (TM c s hs K x) * ramerJac c s hs K x :=
    ae_all_iff.2 fun m => ramerJac_compField_proj_ae_ev c s hs m G K hG hK U hT hTk
  filter_upwards [S1', S4, E1] with x s1 s4 e1 hxU
  have lim := (s1 hxU).mul_const (ramerJac c s hs K x)
  exact tendsto_nhds_unique s4 (lim.congr (fun j => (e1 (φ j) hxU).symm))

/-- Corollary (a) with `hTk` eventually: if `G ∘ T = -K` on `U`, then `J^G(Tx) · J^K(x) = 1`. -/
theorem ramerJac_comp_mul_eq_one_eventually (hs : (1 : ℝ) / 2 < s)
    (U : Set (FullWeightedHilbert c s))
    (hU : IsOpen U) (K G : FullWeightedHilbert c s → ActualCM c)
    (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G)
    (hT : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs K ⁻¹' N) = 0)
    (hTk : ∀ᶠ k in atTop, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs (projField k K) ⁻¹' N) = 0)
    (hGT : ∀ x ∈ U, G (TM c s hs K x) = -K x) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      ramerJac c s hs G (TM c s hs K x) * ramerJac c s hs K x = 1 := by
  have hF : ContDiff ℝ 2 (K + G ∘ TM c s hs K) :=
    hK.add (hG.comp (contDiff_TM c s hs K hK))
  have h1 := ramerJac_eq_one_of_eqOn_zero hs _ hF U hU
    (fun x hx => by simp [hGT x hx])
  filter_upwards [ramer_lemma_5_4_eventually c s hs U hU K G hK hG hT hTk, h1] with x ha hb hxU
  rw [← ha hxU]
  exact hb hxU

#check @ramer_lemma_5_4_eventually
#check @ramerJac_comp_mul_eq_one_eventually
#print axioms ramer_lemma_5_4_eventually
#print axioms ramerJac_comp_mul_eq_one_eventually

end Eventually

end NlsGge.Ramer
