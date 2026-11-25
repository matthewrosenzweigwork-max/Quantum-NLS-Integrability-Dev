import Mathlib
import NlsGge.Ramer.General.RamerLemma54G

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

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant

section Eventually

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- `tendsto_ramerJac_headG_ae` with `hTk` only for `k ≥ k₀`, along `κ` with `k₀ ≤ κ j`. -/
theorem tendsto_ramerJac_headG_ae_ev (m : ℕ)
    (G K : S.E → S.H) (hG : ContDiff ℝ 2 G)
    (κ : ℕ → ℕ) (hκ : StrictMono κ) (k₀ : ℕ) (hκ0 : ∀ j, k₀ ≤ κ j)
    (U : Set (S.E))
    (hT : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM K ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, k₀ ≤ k → ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM (S.projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      Tendsto (fun j => S.ramerJac (S.projField m G) (S.TM (S.projField (κ j) K) x)) atTop
        (𝓝 (S.ramerJac (S.projField m G) (S.TM K x))) := by
  have hGm : ContDiff ℝ 2 (S.projField m G) := S.contDiff_projField m G hG
  have hae := S.ramerDiv_coordE_ae_eq (S.projField m G) hGm (fun x => S.headProj_idem _ _)
  have a0 := NlsGge.Ramer.Gen.ae_on_comp hT hae
  have ak : ∀ᵐ x ∂(S.γE), ∀ j : ℕ, x ∈ U →
      S.ramerDiv (S.projField m G) (S.coordE (S.TM (S.projField (κ j) K) x)) =
        S.ramerA m (S.projField m G)
          (S.coordE (S.TM (S.projField (κ j) K) x)) :=
    ae_all_iff.2 fun j => NlsGge.Ramer.Gen.ae_on_comp (hTk (κ j) (hκ0 j)) hae
  filter_upwards [a0, ak] with x h0 hk hxU
  have key : ∀ y, S.ramerDiv (S.projField m G) (S.coordE y) =
      S.ramerA m (S.projField m G) (S.coordE y) →
      S.ramerJac (S.projField m G) y =
        S.ramerJE (S.projField m G) (S.ramerA m (S.projField m G)) y :=
    fun y hy => by rw [ramerJac_eq, ramerJE_eq, hy]
  rw [key _ (h0 hxU)]
  exact (((S.continuous_ramerJE_ramerA m _ (hGm.of_le (by norm_num))).tendsto _).comp
    ((S.tendsto_TM_projField K x).comp hκ.tendsto_atTop)).congr
    (fun j => (key _ (hk j hxU)).symm)

/-- `ramerJac_compField_proj_ae` with `hTk` eventually. -/
theorem ramerJac_compField_proj_ae_ev (m : ℕ)
    (G K : S.E → S.H) (hG : ContDiff ℝ 2 G) (hK : ContDiff ℝ 2 K)
    (U : Set (S.E))
    (hT : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM K ⁻¹' N) = 0)
    (hTk : ∀ᶠ k in atTop, ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM (S.projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      S.ramerJac (S.compField K (S.projField m G)) x =
        S.ramerJac (S.projField m G) (S.TM K x) * S.ramerJac K x := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hTk
  obtain ⟨κ₁, hκ₁, hdiv⟩ := S.ramerDiv_projField_subseq K hK
  set κ : ℕ → ℕ := fun j => κ₁ (j + k₀) with hκdef
  have hκ : StrictMono κ := fun a b h => hκ₁ (by omega)
  have hκ0 : ∀ j, k₀ ≤ κ j := fun j => (Nat.le_add_left k₀ j).trans (hκ₁.id_le _)
  have hdiv' : ∀ᵐ z ∂(S.γ),
      Tendsto (fun j => S.ramerDiv (S.projField (κ j) K) z) atTop
        (𝓝 (S.ramerDiv K z)) :=
    hdiv.mono fun z h => h.2.comp (tendsto_add_atTop_nat k₀)
  have A := S.tendsto_ramerJac_compField_proj m G K hG hK κ hκ hdiv'
  have D := S.tendsto_ramerJac_projField_ae K hK κ hκ hdiv'
  have C := S.tendsto_ramerJac_headG_ae_ev m G K hG κ hκ k₀ hκ0 U hT hk₀
  have B : ∀ᵐ x ∂(S.γE), ∀ j, x ∈ U →
      S.ramerJac (S.compField (S.projField (κ j) K) (S.projField m G)) x =
        S.ramerJac (S.projField m G) (S.TM (S.projField (κ j) K) x) *
          S.ramerJac (S.projField (κ j) K) x := by
    refine ae_all_iff.2 fun j => ?_
    exact S.ramerJac_compField_ae_on (m := max (κ j) m) (S.projField (κ j) K) (S.projField m G)
      (S.contDiff_projField _ K hK) (S.contDiff_projField _ G hG)
      (fun x => S.headProj_projField_of_le (le_max_left _ _) K x)
      (fun x => S.headProj_projField_of_le (le_max_right _ _) G x) U (hk₀ (κ j) (hκ0 j))
  filter_upwards [A, D, C, B] with x hA hD hC hB hxU
  have lim2 := (hC hxU).mul hD
  exact tendsto_nhds_unique hA (lim2.congr (fun j => (hB j hxU).symm))

/-- **Ramer Lemma 5.4, local form, with `hTk` only eventually in `k`.** -/
theorem ramer_lemma_5_4_eventually (U : Set (S.E))
    (_hU : IsOpen U) (K G : S.E → S.H)
    (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G)
    (hT : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM K ⁻¹' N) = 0)
    (hTk : ∀ᶠ k in atTop, ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM (S.projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      S.ramerJac (K + G ∘ S.TM K) x =
        S.ramerJac G (S.TM K x) * S.ramerJac K x := by
  have hF : ContDiff ℝ 2 (fun y => G (S.TM K y)) :=
    hG.comp (S.contDiff_TM K hK)
  obtain ⟨φ, hφ, hdiv⟩ := S.exists_common_subseq G (fun y => G (S.TM K y)) hG hF
  have S1 := S.tendsto_ramerJac_projField_ae G hG φ hφ (hdiv.mono fun z h => h.1)
  have S1' := NlsGge.Ramer.Gen.ae_on_comp hT S1
  have S4 := S.tendsto_ramerJac_add_projField K (fun y => G (S.TM K y)) hK hF φ hφ
    (hdiv.mono fun z h => h.2)
  have E1 : ∀ᵐ x ∂(S.γE), ∀ m : ℕ, x ∈ U →
      S.ramerJac (S.compField K (S.projField m G)) x =
        S.ramerJac (S.projField m G) (S.TM K x) * S.ramerJac K x :=
    ae_all_iff.2 fun m => S.ramerJac_compField_proj_ae_ev m G K hG hK U hT hTk
  filter_upwards [S1', S4, E1] with x s1 s4 e1 hxU
  have lim := (s1 hxU).mul_const (S.ramerJac K x)
  exact tendsto_nhds_unique s4 (lim.congr (fun j => (e1 (φ j) hxU).symm))

/-- Corollary (a) with `hTk` eventually: if `G ∘ T = -K` on `U`, then `J^G(Tx) · J^K(x) = 1`. -/
theorem ramerJac_comp_mul_eq_one_eventually (U : Set (S.E))
    (hU : IsOpen U) (K G : S.E → S.H)
    (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G)
    (hT : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM K ⁻¹' N) = 0)
    (hTk : ∀ᶠ k in atTop, ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM (S.projField k K) ⁻¹' N) = 0)
    (hGT : ∀ x ∈ U, G (S.TM K x) = -K x) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      S.ramerJac G (S.TM K x) * S.ramerJac K x = 1 := by
  have hF : ContDiff ℝ 2 (K + G ∘ S.TM K) :=
    hK.add (hG.comp (S.contDiff_TM K hK))
  have h1 := S.ramerJac_eq_one_of_eqOn_zero _ hF U hU
    (fun x hx => by simp [hGT x hx])
  filter_upwards [S.ramer_lemma_5_4_eventually U hU K G hK hG hT hTk, h1] with x ha hb hxU
  rw [← ha hxU]
  exact hb hxU


end Eventually

end NlsGge.Ramer.General.RamerSetting
