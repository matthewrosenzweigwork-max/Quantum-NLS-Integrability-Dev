                                                                                                                        
                                                                                                             
                                                                                                                   
import Mathlib
import NlsGge.Hierarchy.ALSampling38

                                                                                                                                                                                                                               
                                                                                                              
                                                                                                           
                                                                                                                     
                             

set_option autoImplicit false
open Filter Topology NlsGge.Pilot NlsGge.Analysis NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.AL

namespace al066Aux

noncomputable def K066 (u : SobolevHilbert 1) : ℝ :=
  ((‖u‖ + 1) * ‖reciprocalBracketL2‖) ^ 2 + 1

theorem alh38_tendsto : Tendsto (fun N : ℕ => alh38 N) atTop (𝓝 0) := by
  refine squeeze_zero (fun N => (alh38_pos N).le) (fun N => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold alh38
  exact one_div_le_one_div_of_le (by positivity)
    (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])

theorem sample_norm_le (y : SobolevHilbert 1) (N : ℕ) (j : ZMod (2 * N + 1)) :
    ‖alSample38 N y j‖ ≤ ‖y‖ * ‖reciprocalBracketL2‖ := by
  unfold alSample38
  exact alCanon_norm_le38 _ _

theorem sample_sq_le_K (u y : SobolevHilbert 1) (hy : ‖y‖ ≤ ‖u‖ + 1) (N : ℕ)
    (j : ZMod (2 * N + 1)) :
    ‖alSample38 N y j‖ ^ 2 ≤ K066 u := by
  have hC : 0 ≤ ‖reciprocalBracketL2‖ := norm_nonneg _
  have hW : ‖alSample38 N y j‖ ≤ (‖u‖ + 1) * ‖reciprocalBracketL2‖ :=
    (sample_norm_le y N j).trans (mul_le_mul_of_nonneg_right hy hC)
  have hW0 : 0 ≤ (‖u‖ + 1) * ‖reciprocalBracketL2‖ :=
    mul_nonneg (by positivity) hC
  have hsq : ‖alSample38 N y j‖ ^ 2 ≤ ((‖u‖ + 1) * ‖reciprocalBracketL2‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hW 2
  unfold K066
  linarith

theorem eventual (β₀ : ℝ) (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hx : Tendsto x atTop (𝓝 u)) :
    ∀ᶠ N : ℕ in atTop, |(β₀ - alh38 N) / alh38 N *
        ∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N (x N) j‖ ^ 2)| ≤
        (|β₀| + 1) * (2 * K066 u ^ 2) * alh38 N ^ 2 := by
  have hxN : ∀ᶠ N : ℕ in atTop, ‖x N‖ < ‖u‖ + 1 :=
    hx.norm.eventually (gt_mem_nhds (lt_add_one ‖u‖))
  filter_upwards [hxN, eventually_ge_atTop ⌈K066 u⌉₊] with N hN hNK
  have hK0 : 0 ≤ K066 u := by unfold K066; positivity
  have hKN : K066 u ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNK)
  have hh := alh38_pos N
  have hmul := alh38_mul N
  have hne : alh38 N ≠ 0 := hh.ne'
  have h1 : alh38 N ≤ 1 := by
    unfold alh38
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hhK : alh38 N * K066 u ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hKN hh.le]
  have hr : alh38 N ^ 2 * K066 u ≤ 1 / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg hh.le hK0)]
  have hw : ∀ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ 2 ≤ K066 u :=
    fun j => sample_sq_le_K u (x N) hN.le N j
  have hw0 : ∀ j : ZMod (2 * N + 1), 0 ≤ ‖alSample38 N (x N) j‖ ^ 2 :=
    fun j => sq_nonneg _
  have l1 : |∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N (x N) j‖ ^ 2)| ≤
      2 * alh38 N ^ 3 * K066 u ^ 2 :=
    (alLogSums38 N (fun j => ‖alSample38 N (x N) j‖ ^ 2) (K066 u) hw0 hw hr).1
  have hβ : |β₀ - alh38 N| ≤ |β₀| + 1 := by
    have := abs_sub_le β₀ 0 (alh38 N)
    rw [sub_zero, zero_sub, abs_neg, abs_of_pos hh] at this
    linarith
  rw [abs_mul, abs_div, abs_of_pos hh]
  calc |β₀ - alh38 N| / alh38 N *
        |∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N (x N) j‖ ^ 2)|
      ≤ (|β₀| + 1) / alh38 N * (2 * alh38 N ^ 3 * K066 u ^ 2) :=
        mul_le_mul (div_le_div_of_nonneg_right hβ hh.le) l1 (abs_nonneg _)
          (div_nonneg (by positivity) hh.le)
    _ = (|β₀| + 1) * (2 * K066 u ^ 2) * alh38 N ^ 2 := by
        field_simp

end al066Aux

theorem al066 (β₀ : ℝ) (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hx : Tendsto x atTop (𝓝 u)) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |(β₀ - alh38 N) / alh38 N *
        ∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N (x N) j‖ ^ 2)| ≤
        C * alh38 N ^ 2) ∧
    Tendsto (fun N => (β₀ - alh38 N) / alh38 N *
      ∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N (x N) j‖ ^ 2)) atTop (𝓝 0) := by
  have hC0 : 0 ≤ (|β₀| + 1) * (2 * al066Aux.K066 u ^ 2) := by positivity
  refine ⟨⟨(|β₀| + 1) * (2 * al066Aux.K066 u ^ 2), hC0, al066Aux.eventual β₀ x u hx⟩, ?_⟩
  have hT : Tendsto (fun N : ℕ => (|β₀| + 1) * (2 * al066Aux.K066 u ^ 2) * alh38 N ^ 2)
      atTop (𝓝 0) := by
    simpa using (al066Aux.alh38_tendsto.pow 2).const_mul
      ((|β₀| + 1) * (2 * al066Aux.K066 u ^ 2))
  exact squeeze_zero_norm'
    (by
      filter_upwards [al066Aux.eventual β₀ x u hx] with N hN
      rwa [Real.norm_eq_abs])
    hT

end NlsGge.ThirdConsultation.AL

