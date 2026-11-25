import Mathlib
import NlsGge.Atomic.G5.G5004Host
import NlsGge.Atomic.G5.G5004Support1
import NlsGge.Atomic.G5.G5004Support2
import NlsGge.GK38.XiSqChiMajorant
import NlsGge.GK38.XiSqActualC3
import NlsGge.GK38.DirichletL2
import NlsGge.GK38.Lib.EntireProductsC34h

                                                                                 
                                                                                  
                                                                                                           
                                                                                                     
                                                              
set_option autoImplicit false

open Set Filter Topology Metric SummationFilter
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5004_tail (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∃ e : ℤ → ℝ, (∀ n, 0 ≤ e n) ∧
        Summable (fun n : ℤ => e n ^ 2) ∧ (∑' n : ℤ, e n ^ 2) ≤ B ∧
        ∀ n : ℤ, (N : ℤ) < |n| →
          ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖ ≤ e n := by
  obtain ⟨Uc, hUc, hUcW, c, hc, Nc, Bc, hBc, hC3⟩ := a5ActualCriticalTau_C3_bound38 φ₀ hφ₀
  obtain ⟨Ud, hUd, hUdW, Nd, hDomain⟩ := a5TailDn_omitted_domain38 φ₀ hφ₀
  obtain ⟨Ug, hUg, _hUgW, Bg, hBg, hGap⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 φ₀ hφ₀
  obtain ⟨Um, hUm, Nm, _hNm, hmu⟩ := muSeq_local_bounds38 φ₀
  obtain ⟨Ul, hUl, Cl, hCl, hlsq⟩ := muSeq_local_l2_38 φ₀
  set K : ℝ := ‖a5TauShift38 φ₀‖ + 1 with hK
  have hKev : ∀ᶠ φ in 𝓝 φ₀, ‖a5TauShift38 φ‖ ≤ K := by
    have hc0 : ContinuousAt (fun φ : PotPair => ‖a5TauShift38 φ‖) φ₀ :=
      (a5TauShift_analytic38 φ₀ hφ₀).continuousAt.norm
    filter_upwards [hc0.eventually_lt continuousAt_const
      (show ‖a5TauShift38 φ₀‖ < K by rw [hK]; linarith)] with φ hφ
    exact hφ.le
  obtain ⟨Uk, hUk, hUkP⟩ := Filter.eventually_iff_exists_mem.mp hKev
  obtain ⟨Cas, hCas⟩ := Lib.omitProd_asymp K
  set C : ℝ := c ^ 2 / 4 with hCdef
  have hC : 0 ≤ C := by positivity
  set L : ℝ := C * Real.exp (C * Bg) with hLdef
  have hL : 0 ≤ L := mul_nonneg hC (Real.exp_pos _).le
  set E : ℝ := Real.exp (Real.pi / 4) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set M1 : ℝ := 1 + L * Bg with hM1def
  have hM1 : 0 ≤ M1 := by rw [hM1def]; positivity
  set M2 : ℝ := E * L with hM2def
  have hM2 : 0 ≤ M2 := mul_nonneg hE0 hL
  let N : ℕ := max Nc (max Nd Nm)
  have hN (n : ℤ) (hn : (N : ℤ) < |n|) :
      (Nc : ℤ) < |n| ∧ (Nd : ℤ) < |n| ∧ (Nm : ℤ) < |n| := by
    have h1 : Nc ≤ N := le_max_left _ _
    have h2 : Nd ≤ N := (le_max_left Nd Nm).trans (le_max_right _ _)
    have h3 : Nm ≤ N := (le_max_right Nd Nm).trans (le_max_right _ _)
    omega
  refine ⟨Uc ∩ (Ud ∩ (Ug ∩ (Um ∩ (Ul ∩ Uk)))),
    inter_mem hUc (inter_mem hUd (inter_mem hUg (inter_mem hUm (inter_mem hUl hUk)))),
    fun φ hφ => hUcW hφ.1, N,
    3 * M1 ^ 2 * max Cas 0 + 3 * M2 ^ 2 * (Bg ^ 2 * Lib.invSqSum) + 3 * Cl, ?_, ?_⟩
  · have := Lib.invSqSum_nonneg
    positivity
  · intro φ hφ
    have hφc : φ ∈ Uc := hφ.1
    have hφd : φ ∈ Ud := hφ.2.1
    have hφg : φ ∈ Ug := hφ.2.2.1
    have hφm : φ ∈ Um := hφ.2.2.2.1
    have hφl : φ ∈ Ul := hφ.2.2.2.2.1
    have hφk : φ ∈ Uk := hφ.2.2.2.2.2
    have hφW : φ ∈ gkW := hUcW hφc
    obtain ⟨b0, hb00, hb0s, hb0B, hb0⟩ := hC3 φ hφc
    have hsγ : Summable (fun m : ℤ => ‖gamma2 φ m‖) := (hGap φ hφg).2.2.1
    have hγB : (∑' m : ℤ, ‖gamma2 φ m‖) ≤ Bg := (hGap φ hφg).2.2.2.2.2
    have hconv := a5GammaConvolution_bounds38 φ Bg hsγ hγB
    obtain ⟨bb, hbb, hbbs, hbbB⟩ := hCas (a5TauShift38 φ) (hUkP φ hφk)
    obtain ⟨hdS, hdB⟩ := hlsq φ hφl
    let g : ℤ → ℝ := fun n => a5GammaConvolution38 φ n
    let d : ℤ → ℝ := fun n => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖
    let e : ℤ → ℝ := fun n => M1 * |bb n| + M2 * g n + d n
    have hg0 : ∀ n, 0 ≤ g n := fun n => (hconv.1 n).1
    have he0 : ∀ n, 0 ≤ e n := fun n => by
      have h1 := hg0 n
      have h2 : 0 ≤ d n := norm_nonneg _
      have h3 : 0 ≤ |bb n| := abs_nonneg _
      show 0 ≤ M1 * |bb n| + M2 * g n + d n
      positivity
    have h3sq : ∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := fun x y z => by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
    have hesq : ∀ n, e n ^ 2 ≤
        3 * M1 ^ 2 * bb n ^ 2 + 3 * M2 ^ 2 * g n ^ 2 + 3 * d n ^ 2 := fun n => by
      have h := h3sq (M1 * |bb n|) (M2 * g n) (d n)
      have e1 : (M1 * |bb n|) ^ 2 = M1 ^ 2 * bb n ^ 2 := by rw [mul_pow, sq_abs]
      have e2 : (M2 * g n) ^ 2 = M2 ^ 2 * g n ^ 2 := mul_pow _ _ _
      show (M1 * |bb n| + M2 * g n + d n) ^ 2 ≤ _
      rw [e1, e2] at h
      linarith
    have hs1 : Summable (fun n : ℤ => 3 * M1 ^ 2 * bb n ^ 2) := hbbs.mul_left (3 * M1 ^ 2)
    have hs2 : Summable (fun n : ℤ => 3 * M2 ^ 2 * g n ^ 2) := hconv.2.2.2.1.mul_left (3 * M2 ^ 2)
    have hs3 : Summable (fun n : ℤ => 3 * d n ^ 2) := hdS.mul_left 3
    have hdom : Summable (fun n : ℤ => 3 * M1 ^ 2 * bb n ^ 2 + 3 * M2 ^ 2 * g n ^ 2 + 3 * d n ^ 2) :=
      (hs1.add hs2).add hs3
    have hes : Summable (fun n : ℤ => e n ^ 2) :=
      hdom.of_nonneg_of_le (fun n => sq_nonneg _) hesq
    refine ⟨e, he0, hes, ?_, ?_⟩
    · apply (hes.tsum_le_tsum hesq hdom).trans
      rw [(hs1.add hs2).tsum_add hs3, hs1.tsum_add hs2, tsum_mul_left, tsum_mul_left, tsum_mul_left]
      have h1 : 3 * M1 ^ 2 * (∑' n : ℤ, bb n ^ 2) ≤ 3 * M1 ^ 2 * max Cas 0 :=
        mul_le_mul_of_nonneg_left (hbbB.trans (le_max_left _ _)) (by positivity)
      have h2 : 3 * M2 ^ 2 * (∑' n : ℤ, g n ^ 2) ≤ 3 * M2 ^ 2 * (Bg ^ 2 * Lib.invSqSum) :=
        mul_le_mul_of_nonneg_left hconv.2.2.2.2 (by positivity)
      have h3 : 3 * (∑' n : ℤ, d n ^ 2) ≤ 3 * Cl := mul_le_mul_of_nonneg_left hdB (by norm_num)
      linarith
    · intro n hn
      obtain ⟨hnc, hnd, hnm⟩ := hN n hn
      have hz : muSeq φ n ∈ Lib.Dn n := by
        have h := (hmu φ hφm n).2 hnm
        simpa [Lib.Dn, Metric.mem_ball, dist_eq_norm] using h
      obtain ⟨hsep, -, -⟩ := hb0 n hnc (muSeq φ n) hz
      have hp := hDomain φ hφd n hnd (muSeq φ n) hz
      have hfac := a5OmittedRoot_tauQ_factorization38 n (φ, muSeq φ n) hp c hc hsep
      have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
      have hRa : radiusOmittedNormalized n φ =
          Lib.omitProd n (a5TauShift38 φ) (muSeq φ n) *
            a5QCorrectionProduct38 n (φ, muSeq φ n) := by
        unfold radiusOmittedNormalized
        rw [hfac]
        simp only [a5TauNumerator38]
        field_simp
      have hom := hbb n (muSeq φ n) hz
      have hsg := g5004_sincAt_sub_sign n hz
      have hsE := Lib.norm_sincAt_le n hz
      have hQ1 := a5QCorrectionProduct_linear_bound38 n (φ, muSeq φ n) hφW c hc hsep Bg
        (hconv.1 n).2
      have hgn := hg0 n
      have hQn : ‖a5QCorrectionProduct38 n (φ, muSeq φ n)‖ ≤ M1 := by
        have hq : a5QCorrectionProduct38 n (φ, muSeq φ n) =
            (a5QCorrectionProduct38 n (φ, muSeq φ n) - 1) + 1 := by ring
        have h1 := norm_add_le (a5QCorrectionProduct38 n (φ, muSeq φ n) - 1) (1 : ℂ)
        rw [← hq, norm_one] at h1
        have h2 : L * g n ≤ L * Bg := mul_le_mul_of_nonneg_left (hconv.1 n).2 hL
        have h3 : ‖a5QCorrectionProduct38 n (φ, muSeq φ n) - 1‖ ≤ L * g n := hQ1
        rw [hM1def]
        linarith
      have hbbn : 0 ≤ bb n := (norm_nonneg _).trans hom
      rw [hRa]
      set oo := Lib.omitProd n (a5TauShift38 φ) (muSeq φ n) with hoo
      set s := Lib.sincAt n (muSeq φ n) with hs
      set Q := a5QCorrectionProduct38 n (φ, muSeq φ n) with hQ
      set pn : ℂ := (-1 : ℂ) ^ n with hpn
      have hdecomp : oo * Q - pn = (oo - s) * Q + s * (Q - 1) + (s - pn) := by ring
      have hA : ‖(oo - s) * Q‖ ≤ bb n * M1 := by
        rw [norm_mul]
        exact mul_le_mul hom hQn (norm_nonneg _) hbbn
      have hB : ‖s * (Q - 1)‖ ≤ E * (L * g n) := by
        rw [norm_mul]
        exact mul_le_mul hsE (hQ1.trans (le_refl _)) (norm_nonneg _) hE0
      have hCc : ‖s - pn‖ ≤ d n := hsg
      calc ‖oo * Q - pn‖ = ‖(oo - s) * Q + s * (Q - 1) + (s - pn)‖ := by rw [hdecomp]
        _ ≤ ‖(oo - s) * Q‖ + ‖s * (Q - 1)‖ + ‖s - pn‖ := norm_add₃_le
        _ ≤ bb n * M1 + E * (L * g n) + d n := by linarith
        _ ≤ M1 * |bb n| + M2 * g n + d n := by
          have h1 : bb n * M1 ≤ M1 * |bb n| := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_abs_self _) hM1
          have h2 : E * (L * g n) = M2 * g n := by rw [hM2def]; ring
          linarith

theorem radiusOmittedNormalized_local_l2
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ U : Set PotPair,
    IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ sourceBetaW ∧
    ∃ B : ℝ, 0 < B ∧ ∀ φ : PotPair, φ ∈ U →
      Summable (fun n : ℤ =>
        ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖ ^ 2) ∧
      (∑' n : ℤ,
        ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖ ^ 2) ≤ B := by
  obtain ⟨Ut, hUt, hUtW, N, Bt, hBt, hT⟩ := g5004_tail φ₀ (sourceBetaW_subset_gkW hφ₀)
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  let X : ℤ → ℝ := fun n => ‖radiusOmittedNormalized n φ₀ - (-1 : ℂ) ^ n‖ + 1
  have hfin : ∀ᶠ φ in 𝓝 φ₀, ∀ n ∈ S,
      ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖ ≤ X n := by
    rw [Filter.eventually_all_finset]
    intro n _
    have hcont : ContinuousAt
        (fun φ : PotPair => ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖) φ₀ :=
      ((radiusOmittedNormalized_analytic n φ₀ hφ₀).continuousAt.sub continuousAt_const).norm
    filter_upwards [hcont.eventually_lt continuousAt_const
      (show ‖radiusOmittedNormalized n φ₀ - (-1 : ℂ) ^ n‖ < X n by simp [X])] with φ hφ
    exact hφ.le
  have hW : Ut ∩ ({φ | ∀ n ∈ S, ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖ ≤ X n} ∩
      sourceBetaW) ∈ 𝓝 φ₀ :=
    inter_mem hUt (inter_mem hfin (sourceFamily.V_open.mem_nhds hφ₀))
  obtain ⟨t, htW, htO, hφt⟩ := _root_.mem_nhds_iff.mp hW
  have hX0 : 0 ≤ ∑ n ∈ S, X n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  refine ⟨t, htO, hφt, fun φ hφ => (htW hφ).2.2, Bt + ∑ n ∈ S, X n ^ 2 + 1, by positivity, ?_⟩
  intro φ hφ
  obtain ⟨hφUt, hφS, -⟩ := htW hφ
  obtain ⟨e, he0, hes, heB, he⟩ := hT φ hφUt
  let f : ℤ → ℝ := fun n => e n ^ 2 + (if n ∈ S then X n ^ 2 else 0)
  have hf2 : Summable (fun n : ℤ => if n ∈ S then X n ^ 2 else 0) :=
    summable_of_ne_finset_zero (s := S) fun n hn => by simp [hn]
  have hfs : Summable f := hes.add hf2
  have hle : ∀ n : ℤ, ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖ ^ 2 ≤ f n := fun n => by
    by_cases hn : n ∈ S
    · have h1 : ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖ ≤ X n := hφS n hn
      have h2 : ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖ ^ 2 ≤ X n ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      show _ ≤ e n ^ 2 + (if n ∈ S then X n ^ 2 else 0)
      have h3 : (if n ∈ S then X n ^ 2 else 0) = X n ^ 2 := by simp [hn]
      rw [h3]
      nlinarith [sq_nonneg (e n)]
    · have hn' : (N : ℤ) < |n| := by
        by_contra hcon
        apply hn
        simp only [S, Finset.mem_Icc]
        exact abs_le.mp (not_lt.mp hcon)
      have h1 := he n hn'
      have h2 : ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖ ^ 2 ≤ e n ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      show _ ≤ e n ^ 2 + (if n ∈ S then X n ^ 2 else 0)
      have h3 : (if n ∈ S then X n ^ 2 else 0) = 0 := by simp [hn]
      rw [h3]
      linarith
  have hsum : Summable (fun n : ℤ => ‖radiusOmittedNormalized n φ - (-1 : ℂ) ^ n‖ ^ 2) :=
    hfs.of_nonneg_of_le (fun n => sq_nonneg _) hle
  refine ⟨hsum, ?_⟩
  apply (hsum.tsum_le_tsum hle hfs).trans
  have hT2 : (∑' n : ℤ, (if n ∈ S then X n ^ 2 else 0)) = ∑ n ∈ S, X n ^ 2 := by
    rw [tsum_eq_sum (s := S) fun n hn => by simp [hn]]
    exact Finset.sum_congr rfl fun n hn => by simp [hn]
  show (∑' n : ℤ, (e n ^ 2 + (if n ∈ S then X n ^ 2 else 0))) ≤ _
  rw [hes.tsum_add hf2, hT2]
  linarith

end
end NlsGge.GKDefinitionDesign
