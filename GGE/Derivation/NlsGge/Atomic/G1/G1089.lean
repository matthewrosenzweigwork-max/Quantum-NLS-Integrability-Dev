import Mathlib
import NlsGge.Atomic.G1.G1087
import NlsGge.GK38.DirichletL2
import NlsGge.GK38.TauGammaL2Realization
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.PoissonMixedNormingData
import NlsGge.GK38.PoissonMixedTargets
import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.IsolatingFamily

/- G1-089 (proof development, AUTHOR; not reviewed).  Statement = proof development's G1089_COMMAND01 (see `G1089_main`).
   Route (GK complex extension): complex labels on PotPair: the mu coordinate mc = muSeq - n*pi on the open set gkW
   (analytic: analyticOnNhd_muSeq_complex38; locally uniform l2: muSeq_l2) and the kappa coordinate kc =
   2*log(parity*normingFactor(muSeq)) on an open set Vk containing the real slice (analytic where the log argument is in the slit
   plane; locally uniform l2: tail from G1-087 `G1087_complex` plus finite head by continuity).  Both are made l2-valued analytic by
   `local_l2_analytic_realization38`; restriction to the real slice via the R-linear `realSlice`, real parts via a bounded
   R-linear map l2(C) -> l2(R). -/

set_option autoImplicit false
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.Pilot Filter Topology Set

namespace NlsGge.Atomic.G1089

noncomputable section

def argK (n : ℤ) (φ : PotPair) : ℂ := parity n * normingFactor φ (muSeq φ n)

def kc (φ : PotPair) (n : ℤ) : ℂ := 2 * Complex.log (argK n φ)

def mc (φ : PotPair) (n : ℤ) : ℂ := muSeq φ n - (n : ℂ) * (Real.pi : ℂ)

theorem argK_analyticAt (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) : AnalyticAt ℂ (argK n) φ := by
  have h2 : AnalyticAt ℂ (fun ψ : PotPair => normingFactor ψ (muSeq ψ n)) φ :=
    (analyticOnNhd_normingFactor38 (φ, muSeq φ n) (mem_univ _)).comp
      (f := fun x : PotPair => (x, muSeq x n)) (x := φ)
      (analyticAt_id.prod (analyticOnNhd_muSeq_complex38 n φ hφ))
  exact analyticAt_const.mul h2

theorem parity_im (n : ℤ) : (parity n).im = 0 := by
  unfold parity
  rcases Int.even_or_odd n with h | h
  · simp [h.neg_one_zpow]
  · simp [h.neg_one_zpow]

theorem real_arg (u : PhysicalL2) (n : ℤ) :
    argK n (realSlice u) = ((signedNorming38 u n : ℝ) : ℂ) ∧ 0 < signedNorming38 u n := by
  obtain ⟨V, hV, N, C, hVv⟩ := NlsGge.Atomic.G1087S2.Final.G1087_real u
  have h := (hVv u (mem_of_mem_nhds hV)).1 n
  refine ⟨?_, h.2⟩
  have hmu : muSeq (realSlice u) n = (gkMu u n : ℂ) := muSeq_eq_gkMu38 u n
  have harg : argK n (realSlice u) = parity n * normingFactor (realSlice u) (gkMu u n : ℂ) := by
    unfold argK; rw [hmu]
  rw [harg]
  apply Complex.ext
  · rw [Complex.ofReal_re]; rfl
  · rw [Complex.mul_im, parity_im, h.1, Complex.ofReal_im]
    ring

theorem kc_real (u : PhysicalL2) (n : ℤ) : kc (realSlice u) n = ((realKappa38 u n : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := real_arg u n
  unfold kc realKappa38
  rw [h1, ← Complex.ofReal_log h2.le]
  push_cast
  ring

theorem mc_real (u : PhysicalL2) (n : ℤ) :
    mc (realSlice u) n = ((gkMu u n - (n : ℝ) * Real.pi : ℝ) : ℂ) := by
  unfold mc
  rw [muSeq_eq_gkMu38 u n]
  push_cast
  ring

/-- Good open sets on which the kappa log argument stays in the slit plane for every index and the
squared tail of kappa is bounded uniformly. -/
def GoodSet (s : Set PotPair) : Prop :=
  IsOpen s ∧ s ⊆ gkW ∧ (∀ ψ ∈ s, ∀ n : ℤ, argK n ψ ∈ Complex.slitPlane) ∧
    ∃ (N : ℕ) (C : ℝ), ∀ ψ ∈ s,
      Summable (fun n : ℤ => if N < n.natAbs then ‖kc ψ n‖ ^ 2 else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then ‖kc ψ n‖ ^ 2 else 0) ≤ C

def Vk : Set PotPair := ⋃₀ {s | GoodSet s}

theorem isOpen_Vk : IsOpen Vk := isOpen_sUnion fun s hs => hs.1

theorem realSlice_mem_Vk (u : PhysicalL2) : realSlice u ∈ Vk := by
  have hφ₀ : realSlice u ∈ gkW := realSlice_mem_gkW u
  obtain ⟨V₀, hV₀, N, C, hV⟩ := NlsGge.Atomic.G1087S2.Final.G1087_complex (realSlice u)
  have hfin : ∀ᶠ ψ in 𝓝 (realSlice u), ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      argK n ψ ∈ Complex.slitPlane := by
    rw [Filter.eventually_all_finset]
    intro n _
    have hc := (argK_analyticAt n (realSlice u) hφ₀).continuousAt
    refine hc.eventually (Complex.isOpen_slitPlane.mem_nhds ?_)
    rw [(real_arg u n).1]
    exact Complex.ofReal_mem_slitPlane.2 (real_arg u n).2
  set T : Set PotPair := {ψ | ψ ∈ gkW ∧ ψ ∈ V₀ ∧ ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      argK n ψ ∈ Complex.slitPlane} with hT
  have hTn : T ∈ 𝓝 (realSlice u) := by
    have h1 : gkW ∈ 𝓝 (realSlice u) := isOpen_gkW.mem_nhds hφ₀
    filter_upwards [h1, hV₀, hfin] with ψ a b c
    exact ⟨a, b, c⟩
  refine ⟨interior T, ⟨isOpen_interior, ?_, ?_, N, C, ?_⟩, mem_interior_iff_mem_nhds.2 hTn⟩
  · intro ψ hψ
    exact (interior_subset hψ).1
  · intro ψ hψ n
    have hψT := interior_subset hψ
    by_cases hn : N < n.natAbs
    · exact (hV ψ hψT.2.1).1 n hn
    · exact hψT.2.2 n (by rw [Finset.mem_Icc]; omega)
  · intro ψ hψ
    have hψT := interior_subset hψ
    exact ⟨(hV ψ hψT.2.1).2.1, (hV ψ hψT.2.1).2.2.1⟩
  
theorem kc_analyticAt (ψ : PotPair) (hψ : ψ ∈ Vk) (n : ℤ) : AnalyticAt ℂ (fun φ => kc φ n) ψ := by
  obtain ⟨s, hs, hψs⟩ := hψ
  obtain ⟨-, hsW, hslit, -⟩ := hs
  have h := (argK_analyticAt n ψ (hsW hψs)).clog (hslit ψ hψs n)
  exact analyticAt_const.mul h

/-- The locally uniform l2 bound for the kappa coordinates (separate leaf, built from the G1-087
tail bound and continuity of the finitely many head coordinates). -/
theorem kc_local_l2 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ Vk) : IsLocUnifL2Seq kc φ₀ := by
  obtain ⟨s, hs, hφs⟩ := hφ₀
  obtain ⟨hso, hsW, hslit, N, C, htail⟩ := hs
  set F : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hF
  have hcont : ∀ n ∈ F, ∀ᶠ ψ in 𝓝 φ₀, ‖kc ψ n‖ ≤ ‖kc φ₀ n‖ + 1 := by
    intro n _
    have hc : ContinuousAt (fun φ => kc φ n) φ₀ := (kc_analyticAt φ₀ ⟨s, ⟨hso, hsW, hslit, N, C, htail⟩, hφs⟩ n).continuousAt
    have := hc.norm.eventually (gt_mem_nhds (lt_add_one ‖kc φ₀ n‖))
    filter_upwards [this] with ψ h using h.le
  have hevF : ∀ᶠ ψ in 𝓝 φ₀, ∀ n ∈ F, ‖kc ψ n‖ ≤ ‖kc φ₀ n‖ + 1 :=
    (Filter.eventually_all_finset F).2 hcont
  set B : ℝ := ∑ n ∈ F, (‖kc φ₀ n‖ + 1) ^ 2 with hB
  refine ⟨s ∩ {ψ | ∀ n ∈ F, ‖kc ψ n‖ ≤ ‖kc φ₀ n‖ + 1}, inter_mem (hso.mem_nhds hφs) hevF,
    C + B, fun ψ hψ => ?_⟩
  obtain ⟨hψs, hψF⟩ := hψ
  obtain ⟨hg, hgle⟩ := htail ψ hψs
  set g : ℤ → ℝ := fun n => if N < n.natAbs then ‖kc ψ n‖ ^ 2 else 0 with hg_def
  set h : ℤ → ℝ := fun n => if N < n.natAbs then 0 else ‖kc ψ n‖ ^ 2 with hh_def
  have hsplit : (fun n : ℤ => ‖kc ψ n‖ ^ 2) = fun n => g n + h n := by
    funext n
    by_cases hn : N < n.natAbs <;> simp [hg_def, hh_def, hn]
  have hhs : Summable h := by
    refine summable_of_ne_finset_zero (s := F) fun n hn => ?_
    have : N < n.natAbs := by
      by_contra hc
      exact hn (by rw [hF, Finset.mem_Icc]; omega)
    simp [hh_def, this]
  have hsum : Summable (fun n : ℤ => ‖kc ψ n‖ ^ 2) := by
    rw [hsplit]; exact hg.add hhs
  refine ⟨hsum, ?_⟩
  have htsum : ∑' n : ℤ, ‖kc ψ n‖ ^ 2 = ∑' n, g n + ∑' n, h n := by
    rw [hsplit]; exact hg.tsum_add hhs
  have hhtsum : ∑' n, h n = ∑ n ∈ F, ‖kc ψ n‖ ^ 2 := by
    rw [tsum_eq_sum (s := F)]
    · apply Finset.sum_congr rfl
      intro n hn
      have : ¬ N < n.natAbs := by
        rw [hF, Finset.mem_Icc] at hn; omega
      simp [hh_def, this]
    · intro n hn
      have : N < n.natAbs := by
        by_contra hc
        exact hn (by rw [hF, Finset.mem_Icc]; omega)
      simp [hh_def, this]
  have hFle : ∑ n ∈ F, ‖kc ψ n‖ ^ 2 ≤ B := by
    apply Finset.sum_le_sum
    intro n hn
    exact pow_le_pow_left₀ (norm_nonneg _) (hψF n hn) 2
  rw [htsum, hhtsum]
  linarith

theorem l2_sq_summable (x : Lib.L2Z) : Summable (fun n : ℤ => ‖x n‖ ^ 2) := by
  simpa using (lp.hasSum_norm (p := (2 : ENNReal)) (E := fun _ : ℤ => ℂ) (by norm_num) x).summable

theorem re_memℓp (x : Lib.L2Z) : Memℓp (fun n : ℤ => (x n).re) 2 := by
  refine (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr ?_
  have hs : Summable (fun n : ℤ => ‖(x n).re‖ ^ 2) :=
    (l2_sq_summable x).of_nonneg_of_le (fun n => by positivity) (fun n => by
      have : ‖(x n).re‖ ≤ ‖x n‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (x n)
      exact pow_le_pow_left₀ (norm_nonneg _) this 2)
  simpa using hs

def reL2 : Lib.L2Z →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => (x n).re, re_memℓp x⟩
      map_add' := fun x y => by ext n; simp <;> rfl
      map_smul' := fun c x => by ext n; simp <;> rfl }
    1 (fun x => by
      have hx : Summable (fun n : ℤ => ‖x n‖ ^ 2) := by
        simpa using (lp.hasSum_norm (p := (2 : ENNReal)) (E := fun _ : ℤ => ℂ) (by norm_num) x).summable
      set y : lp (fun _ : ℤ => ℝ) 2 := ⟨fun n => (x n).re, re_memℓp x⟩ with hy
      have hys : Summable (fun n : ℤ => ‖y n‖ ^ 2) := by
        simpa using (lp.hasSum_norm (p := (2 : ENNReal)) (E := fun _ : ℤ => ℝ) (by norm_num) y).summable
      have hy2 : ‖y‖ ^ 2 = ∑' n : ℤ, ‖y n‖ ^ 2 := by
        have he := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) y
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using he
      have hx2 : ‖x‖ ^ 2 = ∑' n : ℤ, ‖x n‖ ^ 2 := by
        have he := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using he
      have hle : ∑' n : ℤ, ‖y n‖ ^ 2 ≤ ∑' n : ℤ, ‖x n‖ ^ 2 := by
        refine hys.tsum_le_tsum (fun n => ?_) hx
        have : ‖y n‖ ≤ ‖x n‖ := by
          simpa only [hy, Real.norm_eq_abs] using Complex.abs_re_le_norm (x n)
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      by_contra hc
      push_neg at hc
      have hlt : ‖x‖ < ‖y‖ := by simpa using hc
      nlinarith [norm_nonneg y, norm_nonneg x, hy2, hx2, hle])

theorem reL2_apply (x : Lib.L2Z) (n : ℤ) : (reL2 x : ℤ → ℝ) n = (x n).re := rfl

theorem G1089_main : ((
  ∃ (Kap Mu : PhysicalL2 → lp (fun _ : ℤ => ℝ) 2),
    (∀ u : PhysicalL2, ∀ n : ℤ, (Kap u : ℤ → ℝ) n = realKappa38 u n) ∧
    (∀ u : PhysicalL2, ∀ n : ℤ, (Mu u : ℤ → ℝ) n = gkMu u n - (n : ℝ) * Real.pi) ∧
    AnalyticOnNhd ℝ (fun u : PhysicalL2 => (Kap u, Mu u)) Set.univ
  : Prop)) := by
  -- kappa
  obtain ⟨Ak, hAk, hAkan⟩ := local_l2_analytic_realization38 Vk kc isOpen_Vk
    (fun n φ hφ => kc_analyticAt φ hφ n) (fun φ₀ h => kc_local_l2 φ₀ h)
  -- mu
  obtain ⟨Am, hAm, hAman⟩ := local_l2_analytic_realization38 gkW mc isOpen_gkW
    (fun n φ hφ => (analyticOnNhd_muSeq_complex38 n φ hφ).sub analyticAt_const)
    (fun φ₀ _ => muSeq_l2 φ₀)
  refine ⟨fun u => reL2 (Ak (realSlice u)), fun u => reL2 (Am (realSlice u)), ?_, ?_, ?_⟩
  · intro u n
    rw [reL2_apply, hAk (realSlice u) (realSlice_mem_Vk u) n, kc_real]
    simp
  · intro u n
    rw [reL2_apply, hAm (realSlice u) (realSlice_mem_gkW u) n, mc_real]
    simp
  · have h1 : AnalyticOnNhd ℝ (fun u : PhysicalL2 => Ak (realSlice u)) univ :=
      (hAkan.restrictScalars (𝕜 := ℝ)).comp (realSlice.analyticOnNhd univ)
        (fun u _ => realSlice_mem_Vk u)
    have h2 : AnalyticOnNhd ℝ (fun u : PhysicalL2 => Am (realSlice u)) univ :=
      (hAman.restrictScalars (𝕜 := ℝ)).comp (realSlice.analyticOnNhd univ)
        (fun u _ => realSlice_mem_gkW u)
    exact ((reL2.analyticOnNhd univ).comp h1 (fun _ _ => mem_univ _)).prod
      ((reL2.analyticOnNhd univ).comp h2 (fun _ _ => mem_univ _))

end

end NlsGge.Atomic.G1089
