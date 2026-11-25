import Mathlib
import NlsGge.ThirdConsultation.G3.G3015Support
import NlsGge.Atomic.G3.G3017
import NlsGge.Atomic.G3.G3002
import NlsGge.Atomic.G3.G3ZetaHost
import NlsGge.Atomic.G3.G3SegmentHost
import NlsGge.Atomic.G4.G4012
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.G2.G2021
import NlsGge.GK38.TauGamma
import NlsGge.GK38.AngleDirichletAnalytic

/- G3-022 SUPPORT (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/ThirdConsultation/G3/G3022Support.lean, namespace NlsGge.GKDefinitionDesign.G3022Aux.
   Supporting lemmas for the G3_022 head; no head is stated here.  Source route (GK 15.2, p. 84, last paragraph):
   on a disc inside Z_m, beta = eps_m * int_{tau_m}^{mu_m} zeta_m^n dlambda and the straight-segment integral is analytic.
   * collapsed_basic / seg_dom: on the collapsed set the straight segment tau -> mu lies in the isolating disc and in the
     omitted-root domain of the m-th root product;
   * psi_tau_zero: psi_n(tau_m) = 0 on Z_m (psi = 2 i rootProduct (tau - z) betaZeta off tau, then a limit z -> tau);
   * integrand_formula: on Z_m \ E_m, betaZeta(z_t) (mu - tau) = - psi(z_t) / (2 i t rootProduct(z_t)) for t in (0,1)
     (landed G3015Aux.factor_off with normalizedRoot = tau from G3_002);
   * segIntegrand_analyticAt / segIntegrand_bound: analytic in the potential and bounded uniformly on compact parameter sets
     (mean value inequality for psi in the spectral variable, psi(tau)=0, continuity of d_w psi and of 1/rootProduct on a compact set);
   * J_analytic: landed G4-012 analyticOn_integral_of_locally_dominated gives analyticity of z |-> collapsedBetaFinalSegment
     (a + z v) 0 on any open set of parameters whose potentials lie in Z_m \ E_m.
   The analytic anchor gkSourceBeta_analytic38 / gk151BetaAmbient_analytic38 is NOT used here. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G3022Aux
noncomputable section

/-- The point of the straight segment from `tau_m` to `mu_m` at parameter `t`. -/
def segPt (m : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  tauN φ m + (t : ℂ) * (muSeq φ m - tauN φ m)

/-- `- psi_n(z_t) / (2 i t rootProduct_m(phi, z_t))`, the regularised integrand of the collapsed segment integral. -/
def segIntegrand (n m : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  -(psi n φ (segPt m φ t)) / (2 * Complex.I * (t : ℂ) * rootProduct m (φ, segPt m φ t))

theorem collapsed_basic (n m : ℤ) (hmn : m ≠ n) (φ : PotPair) (hφ : φ ∈ collapsedSet m) :
    φ ∈ gkW ∧ lamPlus φ m = lamMinus φ m ∧ tauN φ m = lamMinus φ m ∧
    normalizedRoot n m φ = tauN φ m ∧
    (∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → segPt m φ s ∈ ball (discC φ m) (discR φ m)) := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ.1
  obtain ⟨hPM, hτ⟩ := G3017Aux.tau_eq_lamMinus m φ hgk hφ.2
  have hnr : normalizedRoot n m φ = tauN φ m := (G3_002 n m hmn φ hφ.1 hφ.2).1
  obtain ⟨_c, _N, _hg, hspec⟩ := isolating_family38 φ hgk
  have hτB : tauN φ m ∈ ball (discC φ m) (discR φ m) := by
    refine (hspec.1 m).1 ?_
    rw [hτ]
    exact left_mem_segment ℝ _ _
  have hμB : muSeq φ m ∈ ball (discC φ m) (discR φ m) := (hspec.1 m).2.1
  refine ⟨hgk, hPM, hτ, hnr, fun s hs => ?_⟩
  have h := (convex_ball (discC φ m) (discR φ m)).add_smul_sub_mem hτB hμB hs
  rw [Complex.real_smul] at h
  exact h

theorem seg_dom (n m : ℤ) (hmn : m ≠ n) (φ : PotPair) (hφ : φ ∈ collapsedSet m) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) : (φ, segPt m φ s) ∈ a5OmittedRootDomain38 m := by
  obtain ⟨hgk, -, -, -, hball⟩ := collapsed_basic n m hmn φ hφ
  exact ⟨hgk, fun k hk => closedBall_avoids_other_gaps φ hgk m k hk _
    (ball_subset_closedBall (hball s hs))⟩

theorem psi_tau_zero (n m : ℤ) (hmn : m ≠ n) (φ : PotPair) (hφ : φ ∈ collapsedSet m) :
    psi n φ (tauN φ m) = 0 := by
  obtain ⟨hgk, hPM, hτ, hnr, hball⟩ := collapsed_basic n m hmn φ hφ
  have hW : φ ∈ sourceW := hφ.1
  have hτB : tauN φ m ∈ ball (discC φ m) (discR φ m) := by
    have h := hball 0 ⟨le_refl _, zero_le_one⟩
    simpa [segPt] using h
  have hseg : segment ℝ (lamMinus φ m) (lamPlus φ m) = {tauN φ m} := by
    rw [hPM, hτ, segment_same]
  have hpsi : ContinuousAt (psi n φ) (tauN φ m) :=
    ((G2_075.2.2.2.2.1 n φ hW).1 _ (mem_univ _)).continuousAt
  have hζ : ContinuousAt (betaZeta n m φ) (tauN φ m) :=
    ((G3_002 n m hmn φ hW hφ.2).2.2.2.2.1 _ hτB).continuousAt
  have hdom : (φ, tauN φ m) ∈ a5OmittedRootDomain38 m := by
    have h := seg_dom n m hmn φ hφ 0 ⟨le_refl _, zero_le_one⟩
    simpa [segPt] using h
  have hrP : ContinuousAt (fun z : ℂ => rootProduct m (φ, z)) (tauN φ m) :=
    (((G2_021 m).2.1 _ hdom).continuousAt).comp
      (continuousAt_const.prodMk continuousAt_id)
  have hR : ContinuousAt (fun z : ℂ => 2 * Complex.I * rootProduct m (φ, z) *
      ((normalizedRoot n m φ - z) * betaZeta n m φ z)) (tauN φ m) :=
    (continuousAt_const.mul hrP).mul
      ((continuousAt_const.sub continuousAt_id).mul hζ)
  have hRval : (2 * Complex.I * rootProduct m (φ, tauN φ m) *
      ((normalizedRoot n m φ - tauN φ m) * betaZeta n m φ (tauN φ m))) = 0 := by
    rw [hnr, sub_self, zero_mul, mul_zero]
  have hball' : ball (discC φ m) (discR φ m) ∈ 𝓝 (tauN φ m) := isOpen_ball.mem_nhds hτB
  have heq : ∀ᶠ z in 𝓝[≠] tauN φ m, psi n φ z = 2 * Complex.I * rootProduct m (φ, z) *
      ((normalizedRoot n m φ - z) * betaZeta n m φ z) := by
    filter_upwards [nhdsWithin_le_nhds hball', self_mem_nhdsWithin] with z hz hne
    exact G3015Aux.factor_off n m hmn φ hW z hz (by rw [hseg]; exact hne)
  have h1 : Tendsto (psi n φ) (𝓝[≠] tauN φ m) (𝓝 (psi n φ (tauN φ m))) :=
    hpsi.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (psi n φ) (𝓝[≠] tauN φ m) (𝓝 0) := by
    have h3 : Tendsto (fun z : ℂ => 2 * Complex.I * rootProduct m (φ, z) *
        ((normalizedRoot n m φ - z) * betaZeta n m φ z)) (𝓝[≠] tauN φ m)
        (𝓝 (2 * Complex.I * rootProduct m (φ, tauN φ m) *
        ((normalizedRoot n m φ - tauN φ m) * betaZeta n m φ (tauN φ m)))) :=
      hR.tendsto.mono_left nhdsWithin_le_nhds
    rw [hRval] at h3
    exact h3.congr' (heq.mono fun z hz => hz.symm)
  exact tendsto_nhds_unique h1 h2

theorem integrand_formula (n m : ℤ) (hmn : m ≠ n) (φ : PotPair)
    (hφ : φ ∈ collapsedSet m \ endpointSet m) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    betaZeta n m φ (segPt m φ t) * (muSeq φ m - tauN φ m) = segIntegrand n m φ t := by
  obtain ⟨hgk, hPM, hτ, hnr, hball⟩ := collapsed_basic n m hmn φ hφ.1
  have hd : muSeq φ m - tauN φ m ≠ 0 := sub_ne_zero.mpr (G3017Aux.mu_facts m φ hφ).2.2.1
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have hs : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hseg : segment ℝ (lamMinus φ m) (lamPlus φ m) = {tauN φ m} := by
    rw [hPM, hτ, segment_same]
  have hwτ : segPt m φ t - tauN φ m = (t : ℂ) * (muSeq φ m - tauN φ m) := by
    unfold segPt
    ring
  have hwne : segPt m φ t ≠ tauN φ m := by
    intro h
    rw [h, sub_self] at hwτ
    exact mul_ne_zero htc hd hwτ.symm
  have hf := G3015Aux.factor_off n m hmn φ hφ.1.1 (segPt m φ t) (hball t hs)
    (by rw [hseg]; exact hwne)
  rw [hnr] at hf
  have hrP : rootProduct m (φ, segPt m φ t) ≠ 0 :=
    (G2_021 m).2.2 _ (seg_dom n m hmn φ hφ.1 t hs)
  have hY : 2 * Complex.I * (t : ℂ) * rootProduct m (φ, segPt m φ t) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) htc) hrP
  unfold segIntegrand
  rw [eq_div_iff hY, hf]
  have hτw : tauN φ m - segPt m φ t = -((t : ℂ) * (muSeq φ m - tauN φ m)) := by
    rw [← hwτ]
    ring
  rw [hτw]
  ring

theorem segIntegrand_analyticAt (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair)
    (hφ0 : φ0 ∈ collapsedSet m) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    AnalyticAt ℂ (fun φ : PotPair => segIntegrand n m φ t) φ0 := by
  have hgk : φ0 ∈ gkW := sourceFamily.W_gk hφ0.1
  have hs : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have hτA : AnalyticAt ℂ (fun φ : PotPair => tauN φ m) φ0 := tauN_analytic m φ0 hgk
  have hμA : AnalyticAt ℂ (fun φ : PotPair => muSeq φ m) φ0 :=
    analyticOnNhd_muSeq_complex38 m φ0 hgk
  have hzA : AnalyticAt ℂ (fun φ : PotPair => segPt m φ t) φ0 :=
    hτA.add (analyticAt_const.mul (hμA.sub hτA))
  have hpair : AnalyticAt ℂ (fun φ : PotPair => (φ, segPt m φ t)) φ0 :=
    analyticAt_id.prod hzA
  have hpsi : AnalyticAt ℂ (fun φ : PotPair => psi n φ (segPt m φ t)) φ0 :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => psi n p.1 p.2)
      (f := fun φ : PotPair => (φ, segPt m φ t))
      (G2_075.2.2.2.1 n _ ⟨hφ0.1, mem_univ _⟩) hpair
  have hdom := seg_dom n m hmn φ0 hφ0 t hs
  have hrP : AnalyticAt ℂ (fun φ : PotPair => rootProduct m (φ, segPt m φ t)) φ0 :=
    AnalyticAt.comp (g := rootProduct m) (f := fun φ : PotPair => (φ, segPt m φ t))
      ((G2_021 m).2.1 _ hdom) hpair
  have hrN : rootProduct m (φ0, segPt m φ0 t) ≠ 0 := (G2_021 m).2.2 _ hdom
  have hY : 2 * Complex.I * (t : ℂ) * rootProduct m (φ0, segPt m φ0 t) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) htc) hrN
  have h := hpsi.neg.div (analyticAt_const.mul hrP) hY
  exact h.congr (Filter.Eventually.of_forall fun ψ => rfl)

theorem segIntegrand_continuousOn (n m : ℤ) (hmn : m ≠ n) (φ : PotPair)
    (hφ : φ ∈ collapsedSet m) :
    ContinuousOn (segIntegrand n m φ) (Ioo (0 : ℝ) 1) := by
  have hwc : Continuous (fun t : ℝ => segPt m φ t) := by
    unfold segPt
    fun_prop
  have hpsi : Continuous (fun t : ℝ => psi n φ (segPt m φ t)) :=
    ((G2_075.2.2.2.2.1 n φ hφ.1).1.continuousOn).comp_continuous hwc (fun _ => mem_univ _)
  have hrP : ContinuousOn (fun t : ℝ => rootProduct m (φ, segPt m φ t)) (Icc (0 : ℝ) 1) :=
    ((G2_021 m).2.1.continuousOn).comp (continuousOn_const.prodMk hwc.continuousOn)
      (fun t ht => seg_dom n m hmn φ hφ t ht)
  have hden : ContinuousOn (fun t : ℝ => 2 * Complex.I * (t : ℂ) * rootProduct m (φ, segPt m φ t))
      (Ioo (0 : ℝ) 1) :=
    ((continuousOn_const.mul Complex.continuous_ofReal.continuousOn).mul
      (hrP.mono Ioo_subset_Icc_self))
  have h := hpsi.continuousOn.neg.div hden (fun t ht => by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) htc)
      ((G2_021 m).2.2 _ (seg_dom n m hmn φ hφ t ⟨ht.1.le, ht.2.le⟩)))
  exact h

theorem psi_deriv_continuousOn (n : ℤ) :
    ContinuousOn (fun p : PotPair × ℂ => deriv (psi n p.1) p.2) (sourceW ×ˢ (univ : Set ℂ)) := by
  have hA := G2_075.2.2.2.1 n
  have hF : ContinuousOn (fun p : PotPair × ℂ =>
      fderiv ℂ (fun q : PotPair × ℂ => psi n q.1 q.2) p ((0 : PotPair), (1 : ℂ)))
      (sourceW ×ˢ (univ : Set ℂ)) :=
    (hA.fderiv.continuousOn).clm_apply continuousOn_const
  refine hF.congr (fun p hp => ?_)
  have hd : DifferentiableAt ℂ (fun q : PotPair × ℂ => psi n q.1 q.2) p :=
    (hA p hp).differentiableAt
  have h1 : HasDerivAt (fun w : ℂ => ((p.1, w) : PotPair × ℂ)) ((0 : PotPair), (1 : ℂ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h2 := hd.hasFDerivAt.comp_hasDerivAt p.2 h1
  exact h2.deriv

/-- Pure estimate: all compactness input is supplied as constants. -/
theorem segIntegrand_norm_le (n m : ℤ) (hmn : m ≠ n) (φ : PotPair) (hφ : φ ∈ collapsedSet m)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (M1 M2 M3 : ℝ) (h1 : 0 ≤ M1) (h2 : 0 ≤ M2) (h3 : 0 ≤ M3)
    (hM1 : ∀ s ∈ Icc (0 : ℝ) 1, ‖deriv (psi n φ) (segPt m φ s)‖ ≤ M1)
    (hM2 : ‖muSeq φ m - tauN φ m‖ ≤ M2)
    (hM3 : ‖(rootProduct m (φ, segPt m φ t))⁻¹‖ ≤ M3) :
    ‖segIntegrand n m φ t‖ ≤ M1 * M2 * M3 / 2 := by
  have hts : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hW : φ ∈ sourceW := hφ.1
  have hsegEq : ∀ s : ℝ, tauN φ m + s • (muSeq φ m - tauN φ m) = segPt m φ s := fun s => by
    unfold segPt
    rw [Complex.real_smul]
  have hMVT : ‖psi n φ (segPt m φ t) - psi n φ (tauN φ m)‖ ≤ M1 * ‖segPt m φ t - tauN φ m‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le (f := psi n φ)
      (s := segment ℝ (tauN φ m) (muSeq φ m)) ?_ ?_ (convex_segment _ _)
      (left_mem_segment ℝ _ _) ?_
    · intro x _
      exact ((G2_075.2.2.2.2.1 n φ hW).1 x (mem_univ _)).differentiableAt
    · intro x hx
      rw [segment_eq_image'] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      show ‖deriv (psi n φ) (tauN φ m + s • (muSeq φ m - tauN φ m))‖ ≤ M1
      rw [hsegEq s]
      exact hM1 s hs
    · rw [segment_eq_image']
      exact ⟨t, hts, hsegEq t⟩
  have hpt : psi n φ (tauN φ m) = 0 := psi_tau_zero n m hmn _ hφ
  rw [hpt, sub_zero] at hMVT
  have hwτ : segPt m φ t - tauN φ m = (t : ℂ) * (muSeq φ m - tauN φ m) := by
    unfold segPt
    ring
  have hnw : ‖segPt m φ t - tauN φ m‖ = t * ‖muSeq φ m - tauN φ m‖ := by
    rw [hwτ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
  rw [norm_inv] at hM3
  have hrne : ‖rootProduct m (φ, segPt m φ t)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ((G2_021 m).2.2 _ (seg_dom n m hmn _ hφ t hts))
  have hnorm : ‖segIntegrand n m φ t‖ =
      ‖psi n φ (segPt m φ t)‖ * ‖rootProduct m (φ, segPt m φ t)‖⁻¹ / (2 * t) := by
    unfold segIntegrand
    rw [norm_div, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht.1]
    have h2' : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2']
    field_simp
  rw [hnorm, div_le_iff₀ (by linarith [ht.1])]
  have hA : ‖psi n φ (segPt m φ t)‖ ≤ M1 * (t * M2) := by
    refine hMVT.trans ?_
    rw [hnw]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM2 ht.1.le) h1
  have hB := mul_le_mul hA hM3 (inv_nonneg.mpr (norm_nonneg _))
    (mul_nonneg h1 (mul_nonneg ht.1.le h2))
  calc ‖psi n φ (segPt m φ t)‖ * ‖rootProduct m (φ, segPt m φ t)‖⁻¹
      ≤ M1 * (t * M2) * M3 := hB
    _ = M1 * M2 * M3 / 2 * (2 * t) := by ring

theorem path_tau_mu_continuousOn (m : ℤ) (a v : PotPair) (K : Set ℂ)
    (hgk : ∀ z ∈ K, a + z • v ∈ gkW) :
    ContinuousOn (fun z : ℂ => tauN (a + z • v) m) K ∧
      ContinuousOn (fun z : ℂ => muSeq (a + z • v) m) K := by
  have hφc : Continuous (fun z : ℂ => a + z • v) := by fun_prop
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have h : ContinuousAt (fun z : ℂ => tauN (a + z • v) m) z :=
      ContinuousAt.comp (g := fun φ : PotPair => tauN φ m) (f := fun z : ℂ => a + z • v)
        (tauN_analytic m _ (hgk z hz)).continuousAt hφc.continuousAt
    exact h.continuousWithinAt
  · have h : ContinuousAt (fun z : ℂ => muSeq (a + z • v) m) z :=
      ContinuousAt.comp (g := fun φ : PotPair => muSeq φ m) (f := fun z : ℂ => a + z • v)
        (analyticOnNhd_muSeq_complex38 m _ (hgk z hz)).continuousAt hφc.continuousAt
    exact h.continuousWithinAt

theorem path_segPt_continuousOn (m : ℤ) (a v : PotPair) (K : Set ℂ)
    (hgk : ∀ z ∈ K, a + z • v ∈ gkW) :
    ContinuousOn (fun p : ℂ × ℝ => segPt m (a + p.1 • v) p.2) (K ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨hτc, hμc⟩ := path_tau_mu_continuousOn m a v K hgk
  have hKTK : ∀ p ∈ K ×ˢ Icc (0 : ℝ) 1, p.1 ∈ K := fun p hp => hp.1
  have hτ2 : ContinuousOn (fun p : ℂ × ℝ => tauN (a + p.1 • v) m) (K ×ˢ Icc (0 : ℝ) 1) :=
    ContinuousOn.comp (g := fun z : ℂ => tauN (a + z • v) m) (f := Prod.fst) hτc
      continuousOn_fst hKTK
  have hμ2 : ContinuousOn (fun p : ℂ × ℝ => muSeq (a + p.1 • v) m) (K ×ˢ Icc (0 : ℝ) 1) :=
    ContinuousOn.comp (g := fun z : ℂ => muSeq (a + z • v) m) (f := Prod.fst) hμc
      continuousOn_fst hKTK
  have hr : ContinuousOn (fun p : ℂ × ℝ => ((p.2 : ℝ) : ℂ)) (K ×ˢ Icc (0 : ℝ) 1) :=
    Complex.continuous_ofReal.comp_continuousOn continuousOn_snd
  exact hτ2.add (hr.mul (hμ2.sub hτ2))

theorem segIntegrand_bound (n m : ℤ) (hmn : m ≠ n) (a v : PotPair) (K : Set ℂ)
    (hK : IsCompact K) (hKc : ∀ z ∈ K, a + z • v ∈ collapsedSet m) :
    ∃ C : ℝ, ∀ z ∈ K, ∀ t ∈ Ioo (0 : ℝ) 1, ‖segIntegrand n m (a + z • v) t‖ ≤ C := by
  have hφc : Continuous (fun z : ℂ => a + z • v) := by fun_prop
  have hgk : ∀ z ∈ K, a + z • v ∈ gkW := fun z hz => sourceFamily.W_gk (hKc z hz).1
  obtain ⟨hτc, hμc⟩ := path_tau_mu_continuousOn m a v K hgk
  have hKT : IsCompact (K ×ˢ Icc (0 : ℝ) 1) := hK.prod isCompact_Icc
  have hKTK : ∀ p ∈ K ×ˢ Icc (0 : ℝ) 1, p.1 ∈ K := fun p hp => hp.1
  have hP := path_segPt_continuousOn m a v K hgk
  have hpair : ContinuousOn (fun p : ℂ × ℝ => ((a + p.1 • v, segPt m (a + p.1 • v) p.2) :
      PotPair × ℂ)) (K ×ˢ Icc (0 : ℝ) 1) :=
    ContinuousOn.prodMk (hφc.comp continuous_fst).continuousOn hP
  have hΨ : ContinuousOn (fun p : ℂ × ℝ =>
      deriv (psi n (a + p.1 • v)) (segPt m (a + p.1 • v) p.2)) (K ×ˢ Icc (0 : ℝ) 1) :=
    ContinuousOn.comp (g := fun q : PotPair × ℂ => deriv (psi n q.1) q.2)
      (f := fun p : ℂ × ℝ => ((a + p.1 • v, segPt m (a + p.1 • v) p.2) : PotPair × ℂ))
      (psi_deriv_continuousOn n) hpair (fun p hp => ⟨(hKc p.1 hp.1).1, mem_univ _⟩)
  have hD : ContinuousOn (fun p : ℂ × ℝ => muSeq (a + p.1 • v) m - tauN (a + p.1 • v) m)
      (K ×ˢ Icc (0 : ℝ) 1) :=
    (ContinuousOn.comp (g := fun z : ℂ => muSeq (a + z • v) m) (f := Prod.fst) hμc
      continuousOn_fst hKTK).sub
    (ContinuousOn.comp (g := fun z : ℂ => tauN (a + z • v) m) (f := Prod.fst) hτc
      continuousOn_fst hKTK)
  have hRP : ContinuousOn (fun p : ℂ × ℝ =>
      rootProduct m (a + p.1 • v, segPt m (a + p.1 • v) p.2)) (K ×ˢ Icc (0 : ℝ) 1) :=
    ContinuousOn.comp (g := rootProduct m)
      (f := fun p : ℂ × ℝ => ((a + p.1 • v, segPt m (a + p.1 • v) p.2) : PotPair × ℂ))
      (G2_021 m).2.1.continuousOn hpair
      (fun p hp => seg_dom n m hmn _ (hKc p.1 hp.1) p.2 hp.2)
  have hR : ContinuousOn (fun p : ℂ × ℝ =>
      (rootProduct m (a + p.1 • v, segPt m (a + p.1 • v) p.2))⁻¹) (K ×ˢ Icc (0 : ℝ) 1) :=
    ContinuousOn.inv₀ hRP
      (fun p hp => (G2_021 m).2.2 _ (seg_dom n m hmn _ (hKc p.1 hp.1) p.2 hp.2))
  obtain ⟨M1, hM1⟩ := hKT.exists_bound_of_continuousOn hΨ
  obtain ⟨M2, hM2⟩ := hKT.exists_bound_of_continuousOn hD
  obtain ⟨M3, hM3⟩ := hKT.exists_bound_of_continuousOn hR
  refine ⟨max M1 0 * max M2 0 * max M3 0 / 2, fun z hz t ht => ?_⟩
  have hts : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  refine segIntegrand_norm_le n m hmn _ (hKc z hz) t ht (max M1 0) (max M2 0) (max M3 0)
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (fun s hs => ?_)
    ((hM2 (z, t) ⟨hz, hts⟩).trans (le_max_left _ _))
    ((hM3 (z, t) ⟨hz, hts⟩).trans (le_max_left _ _))
  exact (hM1 (z, s) ⟨hz, hs⟩).trans (le_max_left _ _)

theorem J_analytic (n m : ℤ) (hmn : m ≠ n) (a v : PotPair) (N : Set ℂ) (hN : IsOpen N)
    (hNc : ∀ z ∈ N, a + z • v ∈ collapsedSet m \ endpointSet m) :
    AnalyticOnNhd ℂ (fun z : ℂ => collapsedBetaFinalSegment n m (a + z • v) 0) N := by
  have hφA : ∀ z : ℂ, AnalyticAt ℂ (fun z : ℂ => a + z • v) z := fun z =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hmain : AnalyticOnNhd ℂ (fun z : ℂ =>
      ∫ t, segIntegrand n m (a + z • v) t ∂(volume.restrict (Ioo (0 : ℝ) 1))) N := by
    apply NlsGge.Atomic.G4.analyticOn_integral_of_locally_dominated hN
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      intro z hz
      exact AnalyticAt.comp (g := fun φ : PotPair => segIntegrand n m φ t)
        (f := fun z : ℂ => a + z • v)
        (segIntegrand_analyticAt n m hmn _ (hNc z hz).1 t ht) (hφA z)
    · intro u hu
      exact (segIntegrand_continuousOn n m hmn _ (hNc u hu).1).aestronglyMeasurable
        measurableSet_Ioo
    · intro u hu
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hN u hu
      have hρ2 : 0 < ρ / 2 := by positivity
      have hsub : ball u (ρ / 2) ⊆ N := (ball_subset_ball (by linarith)).trans hball
      refine ⟨ρ / 2, hρ2, hsub, ?_⟩
      obtain ⟨C, hC⟩ := segIntegrand_bound n m hmn a v (closedBall u (ρ / 2))
        (isCompact_closedBall _ _)
        (fun z hz => (hNc z (hball (closedBall_subset_ball (by linarith) hz))).1)
      refine ⟨fun _ => C, integrable_const C, fun w hw => ?_⟩
      exact (ae_restrict_iff' measurableSet_Ioo).2
        (Filter.Eventually.of_forall fun t ht => hC w (ball_subset_closedBall hw) t ht)
  refine hmain.congr hN (fun z hz => ?_)
  show (∫ t, segIntegrand n m (a + z • v) t ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
    collapsedBetaFinalSegment n m (a + z • v) 0
  unfold collapsedBetaFinalSegment
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine (setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)).symm
  exact integrand_formula n m hmn _ (hNc z hz) t ht

end
end G3022Aux
end NlsGge.GKDefinitionDesign
