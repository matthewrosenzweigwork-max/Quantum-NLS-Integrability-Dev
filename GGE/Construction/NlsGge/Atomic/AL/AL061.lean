import Mathlib
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Atomic.AL.AL060
import NlsGge.Atomic.AL.AL059
import NlsGge.Birkhoff.F05Identity38i

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

open MeasureTheory Filter Topology Set NlsGge.Pilot NlsGge.Analysis NlsGge.AblowitzLadik
  NlsGge.HierarchyRiccati.Core

def sampleStep (N : ℕ) (shift : ℤ) (u : SobolevHilbert 1) : ℝ → ℂ :=
  stepArray N (fun j => alSample38 N u (j + (shift : ZMod (2 * N + 1))))

namespace AL061Aux

theorem canon_cell (y : SobolevHilbert 1) (N : ℕ) (k : ℤ) (s : ℝ) :
    alCanon38 y (alt38 N (k : ZMod (2 * N + 1)) + s) = alCanon38 y ((k : ℝ) * alh38 N + s) := by
  have hn : ((2 * N + 1 : ℕ) : ℝ) * alh38 N = 1 := by
    have := alh38_mul N; push_cast; linarith
  have hval : (((k : ZMod (2 * N + 1)).val : ℤ)) = k % ((2 * N + 1 : ℕ) : ℤ) := ZMod.val_intCast (n := 2 * N + 1) k
  have hk : (k : ℝ) = ((k : ZMod (2 * N + 1)).val : ℝ) + ((k / ((2 * N + 1 : ℕ) : ℤ) : ℤ) : ℝ) * ((2 * N + 1 : ℕ) : ℝ) := by
    have h1 : k = k % ((2 * N + 1 : ℕ) : ℤ) + ((2 * N + 1 : ℕ) : ℤ) * (k / ((2 * N + 1 : ℕ) : ℤ)) :=
      (Int.emod_add_mul_ediv k _).symm
    have h2 : (k : ℝ) = ((k % ((2 * N + 1 : ℕ) : ℤ) : ℤ) : ℝ) +
        ((2 * N + 1 : ℕ) : ℝ) * ((k / ((2 * N + 1 : ℕ) : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
    rw [← hval] at h2
    push_cast at h2 ⊢
    linarith
  have hper := (alCanon_periodic38 y).int_mul (k / ((2 * N + 1 : ℕ) : ℤ))
  have e : (k : ℝ) * alh38 N + s = (alt38 N (k : ZMod (2 * N + 1)) + s) +
      ((k / ((2 * N + 1 : ℕ) : ℤ) : ℤ) : ℝ) * 1 := by
    unfold alt38
    rw [hk]
    have : ((k / ((2 * N + 1 : ℕ) : ℤ) : ℤ) : ℝ) * ((2 * N + 1 : ℕ) : ℝ) * alh38 N =
        ((k / ((2 * N + 1 : ℕ) : ℤ) : ℤ) : ℝ) * 1 := by rw [mul_assoc, hn]
    linarith
  rw [e]
  exact (hper (alt38 N (k : ZMod (2 * N + 1)) + s)).symm

theorem canon_cell0 (y : SobolevHilbert 1) (N : ℕ) (k : ℤ) :
    alCanon38 y (alt38 N (k : ZMod (2 * N + 1))) = alCanon38 y ((k : ℝ) * alh38 N) := by
  have := canon_cell y N k 0
  simpa using this

theorem canon_cell_sub (y : SobolevHilbert 1) (N : ℕ) (k : ℤ) :
    alCanon38 y (alt38 N (k : ZMod (2 * N + 1)) - alh38 N) =
      alCanon38 y ((k : ℝ) * alh38 N - alh38 N) := by
  have := canon_cell y N k (-(alh38 N))
  simpa [sub_eq_add_neg] using this

theorem forward_eq (N : ℕ) (y : SobolevHilbert 1) (t : ℝ) :
    forwardStep N y t = NlsGge.Atomic.AL060.alForwardStep38 N (alCanon38 y) t := by
  unfold forwardStep stepArray alFd38 NlsGge.Atomic.AL060.alForwardStep38 NlsGge.Atomic.AL060.alCellLeft38
  rw [canon_cell y N _ (alh38 N), canon_cell0 y N]

theorem backward_eq (N : ℕ) (y : SobolevHilbert 1) (t : ℝ) :
    backwardStep N y t = NlsGge.Atomic.AL060.alBackwardStep38 N (alCanon38 y) t := by
  unfold backwardStep stepArray alBd38 NlsGge.Atomic.AL060.alBackwardStep38 NlsGge.Atomic.AL060.alCellLeft38
  rw [canon_cell0 y N, canon_cell_sub y N]

local instance alFin061 : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

theorem mk_mp : MeasurePreserving (QuotientAddGroup.mk : ℝ → PhysicalCircle)
    (volume.restrict (Set.Ioc (0 : ℝ) 1)) spatialMeasure := by
  have hv : (volume : Measure PhysicalCircle) = spatialMeasure := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp [spatialMeasure]
  have hm : MeasurePreserving (QuotientAddGroup.mk : ℝ → PhysicalCircle)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [← hv]; exact hm

theorem alDeriv_memLp (u : SobolevHilbert 1) :
    MemLp (alDeriv38 u) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  (Lp.memLp (physicalH1DerivativeL2CLM u)).comp_measurePreserving mk_mp

theorem eLpNorm_alDeriv (u : SobolevHilbert 1) :
    eLpNorm (alDeriv38 u) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) =
      ENNReal.ofReal ‖physicalH1DerivativeL2CLM u‖ := by
  have h := eLpNorm_comp_measurePreserving (p := 2) (Lp.aestronglyMeasurable (physicalH1DerivativeL2CLM u))
    mk_mp
  show eLpNorm ((⇑(physicalH1DerivativeL2CLM u)) ∘ (QuotientAddGroup.mk : ℝ → PhysicalCircle)) 2
    (volume.restrict (Set.Ioc (0 : ℝ) 1)) = _
  rw [h, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]

theorem alDeriv_sub_ae (u v : SobolevHilbert 1) :
    alDeriv38 (u - v) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t => alDeriv38 u t - alDeriv38 v t := by
  have h : (⇑(physicalH1DerivativeL2CLM (u - v))) =ᵐ[spatialMeasure]
      ⇑(physicalH1DerivativeL2CLM u) - ⇑(physicalH1DerivativeL2CLM v) := by
    rw [map_sub]; exact Lp.coeFn_sub _ _
  have h2 := mk_mp.quasiMeasurePreserving.ae h
  filter_upwards [h2] with t ht
  exact ht

theorem forward_sub (N : ℕ) (x y : SobolevHilbert 1) (t : ℝ) :
    forwardStep N (x - y) t = forwardStep N x t - forwardStep N y t := by
  unfold forwardStep stepArray; rw [alFd_sub38]

theorem backward_sub (N : ℕ) (x y : SobolevHilbert 1) (t : ℝ) :
    backwardStep N (x - y) t = backwardStep N x t - backwardStep N y t := by
  unfold backwardStep stepArray; rw [alBd_sub38]

theorem forward_memLp {N : ℕ} {y : SobolevHilbert 1} (hy : alInF38 N y) :
    MemLp (forwardStep N y) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have : forwardStep N y = NlsGge.Atomic.AL060.alForwardStep38 N
      (planeReal N (physicalH1FiniteProjectionPlane N y)) := by
    funext t
    rw [forward_eq]
    have hc : alCanon38 y = planeReal N (physicalH1FiniteProjectionPlane N y) :=
      funext fun s => alCanon_plane38 hy s
    rw [hc]
  rw [this]
  exact (NlsGge.Atomic.AL060.alStep_memLp38 N _ N).1

theorem backward_memLp {N : ℕ} {y : SobolevHilbert 1} (hy : alInF38 N y) :
    MemLp (backwardStep N y) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have : backwardStep N y = NlsGge.Atomic.AL060.alBackwardStep38 N
      (planeReal N (physicalH1FiniteProjectionPlane N y)) := by
    funext t
    rw [backward_eq]
    have hc : alCanon38 y = planeReal N (physicalH1FiniteProjectionPlane N y) :=
      funext fun s => alCanon_plane38 hy s
    rw [hc]
  rw [this]
  exact (NlsGge.Atomic.AL060.alStep_memLp38 N _ N).2

theorem eLpNorm_le_of_integral (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (D : ℝ) (hD : 0 ≤ D) (h : ∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2 ≤ D ^ 2) :
    eLpNorm f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤ ENNReal.ofReal D := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  refine Real.sqrt_le_iff.2 ⟨hD, ?_⟩
  rw [intervalIntegral.integral_of_le zero_le_one] at h
  exact h

theorem forward_bound {N : ℕ} {y : SobolevHilbert 1} (hy : alInF38 N y) :
    eLpNorm (forwardStep N y) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal ‖physicalH1DerivativeL2CLM y‖ := by
  obtain ⟨_, _, h3, _, h5, _⟩ := al059 N y hy
  exact eLpNorm_le_of_integral _ (forward_memLp hy) _ (norm_nonneg _) (h5.trans_le h3)

theorem backward_bound {N : ℕ} {y : SobolevHilbert 1} (hy : alInF38 N y) :
    eLpNorm (backwardStep N y) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal ‖physicalH1DerivativeL2CLM y‖ := by
  obtain ⟨_, _, _, h4, _, h6⟩ := al059 N y hy
  exact eLpNorm_le_of_integral _ (backward_memLp hy) _ (norm_nonneg _) (h6.trans_le h4)

theorem poly_forward {M : ℕ} {p : SobolevHilbert 1} (hp : alInF38 M p) :
    Tendsto (fun N => eLpNorm (fun t => forwardStep N p t - alDeriv38 p t) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
  set z := physicalH1FiniteProjectionPlane M p with hz
  have hc : alCanon38 p = planeReal M z := funext fun s => alCanon_plane38 hp s
  have hae : alDeriv38 p =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] planeReal M (derivativePlane M z) := by
    filter_upwards [NlsGge.Birkhoff.alDeriv_plane38 hp] with t ht
    rw [ht, deriv_planeReal]
  have h := (NlsGge.Atomic.AL060.fixedTrigPolynomial_difference_L2_38 M z).2.1
  refine h.congr (fun N => ?_)
  refine eLpNorm_congr_ae ?_
  filter_upwards [hae] with t ht
  rw [forward_eq, hc, ht]

theorem poly_backward {M : ℕ} {p : SobolevHilbert 1} (hp : alInF38 M p) :
    Tendsto (fun N => eLpNorm (fun t => backwardStep N p t - alDeriv38 p t) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
  set z := physicalH1FiniteProjectionPlane M p with hz
  have hc : alCanon38 p = planeReal M z := funext fun s => alCanon_plane38 hp s
  have hae : alDeriv38 p =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] planeReal M (derivativePlane M z) := by
    filter_upwards [NlsGge.Birkhoff.alDeriv_plane38 hp] with t ht
    rw [ht, deriv_planeReal]
  have h := (NlsGge.Atomic.AL060.fixedTrigPolynomial_difference_L2_38 M z).2.2
  refine h.congr (fun N => ?_)
  refine eLpNorm_congr_ae ?_
  filter_upwards [hae] with t ht
  rw [backward_eq, hc, ht]

theorem conv_generic (T : ℕ → SobolevHilbert 1 → ℝ → ℂ)
    (hlin : ∀ N a b t, T N (a - b) t = T N a t - T N b t)
    (hmem : ∀ N y, alInF38 N y → MemLp (T N y) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hbd : ∀ N y, alInF38 N y → eLpNorm (T N y) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal ‖physicalH1DerivativeL2CLM y‖)
    (hpoly : ∀ M p, alInF38 M p → Tendsto (fun N => eLpNorm (fun t => T N p t - alDeriv38 p t) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0))
    (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1) (hF : ∀ N, alInF38 N (x N))
    (hx : Tendsto x atTop (𝓝 u)) :
    Tendsto (fun N => eLpNorm (fun t => T N (x N) t - alDeriv38 u t) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
  set μ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  obtain ⟨C, hCpos, hCb⟩ := (physicalH1DerivativeL2CLM).bound
  have hC0 : 0 ≤ C := hCpos.le
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact Eventually.of_forall fun N => by rw [htop]; exact le_top
  set e : ℝ := ε.toReal with he
  have hepos : 0 < e := ENNReal.toReal_pos hε.ne' htop
  have hεe : ε = ENNReal.ofReal e := (ENNReal.ofReal_toReal htop).symm
  set δ : ℝ := e / (6 * (C + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hCδ : C * δ ≤ e / 6 := by
    have h1 : δ * (C + 1) = e / 6 := by rw [hδ]; field_simp
    nlinarith
  -- choose the polynomial
  have hproj : ∀ᶠ M : ℕ in atTop, dist (physicalH1FiniteProjection M u) u < δ :=
    (Metric.tendsto_nhds.1 (physicalH1FiniteProjection_tendsto u)) δ hδpos
  obtain ⟨M, hM⟩ := hproj.exists
  set p := physicalH1FiniteProjection M u with hp
  have hpF : alInF38 M p := alProj_inF38 M u
  have hxu : ∀ᶠ N : ℕ in atTop, dist (x N) u < δ := (Metric.tendsto_nhds.1 hx) δ hδpos
  have hpoly' : ∀ᶠ N : ℕ in atTop, eLpNorm (fun t => T N p t - alDeriv38 p t) 2 μ <
      ENNReal.ofReal (e / 2) :=
    (hpoly M p hpF).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by positivity)))
  filter_upwards [eventually_ge_atTop M, hxu, hpoly'] with N hMN hxN hpN
  have hpFN : alInF38 N p := alInF_mono38 hMN p hpF
  have hdiffF : alInF38 N (x N - p) := alInF_sub38 N (x N) p (hF N) hpFN
  have hA := hmem N _ hdiffF
  have hB : MemLp (fun t => T N p t - alDeriv38 p t) 2 μ := (hmem N p hpFN).sub (alDeriv_memLp p)
  have hCC : MemLp (fun t => alDeriv38 p t - alDeriv38 u t) 2 μ :=
    (alDeriv_memLp p).sub (alDeriv_memLp u)
  have hsplit : (fun t => T N (x N) t - alDeriv38 u t) =
      (T N (x N - p) + (fun t => T N p t - alDeriv38 p t)) + (fun t => alDeriv38 p t - alDeriv38 u t) := by
    funext t
    simp only [Pi.add_apply, hlin]
    ring
  have h1 : eLpNorm (fun t => T N (x N) t - alDeriv38 u t) 2 μ ≤
      eLpNorm (T N (x N - p)) 2 μ + eLpNorm (fun t => T N p t - alDeriv38 p t) 2 μ +
        eLpNorm (fun t => alDeriv38 p t - alDeriv38 u t) 2 μ := by
    rw [hsplit]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    gcongr
    exact eLpNorm_add_le (by norm_num)
  have hnA : eLpNorm (T N (x N - p)) 2 μ ≤ ENNReal.ofReal (C * (2 * δ)) := by
    refine (hbd N _ hdiffF).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : ‖x N - p‖ ≤ 2 * δ := by
      have hM' : ‖p - u‖ < δ := by simpa [dist_eq_norm] using hM
      have hxN' : ‖x N - u‖ < δ := by simpa [dist_eq_norm] using hxN
      have a1 : ‖x N - p‖ ≤ ‖x N - u‖ + ‖p - u‖ := by
        calc ‖x N - p‖ = ‖(x N - u) - (p - u)‖ := by congr 1; abel
          _ ≤ ‖x N - u‖ + ‖p - u‖ := norm_sub_le _ _
      linarith
    calc ‖physicalH1DerivativeL2CLM (x N - p)‖ ≤ C * ‖x N - p‖ := hCb _
      _ ≤ C * (2 * δ) := mul_le_mul_of_nonneg_left h2 hC0
  have hnC : eLpNorm (fun t => alDeriv38 p t - alDeriv38 u t) 2 μ ≤ ENNReal.ofReal (C * δ) := by
    have hae : (fun t => alDeriv38 p t - alDeriv38 u t) =ᵐ[μ] alDeriv38 (p - u) :=
      (alDeriv_sub_ae p u).symm
    rw [eLpNorm_congr_ae hae, eLpNorm_alDeriv]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpu : ‖p - u‖ ≤ δ := by
      have hM' : ‖p - u‖ < δ := by simpa [dist_eq_norm] using hM
      exact hM'.le
    calc ‖physicalH1DerivativeL2CLM (p - u)‖ ≤ C * ‖p - u‖ := hCb _
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hpu hC0
  calc eLpNorm (fun t => T N (x N) t - alDeriv38 u t) 2 μ
      ≤ eLpNorm (T N (x N - p)) 2 μ + eLpNorm (fun t => T N p t - alDeriv38 p t) 2 μ +
        eLpNorm (fun t => alDeriv38 p t - alDeriv38 u t) 2 μ := h1
    _ ≤ ENNReal.ofReal (C * (2 * δ)) + ENNReal.ofReal (e / 2) + ENNReal.ofReal (C * δ) := by
        gcongr
    _ ≤ ε := by
        rw [hεe, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith

end AL061Aux

open AL061Aux in
theorem al061 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hF : ∀ N, alInF38 N (x N)) (hx : Tendsto x atTop (𝓝 u)) :
    (∀ N, MemLp (forwardStep N (x N)) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
      MemLp (backwardStep N (x N)) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
    MemLp (alDeriv38 u) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
    (∀ N : ℕ, ∀ t : ℝ,
      forwardStep N (x N) t + backwardStep N (x N) t =
        (sampleStep N 1 (x N) t - sampleStep N (-1) (x N) t) / (alh38 N : ℂ)) ∧
    Tendsto (fun N => eLpNorm
      (fun t : ℝ => forwardStep N (x N) t - alDeriv38 u t)
      2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) ∧
    Tendsto (fun N => eLpNorm
      (fun t : ℝ => backwardStep N (x N) t - alDeriv38 u t)
      2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) ∧
    Tendsto (fun N => eLpNorm
      (fun t : ℝ =>
        (sampleStep N 1 (x N) t - sampleStep N (-1) (x N) t) / (alh38 N : ℂ) -
        2 * alDeriv38 u t)
      2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
  have hsum : ∀ N : ℕ, ∀ t : ℝ,
      forwardStep N (x N) t + backwardStep N (x N) t =
        (sampleStep N 1 (x N) t - sampleStep N (-1) (x N) t) / (alh38 N : ℂ) := by
    intro N t
    have hh : (alh38 N : ℂ) ≠ 0 := by exact_mod_cast (alh38_pos N).ne'
    unfold forwardStep backwardStep sampleStep stepArray
    rw [alFd_sample38, alBd_sample38]
    simp only [Int.cast_one, Int.cast_neg, ← sub_eq_add_neg]
    field_simp
    ring
  have hfw : Tendsto (fun N => eLpNorm (fun t : ℝ => forwardStep N (x N) t - alDeriv38 u t) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) :=
    conv_generic (fun N y t => forwardStep N y t) forward_sub (fun N y hy => forward_memLp hy)
      (fun N y hy => forward_bound hy) (fun M p hp => poly_forward hp) x u hF hx
  have hbw : Tendsto (fun N => eLpNorm (fun t : ℝ => backwardStep N (x N) t - alDeriv38 u t) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) :=
    conv_generic (fun N y t => backwardStep N y t) backward_sub (fun N y hy => backward_memLp hy)
      (fun N y hy => backward_bound hy) (fun M p hp => poly_backward hp) x u hF hx
  refine ⟨fun N => ⟨forward_memLp (hF N), backward_memLp (hF N)⟩, alDeriv_memLp u, hsum, hfw, hbw, ?_⟩
  have hbound : ∀ N : ℕ, eLpNorm (fun t : ℝ =>
        (sampleStep N 1 (x N) t - sampleStep N (-1) (x N) t) / (alh38 N : ℂ) - 2 * alDeriv38 u t) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤
      eLpNorm (fun t : ℝ => forwardStep N (x N) t - alDeriv38 u t) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) +
      eLpNorm (fun t : ℝ => backwardStep N (x N) t - alDeriv38 u t) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro N
    have e : (fun t : ℝ =>
        (sampleStep N 1 (x N) t - sampleStep N (-1) (x N) t) / (alh38 N : ℂ) - 2 * alDeriv38 u t) =
        (fun t : ℝ => forwardStep N (x N) t - alDeriv38 u t) +
          (fun t : ℝ => backwardStep N (x N) t - alDeriv38 u t) := by
      funext t
      simp only [Pi.add_apply]
      rw [← hsum N t]
      ring
    rw [e]
    exact eLpNorm_add_le (by norm_num)
  have hz : Tendsto (fun N => eLpNorm (fun t : ℝ => forwardStep N (x N) t - alDeriv38 u t) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) +
      eLpNorm (fun t : ℝ => backwardStep N (x N) t - alDeriv38 u t) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
    simpa using hfw.add hbw
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun N => zero_le) hbound


end NlsGge.ThirdConsultation.AL
