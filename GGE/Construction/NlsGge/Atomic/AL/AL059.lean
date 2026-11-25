                                                                                                                                                                                                                                                                                      
import Mathlib
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALQ4Limit38

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

def stepArray (N : ℕ) (v : ZMod (2 * N + 1) → ℂ) (t : ℝ) : ℂ :=
  v ((Int.floor (t / alh38 N) : ℤ) : ZMod (2 * N + 1))

def forwardStep (N : ℕ) (u : SobolevHilbert 1) : ℝ → ℂ :=
  stepArray N (alFd38 N u)

def backwardStep (N : ℕ) (u : SobolevHilbert 1) : ℝ → ℂ :=
  stepArray N (alBd38 N u)

namespace AL059Aux

theorem sum_modes (N : ℕ) (f : ℤ → ℝ) :
    ∑ i : Fin (2 * N + 1), f (modeIndex N i) = ∑ k ∈ Finset.Icc (-(N : ℤ)) N, f k := by
  have himg : Finset.Icc (-(N : ℤ)) N = Finset.univ.image (modeIndex N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact modeIndex_covers N n h1 h2
    · rintro ⟨i, rfl⟩
      exact modeIndex_bounds N i
  rw [himg, Finset.sum_image (fun i _ j _ hij => modeIndex_injective N hij)]

theorem fd_sum (N : ℕ) (u : SobolevHilbert 1) (hu : alInF38 N u) :
    alh38 N * (∑ j, ‖alFd38 N u j‖ ^ 2) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, alomega38 N k ^ 2 * ‖alCoefH1_38 u k‖ ^ 2 := by
  have this : ∀ j, alFd38 N u j =
      (planeReal N (physicalH1FiniteProjectionPlane N u) (alt38 N j + alh38 N)
        - planeReal N (physicalH1FiniteProjectionPlane N u) (alt38 N j)) / (alh38 N : ℂ) := by
    intro j; unfold alFd38; rw [alCanon_plane38 hu, alCanon_plane38 hu]
  simp_rw [this]
  rw [parsevalFwd38]
  exact sum_modes N (fun k => alomega38 N k ^ 2 * ‖alCoefH1_38 u k‖ ^ 2)

theorem bd_sum (N : ℕ) (u : SobolevHilbert 1) (hu : alInF38 N u) :
    alh38 N * (∑ j, ‖alBd38 N u j‖ ^ 2) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, alomega38 N k ^ 2 * ‖alCoefH1_38 u k‖ ^ 2 := by
  have this : ∀ j, alBd38 N u j =
      (planeReal N (physicalH1FiniteProjectionPlane N u) (alt38 N j)
        - planeReal N (physicalH1FiniteProjectionPlane N u) (alt38 N j - alh38 N)) / (alh38 N : ℂ) := by
    intro j; unfold alBd38; rw [alCanon_plane38 hu, alCanon_plane38 hu]
  simp_rw [this]
  rw [parsevalBwd38]
  exact sum_modes N (fun k => alomega38 N k ^ 2 * ‖alCoefH1_38 u k‖ ^ 2)

theorem deriv_hasSum (u : SobolevHilbert 1) :
    HasSum (fun n : ℤ => (2 * Real.pi * |(n : ℝ)|) ^ 2 * ‖alCoefH1_38 u n‖ ^ 2)
      (‖physicalH1DerivativeL2CLM u‖ ^ 2) := by
  have h := hasSum_physicalFourier_sq (physicalH1DerivativeL2CLM u)
  convert h using 1
  funext n
  rw [physicalH1DerivativeL2CLM_apply, physicalH1FourierDerivativeClass_fourier, norm_mul,
    norm_fourierMultiplier, physicalH1CarrierToL2AfterAcceptedCoordinate_fourier]
  simp only [alCoefH1_38]
  ring

theorem sum_le_deriv (N : ℕ) (u : SobolevHilbert 1) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) N, alomega38 N k ^ 2 * ‖alCoefH1_38 u k‖ ^ 2 ≤
      ‖physicalH1DerivativeL2CLM u‖ ^ 2 := by
  have hs := deriv_hasSum u
  calc ∑ k ∈ Finset.Icc (-(N : ℤ)) N, alomega38 N k ^ 2 * ‖alCoefH1_38 u k‖ ^ 2
      ≤ ∑ k ∈ Finset.Icc (-(N : ℤ)) N, (2 * Real.pi * |(k : ℝ)|) ^ 2 * ‖alCoefH1_38 u k‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h := abs_alomega_le38 N k
        calc alomega38 N k ^ 2 = |alomega38 N k| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * Real.pi * |(k : ℝ)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ ≤ ‖physicalH1DerivativeL2CLM u‖ ^ 2 :=
        sum_le_hasSum _ (fun n _ => by positivity) hs

theorem step_integral (N : ℕ) (v : ZMod (2 * N + 1) → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖stepArray N v t‖ ^ 2) = alh38 N * ∑ j, ‖v j‖ ^ 2 := by
  have hh := alh38_pos N
  have hL : ((2 * N + 1 : ℕ) : ℝ) * alh38 N = 1 := by
    have := alh38_mul N; push_cast; linarith
  set h : ℝ := alh38 N with hhdef
  let F : ℝ → ℝ := fun t => ‖stepArray N v t‖ ^ 2
  have hpiece : ∀ j : ℕ, j < 2 * N + 1 →
      ∀ᵐ t ∂(volume.restrict (Set.Ioc ((j : ℝ) * h) (((j : ℝ) + 1) * h))),
        F t = ‖v ((j : ℕ) : ZMod (2 * N + 1))‖ ^ 2 := by
    intro j hj
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({((j : ℝ) + 1) * h} : Set ℝ) :=
      (Set.countable_singleton _).ae_notMem _
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne] with t ht hne'
    have hlt : t < ((j : ℝ) + 1) * h := lt_of_le_of_ne ht.2 hne'
    have hfl : Int.floor (t / h) = (j : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hh]; push_cast; exact ht.1.le
      · rw [div_lt_iff₀ hh]; push_cast; exact hlt
    simp only [F, stepArray]
    rw [hfl]
    simp
  have hint : ∀ j : ℕ, j < 2 * N + 1 →
      IntervalIntegrable F volume ((j : ℝ) * h) (((j : ℝ) + 1) * h) := by
    intro j hj
    have hle : (j : ℝ) * h ≤ ((j : ℝ) + 1) * h := by nlinarith
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    exact (integrable_const (‖v ((j : ℕ) : ZMod (2 * N + 1))‖ ^ 2)).congr
      (by
        filter_upwards [hpiece j hj] with t ht using ht.symm)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := F)
    (a := fun k : ℕ => (k : ℝ) * h) (n := 2 * N + 1)
    (fun k hk => by
      have := hint k hk
      simpa [Nat.cast_add, add_mul] using this)
  have hend : ((2 * N + 1 : ℕ) : ℝ) * h = 1 := hL
  simp only [Nat.cast_zero, zero_mul] at hsum
  rw [hend] at hsum
  rw [← hsum]
  have hval : ∀ j : ℕ, j < 2 * N + 1 →
      ∫ t in ((j : ℝ) * h)..(((j : ℝ) + 1) * h), F t = h * ‖v ((j : ℕ) : ZMod (2 * N + 1))‖ ^ 2 := by
    intro j hj
    have hle : (j : ℝ) * h ≤ ((j : ℝ) + 1) * h := by nlinarith
    rw [intervalIntegral.integral_of_le hle]
    rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc ?_ (g := fun _ => ‖v ((j : ℕ) : ZMod (2 * N + 1))‖ ^ 2)]
    · rw [setIntegral_const]
      simp only [Real.volume_real_Ioc_of_le hle, smul_eq_mul]
      congr 1; ring
    · filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 (hpiece j hj)] with t ht hmem using ht hmem
  have hrange : ∑ j : ZMod (2 * N + 1), ‖v j‖ ^ 2 = ∑ i ∈ Finset.range (2 * N + 1), ‖v ((i : ℕ) : ZMod (2 * N + 1))‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖v ((i : ℕ) : ZMod (2 * N + 1))‖ ^ 2) (2 * N + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg (fun x => ‖v x‖ ^ 2) (ZMod.natCast_zmod_val i).symm
  rw [hrange, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := hval j (Finset.mem_range.1 hj)
  simpa [Nat.cast_add, add_mul] using this

end AL059Aux

open AL059Aux

theorem al059 (N : ℕ) (u : SobolevHilbert 1) (hu : alInF38 N u) :
    alh38 N * (∑ j, ‖alFd38 N u j‖ ^ 2) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        alomega38 N k ^ 2 * ‖alCoefH1_38 u k‖ ^ 2 ∧
    alh38 N * (∑ j, ‖alBd38 N u j‖ ^ 2) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        alomega38 N k ^ 2 * ‖alCoefH1_38 u k‖ ^ 2 ∧
    alh38 N * (∑ j, ‖alFd38 N u j‖ ^ 2) ≤
      ‖physicalH1DerivativeL2CLM u‖ ^ 2 ∧
    alh38 N * (∑ j, ‖alBd38 N u j‖ ^ 2) ≤
      ‖physicalH1DerivativeL2CLM u‖ ^ 2 ∧
    (∫ t in (0 : ℝ)..1, ‖forwardStep N u t‖ ^ 2) =
      alh38 N * ∑ j, ‖alFd38 N u j‖ ^ 2 ∧
    (∫ t in (0 : ℝ)..1, ‖backwardStep N u t‖ ^ 2) =
      alh38 N * ∑ j, ‖alBd38 N u j‖ ^ 2 := by
  have hF := fd_sum N u hu
  have hB := bd_sum N u hu
  have hD := sum_le_deriv N u
  exact ⟨hF, hB, hF ▸ hD, hB ▸ hD, step_integral N _, step_integral N _⟩


end NlsGge.ThirdConsultation.AL
