import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.G1.G1015
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairVolterraDefs
import NlsGge.GK38.DirichletCounting
import NlsGge.GK38.PoissonMixedTargets
import NlsGge.GK38.PoissonMixedRealNormingData
import NlsGge.GK38.GradFundamentalPairing
import NlsGge.GK38.DirichletRealWinding
import NlsGge.GK38.GradEigenRealState
import NlsGge.Atomic.G1.G1019
import NlsGge.GK38.DirichletL2
import NlsGge.GK38.NeumannLabels
import NlsGge.Atomic.G1.G1060
import NlsGge.Atomic.G1.G1087

/- G1-061 landing kit (proof development review): S1's G1061_PROOF01 lines 5124-6143 with the private G1087_UNIFORM paste replaced by the landed G1-087 import. -/
/- ===== G1-061 proper (proof development) ===== -/

set_option autoImplicit false

namespace NlsGge.Atomic.G1061S1

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.Atomic.Volterra NlsGge.SpectralFoundations

noncomputable section

/-- the Volterra-series matrix `M(s, z)` -/
def Mser (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 :=
  ∑' m : ℕ, potentialVolterraTerm38 φ z m s

theorem Mser_eq_fundPair (φ : PotPair) (z : ℂ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Mser φ z s = fundPair φ z ⟨s, hs⟩ := by
  unfold Mser
  rw [NlsGge.Atomic.G1004GenT.tsum_terms_eq_fundContT φ z zero_le_one hs]
  rfl

theorem gcomp_eq (φ : PotPair) (z : ℂ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (i : Fin 2) :
    pairKernelExt38 (state φ z (![1, 1] : PairVec38)) s i =
      Mser φ z s i 0 + Mser φ z s i 1 := by
  rw [state_ext, ext38_of_mem _ hs, Mser_eq_fundPair φ z hs]
  simp [fundPair_eq, fundContP]
  rfl

theorem freeZs_00 (z : ℂ) (t : ℝ) :
    freeZsFundamentalComplex z t 0 0 = Complex.exp (↑t * (-Complex.I * z)) := by
  simp [freeZsFundamentalComplex, freeDiagonalCandidate, Matrix.diagonal_apply, Complex.real_smul]

theorem freeZs_11 (z : ℂ) (t : ℝ) :
    freeZsFundamentalComplex z t 1 1 = Complex.exp (↑t * (Complex.I * z)) := by
  simp [freeZsFundamentalComplex, freeDiagonalCandidate, Matrix.diagonal_apply, Complex.real_smul]

theorem freeZs_01 (z : ℂ) (t : ℝ) : freeZsFundamentalComplex z t 0 1 = 0 := by
  simp [freeZsFundamentalComplex, freeDiagonalCandidate, Matrix.diagonal_apply]

theorem freeZs_10 (z : ℂ) (t : ℝ) : freeZsFundamentalComplex z t 1 0 = 0 := by
  simp [freeZsFundamentalComplex, freeDiagonalCandidate, Matrix.diagonal_apply]

theorem norm_exp_sub_one_le_R {w : ℂ} {R : ℝ} (hw : ‖w‖ ≤ R) :
    ‖Complex.exp w - 1‖ ≤ (Real.exp R + 2) * ‖w‖ := by
  by_cases h1 : ‖w‖ ≤ 1
  · have := Complex.norm_exp_sub_one_le h1
    have hp : (0 : ℝ) ≤ Real.exp R := (Real.exp_pos R).le
    nlinarith [norm_nonneg w]
  · push_neg at h1
    have h2 : ‖Complex.exp w‖ ≤ Real.exp R := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm w).trans hw)
    have h3 : ‖Complex.exp w - 1‖ ≤ ‖Complex.exp w‖ + 1 := by
      simpa using norm_sub_le (Complex.exp w) 1
    nlinarith [norm_nonneg w, Real.exp_pos R]

theorem norm_e (r : ℝ) : ‖Complex.exp ((r : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I r

/-- exponential comparison, first diagonal entry -/
theorem exp_diff0 (n : ℤ) (ξ : ℂ) {t R : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hξ : ‖ξ - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R) :
    ‖Complex.exp (↑t * (-Complex.I * ξ)) - Complex.exp (-(Real.pi * n * t * Complex.I))‖ ≤
      (Real.exp R + 2) * ‖ξ - (n : ℂ) * (Real.pi : ℂ)‖ := by
  set δ : ℂ := ξ - (n : ℂ) * (Real.pi : ℂ) with hδ
  have e1 : Complex.exp (↑t * (-Complex.I * ξ)) =
      Complex.exp (-(Real.pi * n * t * Complex.I)) * Complex.exp (↑t * (-Complex.I * δ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hδ]; push_cast; ring
  have hn : ‖Complex.exp (-(Real.pi * n * t * Complex.I))‖ = 1 := by
    have := norm_e (-(Real.pi * n * t))
    simpa [Complex.ofReal_neg, neg_mul] using this
  have hw : ‖(↑t : ℂ) * (-Complex.I * δ)‖ ≤ R := by
    have : ‖(↑t : ℂ) * (-Complex.I * δ)‖ = t * ‖δ‖ := by
      simp [norm_mul, abs_of_nonneg ht0]
    rw [this]
    nlinarith [norm_nonneg δ]
  have h2 := norm_exp_sub_one_le_R hw
  have hw' : ‖(↑t : ℂ) * (-Complex.I * δ)‖ ≤ ‖δ‖ := by
    have : ‖(↑t : ℂ) * (-Complex.I * δ)‖ = t * ‖δ‖ := by
      simp [norm_mul, abs_of_nonneg ht0]
    rw [this]
    nlinarith [norm_nonneg δ]
  have hp : (0 : ℝ) < Real.exp R + 2 := by positivity
  calc ‖Complex.exp (↑t * (-Complex.I * ξ)) - Complex.exp (-(Real.pi * n * t * Complex.I))‖
      = ‖Complex.exp (-(Real.pi * n * t * Complex.I)) *
          (Complex.exp (↑t * (-Complex.I * δ)) - 1)‖ := by rw [e1]; ring_nf
    _ = ‖Complex.exp (↑t * (-Complex.I * δ)) - 1‖ := by rw [norm_mul, hn, one_mul]
    _ ≤ (Real.exp R + 2) * ‖(↑t : ℂ) * (-Complex.I * δ)‖ := h2
    _ ≤ (Real.exp R + 2) * ‖δ‖ := mul_le_mul_of_nonneg_left hw' hp.le

/-- exponential comparison, second diagonal entry -/
theorem exp_diff1 (n : ℤ) (ξ : ℂ) {t R : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hξ : ‖ξ - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R) :
    ‖Complex.exp (↑t * (Complex.I * ξ)) - Complex.exp (Real.pi * n * t * Complex.I)‖ ≤
      (Real.exp R + 2) * ‖ξ - (n : ℂ) * (Real.pi : ℂ)‖ := by
  set δ : ℂ := ξ - (n : ℂ) * (Real.pi : ℂ) with hδ
  have e1 : Complex.exp (↑t * (Complex.I * ξ)) =
      Complex.exp (Real.pi * n * t * Complex.I) * Complex.exp (↑t * (Complex.I * δ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hδ]; push_cast; ring
  have hn : ‖Complex.exp (Real.pi * n * t * Complex.I)‖ = 1 := by
    have := norm_e (Real.pi * n * t)
    simpa using this
  have hw' : ‖(↑t : ℂ) * (Complex.I * δ)‖ = t * ‖δ‖ := by
    simp [norm_mul, abs_of_nonneg ht0]
  have hw : ‖(↑t : ℂ) * (Complex.I * δ)‖ ≤ R := by
    rw [hw']
    nlinarith [norm_nonneg δ]
  have h2 := norm_exp_sub_one_le_R hw
  have hp : (0 : ℝ) < Real.exp R + 2 := by positivity
  have hw2 : ‖(↑t : ℂ) * (Complex.I * δ)‖ ≤ ‖δ‖ := by
    rw [hw']; nlinarith [norm_nonneg δ]
  calc ‖Complex.exp (↑t * (Complex.I * ξ)) - Complex.exp (Real.pi * n * t * Complex.I)‖
      = ‖Complex.exp (Real.pi * n * t * Complex.I) *
          (Complex.exp (↑t * (Complex.I * δ)) - 1)‖ := by rw [e1]; ring_nf
    _ = ‖Complex.exp (↑t * (Complex.I * δ)) - 1‖ := by rw [norm_mul, hn, one_mul]
    _ ≤ (Real.exp R + 2) * ‖(↑t : ℂ) * (Complex.I * δ)‖ := h2
    _ ≤ (Real.exp R + 2) * ‖δ‖ := mul_le_mul_of_nonneg_left hw2 hp.le


open scoped Matrix.Norms.L2Operator in
theorem norm_entry_le_l2 (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : ‖A i j‖ ≤ ‖A‖ := by
  classical
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have e1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  have e2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin 2) ℂ).symm
    (Matrix.mulVec A ⇑(EuclideanSpace.single j (1 : ℂ)))) i
  have e3 : ((EuclideanSpace.equiv (Fin 2) ℂ).symm (Matrix.mulVec A ⇑(EuclideanSpace.single j (1 : ℂ)))) i =
      A i j := by
    simp [Matrix.mulVec_single_one]
  rw [e3] at e2
  rw [e1, mul_one] at h
  exact e2.trans h

open scoped Matrix.Norms.L2Operator in
theorem eps0_bound (φ : PotPair) (ξ : ℂ) (n : ℤ) {t R : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hξ : ‖ξ - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R) :
    ‖(Mser φ ξ t 0 0 + Mser φ ξ t 0 1) - Complex.exp (-(Real.pi * n * t * Complex.I))‖ ≤
      2 * ‖Mser φ ξ t - freeZsFundamentalComplex ξ t‖ +
        (Real.exp R + 2) * ‖ξ - (n : ℂ) * (Real.pi : ℂ)‖ := by
  set D := Mser φ ξ t - freeZsFundamentalComplex ξ t with hD
  have h00 : Mser φ ξ t 0 0 = D 0 0 + Complex.exp (↑t * (-Complex.I * ξ)) := by
    rw [hD]; simp [freeZs_00]
  have h01 : Mser φ ξ t 0 1 = D 0 1 := by
    rw [hD]; simp [freeZs_01]
  have key : (Mser φ ξ t 0 0 + Mser φ ξ t 0 1) - Complex.exp (-(Real.pi * n * t * Complex.I)) =
      D 0 0 + D 0 1 + (Complex.exp (↑t * (-Complex.I * ξ)) -
        Complex.exp (-(Real.pi * n * t * Complex.I))) := by
    rw [h00, h01]; ring
  rw [key]
  have e := exp_diff0 n ξ ht0 ht1 hξ
  have a0 := norm_entry_le_l2 D 0 0
  have a1 := norm_entry_le_l2 D 0 1
  calc _ ≤ ‖D 0 0 + D 0 1‖ + ‖Complex.exp (↑t * (-Complex.I * ξ)) -
        Complex.exp (-(Real.pi * n * t * Complex.I))‖ := norm_add_le _ _
    _ ≤ (‖D 0 0‖ + ‖D 0 1‖) + (Real.exp R + 2) * ‖ξ - (n : ℂ) * (Real.pi : ℂ)‖ :=
        add_le_add (norm_add_le _ _) e
    _ ≤ _ := by linarith

open scoped Matrix.Norms.L2Operator in
theorem eps1_bound (φ : PotPair) (ξ : ℂ) (n : ℤ) {t R : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hξ : ‖ξ - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R) :
    ‖(Mser φ ξ t 1 0 + Mser φ ξ t 1 1) - Complex.exp (Real.pi * n * t * Complex.I)‖ ≤
      2 * ‖Mser φ ξ t - freeZsFundamentalComplex ξ t‖ +
        (Real.exp R + 2) * ‖ξ - (n : ℂ) * (Real.pi : ℂ)‖ := by
  set D := Mser φ ξ t - freeZsFundamentalComplex ξ t with hD
  have h10 : Mser φ ξ t 1 0 = D 1 0 := by
    rw [hD]; simp [freeZs_10]
  have h11 : Mser φ ξ t 1 1 = D 1 1 + Complex.exp (↑t * (Complex.I * ξ)) := by
    rw [hD]; simp [freeZs_11]
  have key : (Mser φ ξ t 1 0 + Mser φ ξ t 1 1) - Complex.exp (Real.pi * n * t * Complex.I) =
      D 1 0 + D 1 1 + (Complex.exp (↑t * (Complex.I * ξ)) -
        Complex.exp (Real.pi * n * t * Complex.I)) := by
    rw [h10, h11]; ring
  rw [key]
  have e := exp_diff1 n ξ ht0 ht1 hξ
  have a0 := norm_entry_le_l2 D 1 0
  have a1 := norm_entry_le_l2 D 1 1
  calc _ ≤ ‖D 1 0 + D 1 1‖ + ‖Complex.exp (↑t * (Complex.I * ξ)) -
        Complex.exp (Real.pi * n * t * Complex.I)‖ := norm_add_le _ _
    _ ≤ (‖D 1 0‖ + ‖D 1 1‖) + (Real.exp R + 2) * ‖ξ - (n : ℂ) * (Real.pi : ℂ)‖ :=
        add_le_add (norm_add_le _ _) e
    _ ≤ _ := by linarith


/-- the two component errors of the eigenfunction `M(t, ξ)[1,1]` against the lattice leading term. -/
def errsq (φ : PotPair) (ξ : ℤ → ℂ) (n : ℤ) (t : ℝ) : ℝ :=
  ‖(Mser φ (ξ n) t 0 0 + Mser φ (ξ n) t 0 1) - Complex.exp (-(Real.pi * n * t * Complex.I))‖ ^ 2 +
  ‖(Mser φ (ξ n) t 1 0 + Mser φ (ξ n) t 1 1) - Complex.exp (Real.pi * n * t * Complex.I)‖ ^ 2

theorem errsq_nonneg (φ : PotPair) (ξ : ℤ → ℂ) (n : ℤ) (t : ℝ) : 0 ≤ errsq φ ξ n t := by
  unfold errsq; positivity

open scoped Matrix.Norms.L2Operator in
theorem errsq_le (φ : PotPair) (ξ : ℤ → ℂ) (n : ℤ) {t R : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hξ : ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R) :
    errsq φ ξ n t ≤ 16 * ‖Mser φ (ξ n) t - freeZsFundamentalComplex (ξ n) t‖ ^ 2 +
      4 * (Real.exp R + 2) ^ 2 * ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 := by
  have h0 := eps0_bound φ (ξ n) n ht0 ht1 hξ
  have h1 := eps1_bound φ (ξ n) n ht0 ht1 hξ
  unfold errsq
  set D := ‖Mser φ (ξ n) t - freeZsFundamentalComplex (ξ n) t‖
  set K := Real.exp R + 2
  set d := ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖
  have hD : 0 ≤ D := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hK : 0 ≤ K := by positivity
  have s0 := sq_le_sq' (by nlinarith [norm_nonneg ((Mser φ (ξ n) t 0 0 + Mser φ (ξ n) t 0 1) - Complex.exp (-(Real.pi * n * t * Complex.I)))]) h0
  have s1 := sq_le_sq' (by nlinarith [norm_nonneg ((Mser φ (ξ n) t 1 0 + Mser φ (ξ n) t 1 1) - Complex.exp (Real.pi * n * t * Complex.I))]) h1
  nlinarith [sq_nonneg (2 * D - K * d), mul_nonneg hK hd]

open scoped Matrix.Norms.L2Operator in
theorem errsq_finite_sum (φ : PotPair) (ξ : ℤ → ℂ) {R1 C1 Cδ t : ℝ}
    (hξ : ∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1)
    (hS : Summable (fun n : ℤ => ‖Mser φ (ξ n) t - freeZsFundamentalComplex (ξ n) t‖ ^ 2))
    (hT : (∑' n : ℤ, ‖Mser φ (ξ n) t - freeZsFundamentalComplex (ξ n) t‖ ^ 2) ≤ C1)
    (hSd : Summable (fun n : ℤ => ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (hTd : (∑' n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ Cδ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (F : Finset ℤ) :
    ∑ n ∈ F, errsq φ ξ n t ≤ 16 * C1 + 4 * (Real.exp R1 + 2) ^ 2 * Cδ := by
  have h1 : ∑ n ∈ F, errsq φ ξ n t ≤
      ∑ n ∈ F, (16 * ‖Mser φ (ξ n) t - freeZsFundamentalComplex (ξ n) t‖ ^ 2 +
        4 * (Real.exp R1 + 2) ^ 2 * ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :=
    Finset.sum_le_sum fun n _ => errsq_le φ ξ n ht0 ht1 (hξ n)
  have h2 : ∑ n ∈ F, ‖Mser φ (ξ n) t - freeZsFundamentalComplex (ξ n) t‖ ^ 2 ≤ C1 :=
    (hS.sum_le_tsum F (fun _ _ => sq_nonneg _)).trans hT
  have h3 : ∑ n ∈ F, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 ≤ Cδ :=
    (hSd.sum_le_tsum F (fun _ _ => sq_nonneg _)).trans hTd
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  have hK : 0 ≤ 4 * (Real.exp R1 + 2) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hK]


/-- the canonical Dirichlet-type eigenfunction components `(M₁ + M₂)(s, z)` -/
def gv (φ : PotPair) (z : ℂ) (s : ℝ) (i : Fin 2) : ℂ :=
  pairKernelExt38 (state φ z (![1, 1] : PairVec38)) s i

theorem continuous_gv (φ : PotPair) (z : ℂ) (i : Fin 2) : Continuous (fun s => gv φ z s i) :=
  (continuous_apply i).comp (continuous_pairKernelExt38 _)

theorem errsq_eq_g (φ : PotPair) (ξ : ℤ → ℂ) (n : ℤ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    errsq φ ξ n s =
      ‖gv φ (ξ n) s 0 - Complex.exp (-(Real.pi * n * s * Complex.I))‖ ^ 2 +
      ‖gv φ (ξ n) s 1 - Complex.exp (Real.pi * n * s * Complex.I)‖ ^ 2 := by
  unfold errsq gv
  rw [gcomp_eq φ (ξ n) hs 0, gcomp_eq φ (ξ n) hs 1]

theorem sq_integral_le {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ s in (0 : ℝ)..1, f s) ^ 2 ≤ ∫ s in (0 : ℝ)..1, (f s) ^ 2 := by
  set c : ℝ := ∫ s in (0 : ℝ)..1, f s with hc
  have h0 : 0 ≤ ∫ s in (0 : ℝ)..1, (f s - c) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => sq_nonneg _)
  have hi1 : IntervalIntegrable (fun s => (f s) ^ 2) MeasureTheory.volume 0 1 :=
    (hf.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s => 2 * c * f s) MeasureTheory.volume 0 1 :=
    (continuous_const.mul hf).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun _ : ℝ => c ^ 2) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have e : ∫ s in (0 : ℝ)..1, (f s - c) ^ 2 =
      (∫ s in (0 : ℝ)..1, (f s) ^ 2) - 2 * c * c + c ^ 2 := by
    have e1 : (fun s => (f s - c) ^ 2) = fun s => ((f s) ^ 2 - 2 * c * f s) + c ^ 2 := by
      funext s; ring
    rw [e1, intervalIntegral.integral_add (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul]
    simp [hc]
  rw [e] at h0
  nlinarith

theorem summable_tsum_of_finite_sums {f : ℤ → ℝ} (hf : ∀ n, 0 ≤ f n) {C : ℝ}
    (h : ∀ F : Finset ℤ, ∑ n ∈ F, f n ≤ C) : Summable f ∧ ∑' n, f n ≤ C :=
  ⟨summable_of_sum_le hf h, (summable_of_sum_le hf h).tsum_le_of_sum_le h⟩

theorem sq_diff_le {g a : ℂ} {B : ℝ} (ha : ‖a‖ = 1) (hg : ‖g - a‖ ≤ B) :
    ‖g ^ 2 - a ^ 2‖ ≤ (2 + B) * ‖g - a‖ := by
  have e : g ^ 2 - a ^ 2 = (g - a) * (g + a) := by ring
  have h2 : ‖g + a‖ ≤ 2 + B := by
    have : g + a = (g - a) + 2 * a := by ring
    rw [this]
    calc ‖(g - a) + 2 * a‖ ≤ ‖g - a‖ + ‖2 * a‖ := norm_add_le _ _
      _ ≤ B + 2 := by rw [norm_mul, ha]; simp; linarith
      _ = 2 + B := by ring
  rw [e, norm_mul]
  calc ‖g - a‖ * ‖g + a‖ ≤ ‖g - a‖ * (2 + B) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = (2 + B) * ‖g - a‖ := by ring

theorem norm_e0 (n : ℤ) (s : ℝ) : ‖Complex.exp (-(Real.pi * n * s * Complex.I))‖ = 1 := by
  have := norm_e (-(Real.pi * n * s))
  simpa [Complex.ofReal_neg, neg_mul] using this

theorem norm_e1 (n : ℤ) (s : ℝ) : ‖Complex.exp (Real.pi * n * s * Complex.I)‖ = 1 := by
  have := norm_e (Real.pi * n * s)
  simpa using this

theorem e0_mul_e1 (n : ℤ) (s : ℝ) :
    Complex.exp (-(Real.pi * n * s * Complex.I)) * Complex.exp (Real.pi * n * s * Complex.I) = 1 := by
  rw [← Complex.exp_add]; simp


/-- continuous (g-form) version of `errsq`. -/
def errg (φ : PotPair) (ξ : ℤ → ℂ) (n : ℤ) (s : ℝ) : ℝ :=
  ‖gv φ (ξ n) s 0 - Complex.exp (-(Real.pi * n * s * Complex.I))‖ ^ 2 +
  ‖gv φ (ξ n) s 1 - Complex.exp (Real.pi * n * s * Complex.I)‖ ^ 2

theorem errg_nonneg (φ : PotPair) (ξ : ℤ → ℂ) (n : ℤ) (s : ℝ) : 0 ≤ errg φ ξ n s := by
  unfold errg; positivity

theorem continuous_errg (φ : PotPair) (ξ : ℤ → ℂ) (n : ℤ) : Continuous (errg φ ξ n) := by
  unfold errg
  have h0 : Continuous fun s : ℝ => Complex.exp (-(Real.pi * n * s * Complex.I)) := by fun_prop
  have h1 : Continuous fun s : ℝ => Complex.exp (Real.pi * n * s * Complex.I) := by fun_prop
  have := ((continuous_gv φ (ξ n) 0).sub h0).norm.pow 2
  have := (((continuous_gv φ (ξ n) 0).sub h0).norm.pow 2).add (((continuous_gv φ (ξ n) 1).sub h1).norm.pow 2)
  exact this

theorem errg_eq_errsq (φ : PotPair) (ξ : ℤ → ℂ) (n : ℤ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    errg φ ξ n s = errsq φ ξ n s := (errsq_eq_g φ ξ n hs).symm

/-- the pointwise-in-time sum bound, `errg` version, from `errsq_finite_sum`-type bounds. -/
theorem Q_sub_two_sq_le (φ : PotPair) (ξ : ℤ → ℂ) (n : ℤ) {Cε : ℝ} (hC : 0 ≤ Cε)
    (hpt : ∀ s ∈ Icc (0 : ℝ) 1, errg φ ξ n s ≤ Cε) :
    ‖Q (state φ (ξ n) (![1, 1] : PairVec38)) - 2‖ ^ 2 ≤
      8 * (1 + Real.sqrt Cε) ^ 2 * ∫ s in (0 : ℝ)..1, errg φ ξ n s := by
  set B := Real.sqrt Cε with hB
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  set a0 : ℝ → ℂ := fun s => Complex.exp (-(Real.pi * n * s * Complex.I)) with ha0
  set a1 : ℝ → ℂ := fun s => Complex.exp (Real.pi * n * s * Complex.I) with ha1
  set E0 : ℝ → ℝ := fun s => ‖gv φ (ξ n) s 0 - a0 s‖ with hE0
  set E1 : ℝ → ℝ := fun s => ‖gv φ (ξ n) s 1 - a1 s‖ with hE1
  have cE0 : Continuous E0 := by
    have h0 : Continuous a0 := by simp only [ha0]; fun_prop
    exact ((continuous_gv φ (ξ n) 0).sub h0).norm
  have cE1 : Continuous E1 := by
    have h1 : Continuous a1 := by simp only [ha1]; fun_prop
    exact ((continuous_gv φ (ξ n) 1).sub h1).norm
  have hE0B : ∀ s ∈ Icc (0 : ℝ) 1, E0 s ≤ B := by
    intro s hs
    have h := hpt s hs
    have : E0 s ^ 2 ≤ Cε := by
      have := errg_nonneg φ ξ n s
      unfold errg at h
      nlinarith [sq_nonneg (E1 s), sq_nonneg (‖gv φ (ξ n) s 1 - Complex.exp (Real.pi * n * s * Complex.I)‖)]
    rw [hB]
    exact Real.le_sqrt_of_sq_le this
  have hE1B : ∀ s ∈ Icc (0 : ℝ) 1, E1 s ≤ B := by
    intro s hs
    have h := hpt s hs
    have : E1 s ^ 2 ≤ Cε := by
      unfold errg at h
      nlinarith [sq_nonneg (‖gv φ (ξ n) s 0 - Complex.exp (-(Real.pi * n * s * Complex.I))‖)]
    rw [hB]
    exact Real.le_sqrt_of_sq_le this
  have hn0 : ∀ s, ‖a0 s‖ = 1 := fun s => norm_e0 n s
  have hn1 : ∀ s, ‖a1 s‖ = 1 := fun s => norm_e1 n s
  have hmul : ∀ s, a0 s * a1 s = 1 := fun s => e0_mul_e1 n s
  -- pointwise bound
  have hpw : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖gv φ (ξ n) s 0 * gv φ (ξ n) s 1 - 1‖ ≤ (1 + B) * (E0 s + E1 s) := by
    intro s hs
    have e : gv φ (ξ n) s 0 * gv φ (ξ n) s 1 - 1 =
        (gv φ (ξ n) s 0 - a0 s) * gv φ (ξ n) s 1 + a0 s * (gv φ (ξ n) s 1 - a1 s) := by
      have := hmul s
      linear_combination this
    have hg1 : ‖gv φ (ξ n) s 1‖ ≤ 1 + B := by
      have : gv φ (ξ n) s 1 = (gv φ (ξ n) s 1 - a1 s) + a1 s := by ring
      rw [this]
      calc ‖(gv φ (ξ n) s 1 - a1 s) + a1 s‖ ≤ ‖gv φ (ξ n) s 1 - a1 s‖ + ‖a1 s‖ := norm_add_le _ _
        _ ≤ B + 1 := by rw [hn1]; exact add_le_add (hE1B s hs) le_rfl
        _ = 1 + B := by ring
    rw [e]
    calc ‖(gv φ (ξ n) s 0 - a0 s) * gv φ (ξ n) s 1 + a0 s * (gv φ (ξ n) s 1 - a1 s)‖
        ≤ ‖(gv φ (ξ n) s 0 - a0 s) * gv φ (ξ n) s 1‖ + ‖a0 s * (gv φ (ξ n) s 1 - a1 s)‖ := norm_add_le _ _
      _ = E0 s * ‖gv φ (ξ n) s 1‖ + E1 s := by rw [norm_mul, norm_mul, hn0, one_mul]
      _ ≤ E0 s * (1 + B) + E1 s := by
          have := mul_le_mul_of_nonneg_left hg1 (norm_nonneg (gv φ (ξ n) s 0 - a0 s))
          linarith
      _ ≤ (1 + B) * (E0 s + E1 s) := by
          have : 0 ≤ E1 s := norm_nonneg _
          nlinarith
  -- Q - 2 as an integral
  have hG : Continuous fun s => gv φ (ξ n) s 0 * gv φ (ξ n) s 1 := (continuous_gv φ (ξ n) 0).mul (continuous_gv φ (ξ n) 1)
  have hQ : Q (state φ (ξ n) (![1, 1] : PairVec38)) - 2 =
      2 * ∫ s in (0 : ℝ)..1, (gv φ (ξ n) s 0 * gv φ (ξ n) s 1 - 1) := by
    have hi1 : IntervalIntegrable (fun s => gv φ (ξ n) s 0 * gv φ (ξ n) s 1) MeasureTheory.volume 0 1 :=
      hG.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) MeasureTheory.volume 0 1 := intervalIntegrable_const
    rw [intervalIntegral.integral_sub hi1 hi2]
    simp only [Q, gv, intervalIntegral.integral_const]
    simp; ring
  have hint : ‖∫ s in (0 : ℝ)..1, (gv φ (ξ n) s 0 * gv φ (ξ n) s 1 - 1)‖ ≤
      (1 + B) * ∫ s in (0 : ℝ)..1, (E0 s + E1 s) := by
    have hcont : Continuous fun s => gv φ (ξ n) s 0 * gv φ (ξ n) s 1 - 1 := hG.sub continuous_const
    calc ‖∫ s in (0 : ℝ)..1, (gv φ (ξ n) s 0 * gv φ (ξ n) s 1 - 1)‖
        ≤ ∫ s in (0 : ℝ)..1, ‖gv φ (ξ n) s 0 * gv φ (ξ n) s 1 - 1‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ s in (0 : ℝ)..1, (1 + B) * (E0 s + E1 s) :=
          intervalIntegral.integral_mono_on zero_le_one (hcont.norm.intervalIntegrable _ _)
            ((continuous_const.mul (cE0.add cE1)).intervalIntegrable _ _) hpw
      _ = (1 + B) * ∫ s in (0 : ℝ)..1, (E0 s + E1 s) := by
          rw [intervalIntegral.integral_const_mul]
  have hsq : (∫ s in (0 : ℝ)..1, (E0 s + E1 s)) ^ 2 ≤ ∫ s in (0 : ℝ)..1, (E0 s + E1 s) ^ 2 :=
    sq_integral_le (cE0.add cE1)
  have hle2 : ∫ s in (0 : ℝ)..1, (E0 s + E1 s) ^ 2 ≤ 2 * ∫ s in (0 : ℝ)..1, errg φ ξ n s := by
    have hc2 : Continuous fun s => (E0 s + E1 s) ^ 2 := (cE0.add cE1).pow 2
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one (hc2.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_errg φ ξ n)).intervalIntegrable _ _) (fun s hs => ?_)
    unfold errg
    nlinarith [sq_nonneg (E0 s - E1 s)]
  have hI0 : 0 ≤ ∫ s in (0 : ℝ)..1, (E0 s + E1 s) :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [hQ, norm_mul, Complex.norm_two]
  have h1 : (2 * ‖∫ s in (0 : ℝ)..1, (gv φ (ξ n) s 0 * gv φ (ξ n) s 1 - 1)‖) ^ 2 ≤
      (2 * ((1 + B) * ∫ s in (0 : ℝ)..1, (E0 s + E1 s))) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  refine h1.trans ?_
  have hB1 : 0 ≤ 1 + B := by linarith
  calc (2 * ((1 + B) * ∫ s in (0 : ℝ)..1, (E0 s + E1 s))) ^ 2
      = 4 * (1 + B) ^ 2 * (∫ s in (0 : ℝ)..1, (E0 s + E1 s)) ^ 2 := by ring
    _ ≤ 4 * (1 + B) ^ 2 * (2 * ∫ s in (0 : ℝ)..1, errg φ ξ n s) :=
        mul_le_mul_of_nonneg_left (hsq.trans hle2) (by positivity)
    _ = 8 * (1 + B) ^ 2 * ∫ s in (0 : ℝ)..1, errg φ ξ n s := by ring

/-- finite-sum (hence summable) bound for `Q_n - 2`, by exchanging the finite sum and the integral. -/
theorem Q_sub_two_finite_sum (φ : PotPair) (ξ : ℤ → ℂ) {Cε : ℝ} (hC : 0 ≤ Cε)
    (hpt : ∀ s ∈ Icc (0 : ℝ) 1, ∀ F : Finset ℤ, ∑ n ∈ F, errg φ ξ n s ≤ Cε) (F : Finset ℤ) :
    ∑ n ∈ F, ‖Q (state φ (ξ n) (![1, 1] : PairVec38)) - 2‖ ^ 2 ≤
      8 * (1 + Real.sqrt Cε) ^ 2 * Cε := by
  have h1 : ∀ n ∈ F, ‖Q (state φ (ξ n) (![1, 1] : PairVec38)) - 2‖ ^ 2 ≤
      8 * (1 + Real.sqrt Cε) ^ 2 * ∫ s in (0 : ℝ)..1, errg φ ξ n s := by
    intro n _
    refine Q_sub_two_sq_le φ ξ n hC (fun s hs => ?_)
    have := hpt s hs {n}
    simpa using this
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finset_sum
    (fun n _ => (continuous_errg φ ξ n).intervalIntegrable _ _)]
  have hint : ∫ s in (0 : ℝ)..1, ∑ n ∈ F, errg φ ξ n s ≤ ∫ s in (0 : ℝ)..1, Cε :=
    intervalIntegral.integral_mono_on zero_le_one
      (((continuous_finset_sum _ fun n _ => continuous_errg φ ξ n)).intervalIntegrable _ _)
      intervalIntegrable_const (fun s hs => hpt s hs F)
  have hc : ∫ s in (0 : ℝ)..1, Cε = Cε := by simp
  rw [hc] at hint
  exact mul_le_mul_of_nonneg_left hint (by positivity)


theorem grad_comp_le {Q s f : ℂ} (hQ : ‖Q - 2‖ ≤ 1 / 2) (hf : ‖f‖ = 1) :
    ‖Q⁻¹ * s - (1 / 2 : ℂ) * f‖ ^ 2 ≤ 2 * ‖s - f‖ ^ 2 + ‖Q - 2‖ ^ 2 / 2 := by
  have hQn : (3 / 2 : ℝ) ≤ ‖Q‖ := by
    have h := norm_sub_norm_le (2 : ℂ) Q
    rw [norm_sub_rev] at h
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have hQ0 : Q ≠ 0 := by intro h; rw [h] at hQn; norm_num at hQn
  have e : Q⁻¹ * s - (1 / 2 : ℂ) * f = Q⁻¹ * (s - f) + (Q⁻¹ - 1 / 2) * f := by ring
  have h1 : ‖Q⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have h2 : ‖Q⁻¹ - 1 / 2‖ ≤ ‖Q - 2‖ / 2 := by
    have e2 : Q⁻¹ - 1 / 2 = (2 - Q) / (2 * Q) := by field_simp
    rw [e2, norm_div, norm_mul, norm_sub_rev]
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h3]
    have hpos : 0 ≤ ‖Q - 2‖ := norm_nonneg _
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  rw [e]
  have h3 : ‖Q⁻¹ * (s - f) + (Q⁻¹ - 1 / 2) * f‖ ≤ ‖s - f‖ + ‖Q - 2‖ / 2 := by
    calc ‖Q⁻¹ * (s - f) + (Q⁻¹ - 1 / 2) * f‖ ≤ ‖Q⁻¹ * (s - f)‖ + ‖(Q⁻¹ - 1 / 2) * f‖ := norm_add_le _ _
      _ ≤ ‖s - f‖ + ‖Q - 2‖ / 2 := by
          rw [norm_mul, norm_mul, hf, mul_one]
          have := mul_le_mul h1 (le_refl ‖s - f‖) (norm_nonneg _) zero_le_one
          linarith
  have h4 : 0 ≤ ‖Q⁻¹ * (s - f) + (Q⁻¹ - 1 / 2) * f‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖s - f‖ - ‖Q - 2‖ / 2), norm_nonneg (s - f), norm_nonneg (Q - 2)]


theorem square_ext (w : PairKernelCont38) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    pairKernelExt38 (square w) s 0 = pairKernelExt38 w s 1 * pairKernelExt38 w s 1 ∧
    pairKernelExt38 (square w) s 1 = pairKernelExt38 w s 0 * pairKernelExt38 w s 0 := by
  have h := fun g : PairKernelCont38 => pairKernelExt38_of_mem g hs
  simp only [h]
  simp [square, starProd38]

theorem e1_sq (n : ℤ) (t : ℝ) :
    Complex.exp (Real.pi * n * t * Complex.I) ^ 2 =
      Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I) := by
  rw [pow_two, ← Complex.exp_add]; congr 1; ring

theorem e0_sq (n : ℤ) (t : ℝ) :
    Complex.exp (-(Real.pi * n * t * Complex.I)) ^ 2 =
      Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)) := by
  rw [pow_two, ← Complex.exp_add]; congr 1; ring

/-- the core analytic assembly for the Dirichlet-type eigenfunctions `M(·, ξ_n)[1,1]`. -/
theorem dirichlet_core (φ : PotPair) (ξ : ℤ → ℂ) {Cε : ℝ} (hC : 0 ≤ Cε)
    (hpt : ∀ s ∈ Icc (0 : ℝ) 1, ∀ F : Finset ℤ, ∑ n ∈ F, errg φ ξ n s ≤ Cε) (N : ℕ)
    (hQ : ∀ n : ℤ, N < n.natAbs →
      ‖Q (state φ (ξ n) (![1, 1] : PairVec38)) - 2‖ ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (Summable (fun n : ℤ => errg φ ξ n t) ∧ (∑' n : ℤ, errg φ ξ n t) ≤ Cε) ∧
    (Summable (fun n : ℤ =>
        ‖pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 0 -
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 1 -
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2) ∧
      (∑' n : ℤ,
        (‖pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 0 -
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 1 -
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2)) ≤
        (2 + Real.sqrt Cε) ^ 2 * Cε) ∧
    (∀ n : ℤ, N < n.natAbs → Q (state φ (ξ n) (![1, 1] : PairVec38)) ≠ 0) ∧
    (Summable (fun n : ℤ => if N < n.natAbs then
        ‖(Q (state φ (ξ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 0 -
          (1 / 2 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (ξ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 1 -
          (1 / 2 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then
        ‖(Q (state φ (ξ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 0 -
          (1 / 2 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (ξ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 1 -
          (1 / 2 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) ≤
        2 * (2 + Real.sqrt Cε) ^ 2 * Cε + 8 * (1 + Real.sqrt Cε) ^ 2 * Cε) := by
  set B := Real.sqrt Cε with hB
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hfin : ∀ F : Finset ℤ, ∑ n ∈ F, errg φ ξ n t ≤ Cε := hpt t ht
  have hn1 : ∀ n, errg φ ξ n t ≤ Cε := fun n => by simpa using hfin {n}
  have hε0 : ∀ n, ‖gv φ (ξ n) t 0 - Complex.exp (-(Real.pi * n * t * Complex.I))‖ ≤ B := by
    intro n
    have h := hn1 n
    unfold errg at h
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖gv φ (ξ n) t 1 - Complex.exp (Real.pi * n * t * Complex.I)‖])
  have hε1 : ∀ n, ‖gv φ (ξ n) t 1 - Complex.exp (Real.pi * n * t * Complex.I)‖ ≤ B := by
    intro n
    have h := hn1 n
    unfold errg at h
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖gv φ (ξ n) t 0 - Complex.exp (-(Real.pi * n * t * Complex.I))‖])
  -- squares
  have hsq : ∀ n, ‖pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 0 -
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 1 -
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2 ≤
        (2 + B) ^ 2 * errg φ ξ n t := by
    intro n
    obtain ⟨s0, s1⟩ := square_ext (state φ (ξ n) (![1, 1] : PairVec38)) ht
    rw [s0, s1, ← e1_sq, ← e0_sq]
    have a0 := sq_diff_le (g := gv φ (ξ n) t 0) (a := Complex.exp (-(Real.pi * n * t * Complex.I))) (norm_e0 n t) (hε0 n)
    have a1 := sq_diff_le (g := gv φ (ξ n) t 1) (a := Complex.exp (Real.pi * n * t * Complex.I)) (norm_e1 n t) (hε1 n)
    have c0 : ‖gv φ (ξ n) t 1 * gv φ (ξ n) t 1 - Complex.exp (Real.pi * n * t * Complex.I) ^ 2‖ ≤
        (2 + B) * ‖gv φ (ξ n) t 1 - Complex.exp (Real.pi * n * t * Complex.I)‖ := by
      rw [← pow_two]; exact a1
    have c1 : ‖gv φ (ξ n) t 0 * gv φ (ξ n) t 0 - Complex.exp (-(Real.pi * n * t * Complex.I)) ^ 2‖ ≤
        (2 + B) * ‖gv φ (ξ n) t 0 - Complex.exp (-(Real.pi * n * t * Complex.I))‖ := by
      rw [← pow_two]; exact a0
    unfold errg gv at *
    have hp : 0 ≤ (2 + B) := by linarith
    nlinarith [mul_le_mul c0 c0 (norm_nonneg _) (by positivity), mul_le_mul c1 c1 (norm_nonneg _) (by positivity),
      sq_nonneg ‖pairKernelExt38 (state φ (ξ n) (![1, 1] : PairVec38)) t 0 - Complex.exp (-(Real.pi * n * t * Complex.I))‖,
      sq_nonneg ‖pairKernelExt38 (state φ (ξ n) (![1, 1] : PairVec38)) t 1 - Complex.exp (Real.pi * n * t * Complex.I)‖]
  -- (i)
  have p1 := summable_tsum_of_finite_sums (f := fun n => errg φ ξ n t)
    (fun n => errg_nonneg φ ξ n t) hfin
  -- (ii)
  set sqn : ℤ → ℝ := fun n =>
    ‖pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 0 -
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 1 -
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2 with hsqn
  have hsqn0 : ∀ n, 0 ≤ sqn n := fun n => by simp only [hsqn]; positivity
  have hsq_fin : ∀ F : Finset ℤ, ∑ n ∈ F, sqn n ≤ (2 + B) ^ 2 * Cε := by
    intro F
    calc ∑ n ∈ F, sqn n ≤ ∑ n ∈ F, (2 + B) ^ 2 * errg φ ξ n t := Finset.sum_le_sum fun n _ => hsq n
      _ = (2 + B) ^ 2 * ∑ n ∈ F, errg φ ξ n t := by rw [Finset.mul_sum]
      _ ≤ (2 + B) ^ 2 * Cε := mul_le_mul_of_nonneg_left (hfin F) (by positivity)
  have p2 := summable_tsum_of_finite_sums hsqn0 hsq_fin
  -- (iii)
  have hQne : ∀ n : ℤ, N < n.natAbs → Q (state φ (ξ n) (![1, 1] : PairVec38)) ≠ 0 := by
    intro n hn h0
    have := hQ n hn
    rw [h0] at this
    norm_num at this
  -- (iv)
  have hQ2 := Q_sub_two_finite_sum φ ξ hC hpt
  set gn : ℤ → ℝ := fun n => if N < n.natAbs then
        ‖(Q (state φ (ξ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 0 -
          (1 / 2 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (ξ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 1 -
          (1 / 2 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0 with hgn
  have hgn0 : ∀ n, 0 ≤ gn n := fun n => by
    simp only [hgn]; split_ifs <;> positivity
  have hgn_le : ∀ n, gn n ≤ 2 * sqn n +
      ‖Q (state φ (ξ n) (![1, 1] : PairVec38)) - 2‖ ^ 2 := by
    intro n
    simp only [hgn]
    split_ifs with hn
    · have hQn := hQ n hn
      have a0 := grad_comp_le (s := pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 0)
        (f := Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)) hQn (by
          rw [← e1_sq]; rw [norm_pow, norm_e1]; norm_num)
      have a1 := grad_comp_le (s := pairKernelExt38 (square (state φ (ξ n) (![1, 1] : PairVec38))) t 1)
        (f := Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))) hQn (by
          rw [← e0_sq]; rw [norm_pow, norm_e0]; norm_num)
      simp only [hsqn]
      linarith
    · have := hsqn0 n
      positivity
  have hgn_fin : ∀ F : Finset ℤ, ∑ n ∈ F, gn n ≤
      2 * (2 + B) ^ 2 * Cε + 8 * (1 + B) ^ 2 * Cε := by
    intro F
    calc ∑ n ∈ F, gn n ≤ ∑ n ∈ F, (2 * sqn n + ‖Q (state φ (ξ n) (![1, 1] : PairVec38)) - 2‖ ^ 2) :=
          Finset.sum_le_sum fun n _ => hgn_le n
      _ = 2 * ∑ n ∈ F, sqn n + ∑ n ∈ F, ‖Q (state φ (ξ n) (![1, 1] : PairVec38)) - 2‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * ((2 + B) ^ 2 * Cε) + 8 * (1 + B) ^ 2 * Cε :=
          add_le_add (mul_le_mul_of_nonneg_left (hsq_fin F) (by norm_num)) (hQ2 F)
      _ = 2 * (2 + B) ^ 2 * Cε + 8 * (1 + B) ^ 2 * Cε := by ring
  have p4 := summable_tsum_of_finite_sums hgn0 hgn_fin
  exact ⟨p1, p2, hQne, p4⟩


/-- the Dirichlet part, assuming the uniform smallness of `Q_n - 2` (S2's `Q_small`) as a hypothesis `hQs`. -/
theorem dirichlet_main (φ₀ : PotPair)
    (hQs : ∃ V₃ : Set PotPair, V₃ ∈ 𝓝 φ₀ ∧ ∃ N₃ : ℕ, ∀ ψ ∈ V₃, ∀ n : ℤ, N₃ < n.natAbs →
      ‖Q (state ψ (muSeq ψ n) (![1, 1] : PairVec38)) - 2‖ ≤ 1 / 2) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, ∃ C : ℝ, ∀ φ ∈ V, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      ((Summable (fun n : ℤ => errg φ (muSeq φ) n t) ∧ (∑' n : ℤ, errg φ (muSeq φ) n t) ≤ C) ∧
      (Summable (fun n : ℤ =>
        ‖pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 0 -
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 1 -
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2) ∧
      (∑' n : ℤ,
        (‖pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 0 -
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 1 -
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2)) ≤ C) ∧
      (∀ n : ℤ, N < n.natAbs → Q (state φ (muSeq φ n) (![1, 1] : PairVec38)) ≠ 0) ∧
      (Summable (fun n : ℤ => if N < n.natAbs then
        ‖(Q (state φ (muSeq φ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 0 -
          (1 / 2 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (muSeq φ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 1 -
          (1 / 2 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then
        ‖(Q (state φ (muSeq φ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 0 -
          (1 / 2 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (muSeq φ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 1 -
          (1 / 2 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) ≤ C)) := by
  obtain ⟨U₁, hU₁, N₁, -, hloc⟩ := muSeq_local_bounds38 φ₀
  obtain ⟨U₂, hU₂, Cδ, hCδ0, hl2⟩ := muSeq_local_l2_38 φ₀
  obtain ⟨V₃, hV₃, N₃, hQ3⟩ := hQs
  set b : ℝ := 2 * (N₁ : ℝ) * Real.pi + Real.pi / 4 with hb
  set R0 : ℝ := ‖φ₀.1‖ + ‖φ₀.2‖ + 2 with hR0
  obtain ⟨C1, hC1⟩ := NlsGge.Atomic.G1019S1.G1019_whole R0 b
  set Cε : ℝ := max (16 * C1 + 4 * (Real.exp b + 2) ^ 2 * Cδ) 0 with hCε
  have hCε0 : 0 ≤ Cε := le_max_right _ _
  set B : ℝ := Real.sqrt Cε with hB
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  refine ⟨U₁ ∩ U₂ ∩ V₃ ∩ Metric.ball φ₀ 1, ?_, N₃,
    Cε + (2 + B) ^ 2 * Cε + 2 * (2 + B) ^ 2 * Cε + 8 * (1 + B) ^ 2 * Cε, ?_⟩
  · exact inter_mem (inter_mem (inter_mem hU₁ hU₂) hV₃) (Metric.ball_mem_nhds φ₀ one_pos)
  intro φ hφ t ht
  obtain ⟨⟨⟨hφ1, hφ2⟩, hφ3⟩, hφ4⟩ := hφ
  have hnorm : Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ R0 := by
    have hd : ‖φ - φ₀‖ < 1 := mem_ball_iff_norm.mp hφ4
    have h1 : ‖φ.1‖ ≤ ‖φ₀.1‖ + 1 := by
      have := norm_fst_le (φ - φ₀)
      have e : (φ - φ₀).1 = φ.1 - φ₀.1 := rfl
      rw [e] at this
      have := norm_le_insert' φ.1 φ₀.1
      have h2 : ‖φ.1 - φ₀.1‖ ≤ ‖φ - φ₀‖ := by
        have := norm_fst_le (φ - φ₀)
        simpa using this
      linarith
    have h2 : ‖φ.2‖ ≤ ‖φ₀.2‖ + 1 := by
      have := norm_le_insert' φ.2 φ₀.2
      have h3 : ‖φ.2 - φ₀.2‖ ≤ ‖φ - φ₀‖ := by
        have := norm_snd_le (φ - φ₀)
        simpa using this
      linarith
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [norm_nonneg φ.1, norm_nonneg φ.2, norm_nonneg φ₀.1, norm_nonneg φ₀.2]
  have hξ : ∀ n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ b := fun n => (hloc φ hφ1 n).1
  obtain ⟨hSδ, hTδ⟩ := hl2 φ hφ2
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1, ∀ F : Finset ℤ, ∑ n ∈ F, errg φ (muSeq φ) n s ≤ Cε := by
    intro s hs F
    obtain ⟨hS, hT⟩ := hC1 φ (muSeq φ) hnorm hξ s hs.1 hs.2
    have h1 := errsq_finite_sum φ (muSeq φ) (R1 := b) (C1 := C1) (Cδ := Cδ) hξ hS hT hSδ hTδ hs.1 hs.2 F
    have h2 : ∑ n ∈ F, errg φ (muSeq φ) n s = ∑ n ∈ F, errsq φ (muSeq φ) n s :=
      Finset.sum_congr rfl fun n _ => errg_eq_errsq φ (muSeq φ) n hs
    rw [h2]
    exact h1.trans (le_max_left _ _)
  have hQ' : ∀ n : ℤ, N₃ < n.natAbs →
      ‖Q (state φ (muSeq φ n) (![1, 1] : PairVec38)) - 2‖ ≤ 1 / 2 := fun n hn => hQ3 φ hφ3 n hn
  obtain ⟨⟨p1, p1'⟩, ⟨p2, p2'⟩, p3, ⟨p4, p4'⟩⟩ := dirichlet_core φ (muSeq φ) hCε0 hpt N₃ hQ' ht
  have e1 : 0 ≤ (2 + B) ^ 2 * Cε := by positivity
  have e2 : 0 ≤ 2 * (2 + B) ^ 2 * Cε := by positivity
  have e3 : 0 ≤ 8 * (1 + B) ^ 2 * Cε := by positivity
  refine ⟨⟨p1, by linarith⟩, ⟨p2, by linarith⟩, p3, ⟨p4, by linarith⟩⟩


theorem neu_comp (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pairKernelExt38 (state φ z (![Complex.I, -Complex.I] : PairVec38)) t 0 =
        Complex.I * pairKernelExt38 (state (-φ) z (![1, 1] : PairVec38)) t 0 ∧
    pairKernelExt38 (state φ z (![Complex.I, -Complex.I] : PairVec38)) t 1 =
        -Complex.I * pairKernelExt38 (state (-φ) z (![1, 1] : PairVec38)) t 1 := by
  have h := fun g : PairKernelCont38 => pairKernelExt38_of_mem g ht
  simp only [h]
  have h0 := NlsGge.GK38.SimpleBoundary38.complex_neumann_state_gauge φ z ⟨t, ht⟩ 0
  have h1 := NlsGge.GK38.SimpleBoundary38.complex_neumann_state_gauge φ z ⟨t, ht⟩ 1
  simp only [NlsGge.GK38.gaugeSign38] at h0 h1
  refine ⟨?_, ?_⟩
  · simpa using h0
  · simpa using h1

theorem neu_square (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin 2) :
    pairKernelExt38 (square (state φ z (![Complex.I, -Complex.I] : PairVec38))) t i =
      -pairKernelExt38 (square (state (-φ) z (![1, 1] : PairVec38))) t i := by
  have h := fun g : PairKernelCont38 => pairKernelExt38_of_mem g ht
  simp only [h]
  rw [NlsGge.GK38.SimpleBoundary38.complex_neumann_square φ z]
  simp

theorem neu_Q (φ : PotPair) (z : ℂ) :
    Q (state φ z (![Complex.I, -Complex.I] : PairVec38)) =
      Q (state (-φ) z (![1, 1] : PairVec38)) := NlsGge.GK38.SimpleBoundary38.complex_neumann_Q φ z

/-- the Dirichlet-type clauses, as a predicate (explicit expressions; used only to organise the transfer). -/
theorem neumann_main (φ₀ : PotPair)
    (hQs : ∃ V₃ : Set PotPair, V₃ ∈ 𝓝 (-φ₀) ∧ ∃ N₃ : ℕ, ∀ ψ ∈ V₃, ∀ n : ℤ, N₃ < n.natAbs →
      ‖Q (state ψ (muSeq ψ n) (![1, 1] : PairVec38)) - 2‖ ≤ 1 / 2) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, ∃ C : ℝ, ∀ φ ∈ V, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      ((Summable (fun n : ℤ =>
        ‖pairKernelExt38 (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) t 0 -
          Complex.I * Complex.exp (-(Real.pi * n * t * Complex.I))‖ ^ 2 +
        ‖pairKernelExt38 (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) t 1 -
          (-Complex.I) * Complex.exp (Real.pi * n * t * Complex.I)‖ ^ 2) ∧
      (∑' n : ℤ,
        (‖pairKernelExt38 (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) t 0 -
          Complex.I * Complex.exp (-(Real.pi * n * t * Complex.I))‖ ^ 2 +
        ‖pairKernelExt38 (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) t 1 -
          (-Complex.I) * Complex.exp (Real.pi * n * t * Complex.I)‖ ^ 2)) ≤ C) ∧
      (Summable (fun n : ℤ =>
        ‖pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 0 -
          (-Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 1 -
          (-Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)))‖ ^ 2) ∧
      (∑' n : ℤ,
        (‖pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 0 -
          (-Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 1 -
          (-Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)))‖ ^ 2)) ≤ C) ∧
      (∀ n : ℤ, N < n.natAbs →
        Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) ≠ 0) ∧
      (Summable (fun n : ℤ => if N < n.natAbs then
        ‖(Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 0 -
          (-(1 / 2 : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 1 -
          (-(1 / 2 : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then
        ‖(Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 0 -
          (-(1 / 2 : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 1 -
          (-(1 / 2 : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) ≤ C)) := by
  obtain ⟨V', hV', N, C, H⟩ := dirichlet_main (-φ₀) hQs
  refine ⟨(fun φ : PotPair => -φ) ⁻¹' V', continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV'),
    N, C, fun φ hφ t ht => ?_⟩
  obtain ⟨⟨p1, p1'⟩, ⟨p2, p2'⟩, p3, ⟨p4, p4'⟩⟩ := H (-φ) hφ t ht
  have k1 : ∀ n : ℤ,
      (‖pairKernelExt38 (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) t 0 -
          Complex.I * Complex.exp (-(Real.pi * n * t * Complex.I))‖ ^ 2 +
        ‖pairKernelExt38 (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) t 1 -
          (-Complex.I) * Complex.exp (Real.pi * n * t * Complex.I)‖ ^ 2) =
        errg (-φ) (muSeq (-φ)) n t := by
    intro n
    obtain ⟨c0, c1⟩ := neu_comp φ (nuSeq38 φ n) ht
    rw [c0, c1]
    unfold errg gv
    have e0 : Complex.I * pairKernelExt38 (state (-φ) (nuSeq38 φ n) (![1, 1] : PairVec38)) t 0 -
        Complex.I * Complex.exp (-(Real.pi * n * t * Complex.I)) =
        Complex.I * (pairKernelExt38 (state (-φ) (nuSeq38 φ n) (![1, 1] : PairVec38)) t 0 -
          Complex.exp (-(Real.pi * n * t * Complex.I))) := by ring
    have e1 : -Complex.I * pairKernelExt38 (state (-φ) (nuSeq38 φ n) (![1, 1] : PairVec38)) t 1 -
        (-Complex.I) * Complex.exp (Real.pi * n * t * Complex.I) =
        -Complex.I * (pairKernelExt38 (state (-φ) (nuSeq38 φ n) (![1, 1] : PairVec38)) t 1 -
          Complex.exp (Real.pi * n * t * Complex.I)) := by ring
    rw [e0, e1, norm_mul, norm_mul, norm_neg, Complex.norm_I]
    simp [nuSeq38]
  have k2 : ∀ n : ℤ,
      (‖pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 0 -
          (-Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 1 -
          (-Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)))‖ ^ 2) =
        (‖pairKernelExt38 (square (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38))) t 0 -
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖pairKernelExt38 (square (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38))) t 1 -
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2) := by
    intro n
    have a0 := neu_square φ (nuSeq38 φ n) ht 0
    have a1 := neu_square φ (nuSeq38 φ n) ht 1
    rw [a0, a1]
    have e0 : -pairKernelExt38 (square (state (-φ) (nuSeq38 φ n) (![1, 1] : PairVec38))) t 0 -
        (-Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)) =
        -(pairKernelExt38 (square (state (-φ) (nuSeq38 φ n) (![1, 1] : PairVec38))) t 0 -
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)) := by ring
    have e1 : -pairKernelExt38 (square (state (-φ) (nuSeq38 φ n) (![1, 1] : PairVec38))) t 1 -
        (-Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))) =
        -(pairKernelExt38 (square (state (-φ) (nuSeq38 φ n) (![1, 1] : PairVec38))) t 1 -
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))) := by ring
    rw [e0, e1, norm_neg, norm_neg]
    rfl
  have k3 : ∀ n : ℤ, Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) =
      Q (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38)) := fun n => neu_Q φ (nuSeq38 φ n)
  have k4 : ∀ n : ℤ,
      (if N < n.natAbs then
        ‖(Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 0 -
          (-(1 / 2 : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 1 -
          (-(1 / 2 : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) =
      (if N < n.natAbs then
        ‖(Q (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38))) t 0 -
          (1 / 2 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38))) t 1 -
          (1 / 2 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) := by
    intro n
    split_ifs with hn
    · rw [k3 n, neu_square φ (nuSeq38 φ n) ht 0, neu_square φ (nuSeq38 φ n) ht 1]
      have e0 : (Q (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38)))⁻¹ *
            -pairKernelExt38 (square (state (-φ) (nuSeq38 φ n) (![1, 1] : PairVec38))) t 0 -
          (-(1 / 2 : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I) =
          -((Q (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38))) t 0 -
          (1 / 2 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)) := by
        simp only [nuSeq38]; ring
      have e1 : (Q (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38)))⁻¹ *
            -pairKernelExt38 (square (state (-φ) (nuSeq38 φ n) (![1, 1] : PairVec38))) t 1 -
          (-(1 / 2 : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)) =
          -((Q (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state (-φ) (muSeq (-φ) n) (![1, 1] : PairVec38))) t 1 -
          (1 / 2 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))) := by
        simp only [nuSeq38]; ring
      rw [e0, e1, norm_neg, norm_neg]
    · rfl
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · simpa only [k1] using p1
  · simpa only [k1] using p1'
  · simpa only [k2] using p2
  · simpa only [k2] using p2'
  · intro n hn
    rw [k3 n]; exact p3 n hn
  · simpa only [k4] using p4
  · simpa only [k4] using p4'


/-- `μ_n` is a simple Dirichlet eigenvalue as soon as `Q(g_n) ≠ 0` (exported helper, not part of the main statement). -/
theorem muSeq_simple_of_Q_ne_zero (φ : PotPair) (n : ℤ)
    (hQ : Q (state φ (muSeq φ n) (![1, 1] : PairVec38)) ≠ 0) :
    NlsGge.GK38.SimpleBoundary38.IsSimpleBoundaryEigenvalue
      NlsGge.GK38.SimpleBoundary38.dirichletProblem φ (muSeq φ n) := by
  have hroot : dirichletChar φ (muSeq φ n) = 0 := muSeq_root38 φ n
  have hd : deriv (dirichletChar φ) (muSeq φ n) ≠ 0 := by
    intro h0
    have hrel := dirichlet_Q_spectral_relation φ (muSeq φ n) hroot
    rw [h0, mul_zero] at hrel
    have hm : monodromyPair φ (muSeq φ n) 1 1 - monodromyPair φ (muSeq φ n) 0 1 = 0 :=
      (mul_eq_zero.mp hrel).resolve_right hQ
    have hdet := det_monodromyPair φ (muSeq φ n)
    rw [Matrix.det_fin_two] at hdet
    have hr : monodromyPair φ (muSeq φ n) 1 0 + monodromyPair φ (muSeq φ n) 1 1 -
        monodromyPair φ (muSeq φ n) 0 0 - monodromyPair φ (muSeq φ n) 0 1 = 0 := by
      have h := hroot
      rw [dirichletChar_eq] at h
      have h2 : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
      have := (div_eq_zero_iff.mp h).resolve_right h2
      linear_combination this
    have e1 : monodromyPair φ (muSeq φ n) 1 1 = monodromyPair φ (muSeq φ n) 0 1 := by
      linear_combination hm
    have e2 : monodromyPair φ (muSeq φ n) 1 0 = monodromyPair φ (muSeq φ n) 0 0 := by
      linear_combination hr - e1
    rw [e1, e2] at hdet
    have : (1 : ℂ) = 0 := by rw [← hdet]; ring
    exact one_ne_zero this
  exact (NlsGge.GK38.SimpleBoundary38.simple_boundary_iff
    NlsGge.GK38.SimpleBoundary38.dirichletProblem φ (muSeq φ n)).mpr ⟨hroot, hd⟩

/-- the Neumann analogue. -/
theorem nuSeq_simple_of_Q_ne_zero (φ : PotPair) (n : ℤ)
    (hQ : Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) ≠ 0) :
    NlsGge.GK38.SimpleBoundary38.IsSimpleBoundaryEigenvalue
      NlsGge.GK38.SimpleBoundary38.neumannProblem φ (nuSeq38 φ n) := by
  have h := muSeq_simple_of_Q_ne_zero (-φ) n (by have h := neu_Q φ (nuSeq38 φ n); rw [h] at hQ; exact hQ)
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · show neumannChar38 φ (nuSeq38 φ n) = 0
    rw [neumannChar38_eq_dirichlet_neg]; exact h1
  · show analyticOrderAt (neumannChar38 φ) (nuSeq38 φ n) = 1
    rw [neumannChar38_fun_eq_dirichlet_neg]; exact h2

end

end NlsGge.Atomic.G1061S1


namespace NlsGge.Atomic.G1061S1

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GK38.GradEigen38

noncomputable section

/-- G1-061 (Lemma 7.6), Dirichlet part. -/
theorem G1061_dirichlet (φ₀ : PotPair) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, ∃ C : ℝ, ∀ φ ∈ V, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      ((Summable (fun n : ℤ => errg φ (muSeq φ) n t) ∧ (∑' n : ℤ, errg φ (muSeq φ) n t) ≤ C) ∧
      (Summable (fun n : ℤ =>
        ‖pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 0 -
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 1 -
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2) ∧
      (∑' n : ℤ,
        (‖pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 0 -
          Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 1 -
          Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2)) ≤ C) ∧
      (∀ n : ℤ, N < n.natAbs → Q (state φ (muSeq φ n) (![1, 1] : PairVec38)) ≠ 0) ∧
      (Summable (fun n : ℤ => if N < n.natAbs then
        ‖(Q (state φ (muSeq φ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 0 -
          (1 / 2 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (muSeq φ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 1 -
          (1 / 2 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then
        ‖(Q (state φ (muSeq φ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 0 -
          (1 / 2 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (muSeq φ n) (![1, 1] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (muSeq φ n) (![1, 1] : PairVec38))) t 1 -
          (1 / 2 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) ≤ C)) := by
  obtain ⟨V, hV, N, h⟩ := NlsGge.Atomic.G1087S2.Uniform.Q_small φ₀ (1 / 2) (by norm_num)
  exact dirichlet_main φ₀ ⟨V, hV, N, h⟩

/-- G1-061 (Lemma 7.6), Neumann part. -/
theorem G1061_neumann (φ₀ : PotPair) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, ∃ C : ℝ, ∀ φ ∈ V, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      ((Summable (fun n : ℤ =>
        ‖pairKernelExt38 (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) t 0 -
          Complex.I * Complex.exp (-(Real.pi * n * t * Complex.I))‖ ^ 2 +
        ‖pairKernelExt38 (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) t 1 -
          (-Complex.I) * Complex.exp (Real.pi * n * t * Complex.I)‖ ^ 2) ∧
      (∑' n : ℤ,
        (‖pairKernelExt38 (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) t 0 -
          Complex.I * Complex.exp (-(Real.pi * n * t * Complex.I))‖ ^ 2 +
        ‖pairKernelExt38 (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) t 1 -
          (-Complex.I) * Complex.exp (Real.pi * n * t * Complex.I)‖ ^ 2)) ≤ C) ∧
      (Summable (fun n : ℤ =>
        ‖pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 0 -
          (-Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 1 -
          (-Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)))‖ ^ 2) ∧
      (∑' n : ℤ,
        (‖pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 0 -
          (-Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2 +
        ‖pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 1 -
          (-Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)))‖ ^ 2)) ≤ C) ∧
      (∀ n : ℤ, N < n.natAbs →
        Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)) ≠ 0) ∧
      (Summable (fun n : ℤ => if N < n.natAbs then
        ‖(Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 0 -
          (-(1 / 2 : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 1 -
          (-(1 / 2 : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) ∧
      (∑' n : ℤ, if N < n.natAbs then
        ‖(Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 0 -
          (-(1 / 2 : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I)‖ ^ 2 +
        ‖(Q (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38)))⁻¹ *
            pairKernelExt38 (square (state φ (nuSeq38 φ n) (![Complex.I, -Complex.I] : PairVec38))) t 1 -
          (-(1 / 2 : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I))‖ ^ 2
        else 0) ≤ C)) := by
  obtain ⟨V, hV, N, h⟩ := NlsGge.Atomic.G1087S2.Uniform.Q_small (-φ₀) (1 / 2) (by norm_num)
  exact neumann_main φ₀ ⟨V, hV, N, h⟩

end

end NlsGge.Atomic.G1061S1

#print axioms NlsGge.Atomic.G1061S1.G1061_dirichlet
#print axioms NlsGge.Atomic.G1061S1.G1061_neumann
#print axioms NlsGge.Atomic.G1061S1.muSeq_simple_of_Q_ne_zero
#print axioms NlsGge.Atomic.G1061S1.nuSeq_simple_of_Q_ne_zero
