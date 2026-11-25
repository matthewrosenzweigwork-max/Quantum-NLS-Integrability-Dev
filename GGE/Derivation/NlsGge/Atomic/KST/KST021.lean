import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST007
import NlsGge.Atomic.KST.KST011
import NlsGge.Atomic.KSTPath
import NlsGge.Atomic.KST.KST024
import NlsGge.Schur.FreeResolventComplexHilbertSchmidtOpNormAfterL2Prerequisites

/- KST-021 PRODUCTION01 (proof development landing kit; HELD for landing). Source: proof development/KST021_FULL_01.lean.txt (author proof development, lane req e9de7d22; independent review proof development/KST021_REVIEW01.md), identical except this header, the added `import NlsGge.Atomic.KST.KST018` and the removed `#print axioms` line.
   Target NlsGge/Atomic/KST/KST021.lean. Pro definitions pathProduct/pathBlock/pathMajorant/positivePathTerm are declared here (not in production yet). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NlsGge.ThirdConsultation.KST

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003
open NlsGge.Atomic.KST004 NlsGge.Atomic.KST006 NlsGge.Atomic.KST007
open NlsGge.Atomic.KST012 NlsGge.Atomic.KST013 NlsGge.Atomic.KST016
open NlsGge.Analysis NlsGge.Pilot NlsGge.Schur NlsGge.Atomic.KSTPath

def positivePathTerm (φ : Potential) (n : ℤ) (j : ℕ) : ℂ :=
  inner ℂ (NlsGge.Schur.spectralBasis n)
    ((((positiveBlock φ n false) * (positiveBlock φ n true))^(j+1))
      (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ)))

/-- real nonnegative coefficients -/
def PosVec (g : SpectralScalarL2) : Prop :=
  ∀ k, ∃ r : ℝ, 0 ≤ r ∧ spectralCoeff g k = (r : ℂ)

/-- coefficientwise domination in modulus -/
def Dom (f g : SpectralScalarL2) : Prop :=
  ∀ k, ‖spectralCoeff f k‖ ≤ ‖spectralCoeff g k‖

theorem rd_eq' (n k : ℤ) : reciprocalDistance n k = 1 / (Int.natAbs (k - n) : ℝ) := by
  by_cases h : k = n
  · simp [reciprocalDistance, h]
  · simp only [reciprocalDistance, h, if_false]
    rw [show n - k = -(k - n) by ring, Int.natAbs_neg]

theorem posKernel_nonneg (φ : Potential) (n : ℤ) (u : Bool) (l j : ℤ) :
    0 ≤ positiveKernel φ n u l j := by
  unfold positiveKernel
  refine mul_nonneg (majorant_nonneg φ _) ?_
  rw [rd_eq']; positivity

theorem qterm_le (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (u : Bool)
    (l k : ℤ) (c : ℂ) :
    ‖potentialCoeff φ u (l - k) *
      (complementaryResolventCoeff n z (if u then k else -k) * c)‖ ≤
      positiveKernel φ n u l k * ‖c‖ := by
  simp only [norm_mul]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg c)
  unfold positiveKernel
  exact mul_le_mul (potentialCoeff_norm_le_majorant φ u (l - k))
    (by simpa only [rd_eq'] using
      complementaryResolventCoeff_bound n (if u then k else -k) z hz)
    (norm_nonneg _) (majorant_nonneg φ _)

theorem pos_step (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (u : Bool)
    (f g : SpectralScalarL2) (hD : Dom f g) (hP : PosVec g) :
    Dom (qBlock φ n z hz u f) (positiveBlock φ n u g) ∧ PosVec (positiveBlock φ n u g) := by
  choose r hr0 hrg using hP
  have hcoef : ∀ l, spectralCoeff (positiveBlock φ n u g) l =
      ((∑' j : ℤ, positiveKernel φ n u l j * r j : ℝ) : ℂ) := by
    intro l
    rw [(positiveBlock_coeff φ n u g l).2, Complex.ofReal_tsum]
    refine tsum_congr (fun j => ?_)
    rw [hrg j, Complex.ofReal_mul]
  have hsum : ∀ l, Summable (fun j : ℤ => positiveKernel φ n u l j * r j) := by
    intro l
    refine (positiveBlock_coeff φ n u g l).1.congr (fun j => ?_)
    rw [hrg j, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (posKernel_nonneg φ n u l j), abs_of_nonneg (hr0 j)]
  refine ⟨fun l => ?_, fun l => ⟨∑' j : ℤ, positiveKernel φ n u l j * r j,
    tsum_nonneg (fun j => mul_nonneg (posKernel_nonneg φ n u l j) (hr0 j)), hcoef l⟩⟩
  rw [hcoef l, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun j => mul_nonneg (posKernel_nonneg φ n u l j) (hr0 j))),
    qBlock_coeff]
  have hb : ∀ j : ℤ, ‖potentialCoeff φ u (l - j) *
      (complementaryResolventCoeff n z (if u then j else -j) * spectralCoeff f j)‖ ≤
      positiveKernel φ n u l j * r j := by
    intro j
    refine (qterm_le φ n z hz u l j _).trans (mul_le_mul_of_nonneg_left ?_ (posKernel_nonneg φ n u l j))
    have := hD j
    rwa [hrg j, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 j)] at this
  have hs : Summable (fun j : ℤ => ‖potentialCoeff φ u (l - j) *
      (complementaryResolventCoeff n z (if u then j else -j) * spectralCoeff f j)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hsum l)
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb (hsum l))

theorem pow_dom (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (k : ℕ) :
    ∀ f g : SpectralScalarL2, Dom f g → PosVec g →
      Dom ((((qBlock φ n z hz false) * (qBlock φ n z hz true)) ^ k) f)
        ((((positiveBlock φ n false) * (positiveBlock φ n true)) ^ k) g) ∧
      PosVec ((((positiveBlock φ n false) * (positiveBlock φ n true)) ^ k) g) := by
  induction k with
  | zero =>
    intro f g hD hP
    simpa using ⟨hD, hP⟩
  | succ k ih =>
    intro f g hD hP
    have s1 := pos_step φ n z hz true f g hD hP
    have s2 := pos_step φ n z hz false _ _ s1.1 s1.2
    rw [pow_succ, pow_succ]
    exact ih _ _ s2.1 s2.2

theorem q_comp_block (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (c : Bool)
    (u : H) : (qOperator φ n z hz u) c = qBlock φ n z hz c (u (!c)) := by
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext l
  cases c
  · rw [qOperator_lower_coeff]
    have := qBlock_coeff φ n z hz false (u true) l
    simpa [spectralCoeff, potentialCoeff] using this.symm
  · rw [qOperator_upper_coeff]
    have := qBlock_coeff φ n z hz true (u false) l
    simpa [spectralCoeff, potentialCoeff] using this.symm

theorem pow_even_false (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (k : ℕ)
    (u : H) :
    ((qOperator φ n z hz ^ (2 * k)) u) false =
      (((qBlock φ n z hz false) * (qBlock φ n z hz true)) ^ k) (u false) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ', pow_succ',
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, q_comp_block φ n z hz false,
      Bool.not_false, q_comp_block φ n z hz true, Bool.not_true, ih, pow_succ',
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]

theorem inner_frame_false (n : ℤ) (y : H) :
    inner ℂ (frame n false : H) y = spectralCoeff (y false) n := by
  rw [frame_coe]
  simp only [kstPnFrame, Bool.false_eq_true, if_false]
  unfold kstPnLower
  rw [inner_single_left, ← spectralBasis_repr_inner]
  rfl

theorem spectralCoeff_fm (k a : ℤ) (g : SpectralScalarL2) :
    spectralCoeff (NlsGge.Schur.fourierMultiplier k g) a = fourierCoeff g (a - k) := by
  unfold spectralCoeff
  rw [spectralBasis_repr_inner, inner_basis_mul]

theorem phi_frame_true' (φ : Potential) (n : ℤ) :
    potentialOnPn φ n (frame n true : H) =
      (PiLp.single 2 false (NlsGge.Schur.fourierMultiplier (-n)
        (naturalPhysicalCoverL2 (φ false))) : H) := by
  rw [pot_apply, frame_coe]
  have h := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by simpa [kstPnFrame] using h true true
  have hlu : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by simpa [kstPnFrame] using h false true
  simp only [kstPnFrame, if_true, huu, hlu, one_smul, zero_smul, zero_add]

theorem pathTerm_B_le (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (j : ℕ) :
    ‖pathTerm φ n z hz (2 * j + 2) false true‖ ≤ ‖positivePathTerm φ n j‖ := by
  have hP : PosVec (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ)) := by
    intro a
    refine ⟨majorantCoeff φ (a + n), majorant_nonneg φ _, ?_⟩
    rw [spectralCoeff_fm, sub_neg_eq_add, fc_repr]
    exact majorantFunction_coeff φ (a + n)
  have hD : Dom (NlsGge.Schur.fourierMultiplier (-n) (naturalPhysicalCoverL2 (φ false)))
      (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ)) := by
    intro a
    have e1 : fourierCoeff (majorantFunction φ) (a + n) = (majorantCoeff φ (a + n) : ℂ) := by
      rw [fc_repr]; exact majorantFunction_coeff φ _
    rw [spectralCoeff_fm, spectralCoeff_fm, sub_neg_eq_add, e1,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg φ _)]
    exact potentialCoeff_norm_le_majorant φ false (a + n)
  have hdom := (pow_dom φ n z hz (j + 1) _ _ hD hP).1 n
  unfold pathTerm positivePathTerm
  rw [phi_frame_true', show 2 * j + 2 = 2 * (j + 1) by ring, inner_frame_false,
    pow_even_false, ← spectralBasis_repr_inner]
  exact hdom


/-! ### C-channel: reflection and the true-first chain -/

theorem pow_dom_t (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (k : ℕ) :
    ∀ f g : SpectralScalarL2, Dom f g → PosVec g →
      Dom ((((qBlock φ n z hz true) * (qBlock φ n z hz false)) ^ k) f)
        ((((positiveBlock φ n true) * (positiveBlock φ n false)) ^ k) g) ∧
      PosVec ((((positiveBlock φ n true) * (positiveBlock φ n false)) ^ k) g) := by
  induction k with
  | zero =>
    intro f g hD hP
    simpa using ⟨hD, hP⟩
  | succ k ih =>
    intro f g hD hP
    have s1 := pos_step φ n z hz false f g hD hP
    have s2 := pos_step φ n z hz true _ _ s1.1 s1.2
    rw [pow_succ, pow_succ]
    exact ih _ _ s2.1 s2.2

theorem pow_even_true (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (k : ℕ)
    (u : H) :
    ((qOperator φ n z hz ^ (2 * k)) u) true =
      (((qBlock φ n z hz true) * (qBlock φ n z hz false)) ^ k) (u true) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ', pow_succ',
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, q_comp_block φ n z hz true,
      Bool.not_true, q_comp_block φ n z hz false, Bool.not_false, ih, pow_succ',
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]

theorem inner_frame_true (n : ℤ) (y : H) :
    inner ℂ (frame n true : H) y = spectralCoeff (y true) (-n) := by
  rw [frame_coe]
  simp only [kstPnFrame, if_true]
  unfold kstPnUpper
  rw [inner_single_left, ← spectralBasis_repr_inner]
  rfl

theorem phi_frame_false' (φ : Potential) (n : ℤ) :
    potentialOnPn φ n (frame n false : H) =
      (PiLp.single 2 true (NlsGge.Schur.fourierMultiplier n
        (naturalPhysicalCoverL2 (φ true))) : H) := by
  rw [pot_apply, frame_coe]
  have h := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by simpa [kstPnFrame] using h false false
  have hul : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by simpa [kstPnFrame] using h true false
  simp only [kstPnFrame, Bool.false_eq_true, if_false, hll, hul, one_smul, zero_smul, add_zero]

/-- the coefficient reflection `k ↦ -k` on the scalar space -/
def reflL (x : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun k => x (-k), memℓp_gen (by
    have h := (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x).summable
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h ⊢
    exact h.comp_injective neg_injective)⟩

def reflS (f : SpectralScalarL2) : SpectralScalarL2 :=
  (fourierBasis (T := (2 : ℝ))).repr.symm (reflL ((fourierBasis (T := (2 : ℝ))).repr f))

theorem reflS_coeff (f : SpectralScalarL2) (k : ℤ) :
    spectralCoeff (reflS f) k = spectralCoeff f (-k) := by
  unfold reflS spectralCoeff
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem refl_block (φ : Potential) (n : ℤ) (u : Bool) (f : SpectralScalarL2) :
    reflS (positiveBlock φ n u f) = positiveBlock φ n (!u) (reflS f) := by
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext l
  have h1 : (fourierBasis (T := (2 : ℝ))).repr (reflS (positiveBlock φ n u f)) l =
      spectralCoeff (positiveBlock φ n u f) (-l) := reflS_coeff _ _
  have h2 : (fourierBasis (T := (2 : ℝ))).repr (positiveBlock φ n (!u) (reflS f)) l =
      ∑' j : ℤ, (positiveKernel φ n (!u) l j : ℂ) * spectralCoeff (reflS f) j :=
    (positiveBlock_coeff φ n (!u) (reflS f) l).2
  rw [h1, h2, (positiveBlock_coeff φ n u f (-l)).2]
  have h3 := (Equiv.neg ℤ).tsum_eq
    (fun j : ℤ => (positiveKernel φ n (!u) l j : ℂ) * spectralCoeff (reflS f) j)
  rw [← h3]
  refine tsum_congr (fun j => ?_)
  simp only [Equiv.neg_apply, reflS_coeff, neg_neg]
  congr 1
  unfold positiveKernel
  have he := majorant_even φ
  have e1 : majorantCoeff φ (-l - j) = majorantCoeff φ (l - -j) := by
    rw [← he (-l - j)]; congr 1; ring
  rw [e1]
  cases u <;> simp

theorem refl_pow (φ : Potential) (n : ℤ) (k : ℕ) (f : SpectralScalarL2) :
    reflS ((((positiveBlock φ n true) * (positiveBlock φ n false)) ^ k) f) =
      (((positiveBlock φ n false) * (positiveBlock φ n true)) ^ k) (reflS f) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ']
    simp only [ContinuousLinearMap.mul_apply]
    rw [refl_block, Bool.not_true, refl_block, Bool.not_false, ih]

theorem fc_mf (φ : Potential) (m : ℤ) :
    fourierCoeff (majorantFunction φ) m = (majorantCoeff φ m : ℂ) := by
  rw [fc_repr]; exact majorantFunction_coeff φ _

theorem refl_fm (φ : Potential) (n : ℤ) :
    reflS (NlsGge.Schur.fourierMultiplier n (majorantFunction φ)) =
      NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ) := by
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext k
  have h1 : (fourierBasis (T := (2 : ℝ))).repr
      (reflS (NlsGge.Schur.fourierMultiplier n (majorantFunction φ))) k =
      spectralCoeff (NlsGge.Schur.fourierMultiplier n (majorantFunction φ)) (-k) := reflS_coeff _ _
  have h2 : (fourierBasis (T := (2 : ℝ))).repr
      (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ)) k =
      spectralCoeff (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ)) k := rfl
  rw [h1, h2, spectralCoeff_fm, spectralCoeff_fm, fc_mf, fc_mf]
  have : majorantCoeff φ (-k - n) = majorantCoeff φ (k - -n) := by
    rw [← majorant_even φ (-k - n)]; congr 1; ring
  rw [this]

theorem pathTerm_C_le (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (j : ℕ) :
    ‖pathTerm φ n z hz (2 * j + 2) true false‖ ≤ ‖positivePathTerm φ n j‖ := by
  have hP : PosVec (NlsGge.Schur.fourierMultiplier n (majorantFunction φ)) := by
    intro a
    refine ⟨majorantCoeff φ (a - n), majorant_nonneg φ _, ?_⟩
    rw [spectralCoeff_fm, fc_repr]
    exact majorantFunction_coeff φ (a - n)
  have hD : Dom (NlsGge.Schur.fourierMultiplier n (naturalPhysicalCoverL2 (φ true)))
      (NlsGge.Schur.fourierMultiplier n (majorantFunction φ)) := by
    intro a
    have e1 : fourierCoeff (majorantFunction φ) (a - n) = (majorantCoeff φ (a - n) : ℂ) := by
      rw [fc_repr]; exact majorantFunction_coeff φ _
    rw [spectralCoeff_fm, spectralCoeff_fm, e1,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg φ _)]
    exact potentialCoeff_norm_le_majorant φ true (a - n)
  have hdom := (pow_dom_t φ n z hz (j + 1) _ _ hD hP).1 (-n)
  have hrefl : spectralCoeff ((((positiveBlock φ n true) * (positiveBlock φ n false)) ^ (j + 1))
      (NlsGge.Schur.fourierMultiplier n (majorantFunction φ))) (-n) =
      inner ℂ (NlsGge.Schur.spectralBasis n)
        ((((positiveBlock φ n false) * (positiveBlock φ n true)) ^ (j + 1))
          (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ))) := by
    rw [← refl_fm, ← refl_pow, ← spectralBasis_repr_inner, ← reflS_coeff]
    rfl
  unfold pathTerm
  rw [phi_frame_false', show 2 * j + 2 = 2 * (j + 1) by ring, inner_frame_true, pow_even_true]
  unfold positivePathTerm
  rw [← hrefl]
  exact hdom


/-! ### L3: realness, geometric bound, summability -/

theorem ppt_posvec (φ : Potential) (n : ℤ) (j : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ positivePathTerm φ n j = (r : ℂ) := by
  have hz : ((n : ℂ) * (Real.pi : ℂ)) ∈ spectralStrip n := by
    simp only [spectralStrip, Set.mem_setOf_eq]
    have : (((n : ℂ) * (Real.pi : ℂ))).re = (n : ℝ) * Real.pi := by simp
    rw [this, sub_self, abs_zero]
    positivity
  have hP : PosVec (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ)) := by
    intro a
    refine ⟨majorantCoeff φ (a + n), majorant_nonneg φ _, ?_⟩
    rw [spectralCoeff_fm, sub_neg_eq_add, fc_repr]
    exact majorantFunction_coeff φ (a + n)
  have h := (pow_dom φ n _ hz (j + 1) _ _ (fun k => le_rfl) hP).2 n
  obtain ⟨r, hr0, hr⟩ := h
  refine ⟨r, hr0, ?_⟩
  unfold positivePathTerm
  rw [← hr]
  exact (spectralBasis_repr_inner _ n).symm

theorem ppt_bound (φ : Potential) (n : ℤ) (j : ℕ)
    (hM : ‖(positiveBlock φ n false) * (positiveBlock φ n true)‖ ≤ 1 / 4) :
    ‖positivePathTerm φ n j‖ ≤ (1 / 4 : ℝ) ^ (j + 1) * ‖majorantSequence φ‖ := by
  unfold positivePathTerm
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (NlsGge.Schur.spectralBasis n)
    ((((positiveBlock φ n false) * (positiveBlock φ n true)) ^ (j + 1))
      (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ)))
  rw [NlsGge.Schur.spectralBasis_norm, one_mul] at h1
  refine h1.trans ?_
  have h2 := ((((positiveBlock φ n false) * (positiveBlock φ n true)) ^ (j + 1))).le_opNorm
    (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ))
  rw [NlsGge.Schur.fourierMultiplier_norm_apply, majorantFunction_norm] at h2
  have h3 : ‖(((positiveBlock φ n false) * (positiveBlock φ n true)) ^ (j + 1))‖ ≤
      ‖(positiveBlock φ n false) * (positiveBlock φ n true)‖ ^ (j + 1) :=
    norm_pow_le' _ (Nat.succ_pos j)
  refine h2.trans ?_
  gcongr
  exact h3.trans (pow_le_pow_left₀ (norm_nonneg _) hM _)

theorem ppt_summable (φ : Potential) (n : ℤ)
    (hM : ‖(positiveBlock φ n false) * (positiveBlock φ n true)‖ ≤ 1 / 4) :
    Summable (fun j : ℕ => ‖positivePathTerm φ n j‖) := by
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ppt_bound φ n j hM) ?_
  have hg : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have := (hg.mul_left ((1 / 4 : ℝ) * ‖majorantSequence φ‖))
  refine this.congr (fun j => ?_)
  ring

theorem hsNorm_block_le (φ : Potential) (n : ℤ)
    (hh : NlsGge.Pilot.IsComplexHilbertSchmidt
        ((positiveBlock φ n false).comp (positiveBlock φ n (!false))) ∧
      NlsGge.Pilot.complexHilbertSchmidtNorm
        ((positiveBlock φ n false).comp (positiveBlock φ n (!false))) ≤ (1 / 4 : ℝ)) :
    ‖(positiveBlock φ n false) * (positiveBlock φ n true)‖ ≤ 1 / 4 := by
  have h := NlsGge.Schur.complexHilbertSchmidt_opNorm_le _ hh.1
  simp only [Bool.not_false] at h hh
  exact (h.trans hh.2)


/-! ### L1b: the chain of positive blocks as an ENNReal recursion -/

theorem strip_nπ (n : ℤ) : ((n : ℂ) * (Real.pi : ℂ)) ∈ spectralStrip n := by
  simp only [spectralStrip, Set.mem_setOf_eq]
  have : (((n : ℂ) * (Real.pi : ℂ))).re = (n : ℝ) * Real.pi := by simp
  rw [this, sub_self, abs_zero]
  positivity

def wch (φ : Potential) (n : ℤ) : ℕ → SpectralScalarL2
  | 0 => NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ)
  | m + 1 => positiveBlock φ n (decide (Even m)) (wch φ n m)

theorem wch_pow (φ : Potential) (n : ℤ) (k : ℕ) :
    ((((positiveBlock φ n false) * (positiveBlock φ n true)) ^ k)
      (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ))) = wch φ n (2 * k) := by
  induction k with
  | zero => simp [wch]
  | succ k ih =>
    have e1 : wch φ n (2 * k + 1) = positiveBlock φ n true (wch φ n (2 * k)) := by
      simp [wch]
    have e2 : wch φ n (2 * k + 1 + 1) = positiveBlock φ n false (wch φ n (2 * k + 1)) := by
      simp [wch, Nat.even_add_one]
    rw [pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ih,
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring, e2, e1]

theorem wch_posvec (φ : Potential) (n : ℤ) (m : ℕ) : PosVec (wch φ n m) := by
  induction m with
  | zero =>
    intro a
    refine ⟨majorantCoeff φ (a + n), majorant_nonneg φ _, ?_⟩
    show spectralCoeff (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ)) a = _
    rw [spectralCoeff_fm, sub_neg_eq_add, fc_mf]
  | succ m ih =>
    exact (pos_step φ n _ (strip_nπ n) (decide (Even m)) _ _ (fun k => le_rfl) ih).2

noncomputable def Rv (φ : Potential) (n : ℤ) (m : ℕ) (j : ℤ) : ℝ := (wch_posvec φ n m j).choose

theorem Rv_nonneg (φ : Potential) (n : ℤ) (m : ℕ) (j : ℤ) : 0 ≤ Rv φ n m j :=
  (wch_posvec φ n m j).choose_spec.1

theorem Rv_spec (φ : Potential) (n : ℤ) (m : ℕ) (j : ℤ) :
    spectralCoeff (wch φ n m) j = (Rv φ n m j : ℂ) :=
  (wch_posvec φ n m j).choose_spec.2

theorem Rv_zero (φ : Potential) (n : ℤ) (u : ℤ) : Rv φ n 0 u = majorantCoeff φ (u + n) := by
  have h := Rv_spec φ n 0 u
  have h2 : spectralCoeff (wch φ n 0) u = (majorantCoeff φ (u + n) : ℂ) := by
    show spectralCoeff (NlsGge.Schur.fourierMultiplier (-n) (majorantFunction φ)) u = _
    rw [spectralCoeff_fm, sub_neg_eq_add, fc_mf]
  exact Complex.ofReal_injective (h.symm.trans h2)

theorem Rv_succ (φ : Potential) (n : ℤ) (m : ℕ) (l : ℤ) :
    Summable (fun j : ℤ => positiveKernel φ n (decide (Even m)) l j * Rv φ n m j) ∧
    Rv φ n (m + 1) l = ∑' j : ℤ, positiveKernel φ n (decide (Even m)) l j * Rv φ n m j := by
  have hc := positiveBlock_coeff φ n (decide (Even m)) (wch φ n m) l
  constructor
  · refine hc.1.congr (fun j => ?_)
    rw [Rv_spec, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (posKernel_nonneg φ n _ l j), abs_of_nonneg (Rv_nonneg φ n m j)]
  · have h1 : spectralCoeff (wch φ n (m + 1)) l = (Rv φ n (m + 1) l : ℂ) := Rv_spec φ n (m + 1) l
    have h2 : spectralCoeff (wch φ n (m + 1)) l =
        ((∑' j : ℤ, positiveKernel φ n (decide (Even m)) l j * Rv φ n m j : ℝ) : ℂ) := by
      show spectralCoeff (positiveBlock φ n (decide (Even m)) (wch φ n m)) l = _
      rw [hc.2, Complex.ofReal_tsum]
      refine tsum_congr (fun j => ?_)
      rw [Rv_spec, Complex.ofReal_mul]
    exact Complex.ofReal_injective (h1.symm.trans h2)


def sgn (m : ℕ) : ℤ := if Even m then 1 else -1

theorem sgn_succ (m : ℕ) : sgn (m + 1) = - sgn m := by
  unfold sgn
  by_cases h : Even m <;> simp [h, Nat.even_add_one]

noncomputable def Prec (φ : Potential) (n : ℤ) : ℕ → ℤ → ℝ≥0∞
  | 0, u => ENNReal.ofReal (majorantCoeff φ (u + n))
  | m + 1, u => ∑' ℓ : ℤ,
      ENNReal.ofReal (majorantCoeff φ (u + ℓ) / (Int.natAbs (ℓ - n) : ℝ)) * Prec φ n m ℓ

theorem kernel_id (φ : Potential) (n : ℤ) (m : ℕ) (u ℓ : ℤ) :
    positiveKernel φ n (decide (Even m)) (sgn (m + 1) * u) (sgn m * ℓ) =
      majorantCoeff φ (u + ℓ) / (Int.natAbs (ℓ - n) : ℝ) := by
  unfold positiveKernel
  rw [rd_eq', ← div_eq_mul_one_div]
  have he := majorant_even φ
  by_cases h : Even m
  · have h1 : sgn (m + 1) = -1 := by rw [sgn_succ]; simp [sgn, h]
    have h2 : sgn m = 1 := by simp [sgn, h]
    simp only [h1, h2, decide_eq_true h, if_true, one_mul, neg_mul]
    rw [show -u - ℓ = -(u + ℓ) by ring, he]
  · have h1 : sgn (m + 1) = 1 := by rw [sgn_succ]; simp [sgn, h]
    have h2 : sgn m = -1 := by simp [sgn, h]
    simp only [h1, h2, decide_eq_false h, Bool.false_eq_true, if_false, one_mul, neg_mul]
    rw [show u - -ℓ = u + ℓ by ring, show -(-ℓ) = ℓ by ring]

theorem Prec_eq (φ : Potential) (n : ℤ) (m : ℕ) (u : ℤ) :
    Prec φ n m u = ENNReal.ofReal (Rv φ n m (sgn m * u)) := by
  induction m generalizing u with
  | zero =>
    simp [Prec, sgn, Rv_zero]
  | succ m ih =>
    obtain ⟨hs, hv⟩ := Rv_succ φ n m (sgn (m + 1) * u)
    -- reindex the real sum by j = sgn m * ℓ
    have hmul : ∀ x : ℤ, sgn m * (sgn m * x) = x := by
      intro x
      unfold sgn
      split_ifs <;> ring
    let e : ℤ ≃ ℤ := ⟨fun x => sgn m * x, fun x => sgn m * x, fun x => hmul x, fun x => hmul x⟩
    have hsum' : Summable (fun ℓ : ℤ =>
        positiveKernel φ n (decide (Even m)) (sgn (m + 1) * u) (sgn m * ℓ) * Rv φ n m (sgn m * ℓ)) :=
      e.summable_iff.mpr hs
    have htsum : (∑' ℓ : ℤ,
        positiveKernel φ n (decide (Even m)) (sgn (m + 1) * u) (sgn m * ℓ) * Rv φ n m (sgn m * ℓ)) =
        ∑' j : ℤ, positiveKernel φ n (decide (Even m)) (sgn (m + 1) * u) j * Rv φ n m j :=
      e.tsum_eq (fun j => positiveKernel φ n (decide (Even m)) (sgn (m + 1) * u) j * Rv φ n m j)
    rw [hv, ← htsum]
    have hnn : ∀ ℓ : ℤ, 0 ≤ positiveKernel φ n (decide (Even m)) (sgn (m + 1) * u) (sgn m * ℓ) *
        Rv φ n m (sgn m * ℓ) := fun ℓ =>
      mul_nonneg (posKernel_nonneg φ n _ _ _) (Rv_nonneg φ n m _)
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum']
    unfold Prec
    refine tsum_congr (fun ℓ => ?_)
    rw [ih ℓ, kernel_id φ n m u ℓ, ENNReal.ofReal_mul (div_nonneg (majorant_nonneg φ _) (by positivity))]


/-! ### L1a: the Fin-indexed path sum is the recursion -/

def pathProduct {k : ℕ} (hk : 0 < k) (A : ℤ → ℝ) (n : ℤ)
    (ell : Path k) : ℝ :=
  (∏ j : Fin (2*k+1), A (pathArgument hk n ell j)) /
    ∏ i : Fin (2*k), ((ell i-n).natAbs : ℝ)

open Classical in
def pathBlock {k : ℕ} (hk : 0 < k) (A : ℤ → ℝ) (n : ℤ) : ℝ≥0∞ :=
  ∑' ell : Path k, if admissiblePath n ell then
    ENNReal.ofReal (pathProduct hk A n ell) else 0

def pathMajorant (A : ℤ → ℝ) (n : ℤ) : ℝ≥0∞ :=
  ∑' j : ℕ, pathBlock (Nat.succ_pos j) A n

/-- extension of a finite path by the resonant value -/
def extP (n : ℤ) {m : ℕ} (ℓ : Fin m → ℤ) (i : ℕ) : ℤ := if h : i < m then ℓ ⟨i, h⟩ else n

def argM (A : ℤ → ℝ) (n : ℤ) (m : ℕ) (u : ℤ) (ℓ : Fin m → ℤ) (j : ℕ) : ℝ :=
  A ((if j = 0 then u else extP n ℓ (j - 1)) + extP n ℓ j)

def pathProdM (A : ℤ → ℝ) (n : ℤ) (m : ℕ) (u : ℤ) (ℓ : Fin m → ℤ) : ℝ :=
  (∏ j : Fin (m + 1), argM A n m u ℓ j.val) / ∏ i : Fin m, ((ℓ i - n).natAbs : ℝ)

theorem extP_cons_zero (n ℓ₀ : ℤ) {m : ℕ} (ℓ : Fin m → ℤ) :
    extP n (Fin.cons ℓ₀ ℓ : Fin (m + 1) → ℤ) 0 = ℓ₀ := by
  simp [extP]

theorem extP_cons_succ (n ℓ₀ : ℤ) {m : ℕ} (ℓ : Fin m → ℤ) (i : ℕ) :
    extP n (Fin.cons ℓ₀ ℓ : Fin (m + 1) → ℤ) (i + 1) = extP n ℓ i := by
  unfold extP
  by_cases h : i < m
  · have h' : i + 1 < m + 1 := by omega
    rw [dif_pos h', dif_pos h]
    exact Fin.cons_succ (α := fun _ => ℤ) ℓ₀ ℓ ⟨i, h⟩
  · have h' : ¬ i + 1 < m + 1 := by omega
    rw [dif_neg h', dif_neg h]

theorem pathProdM_cons (A : ℤ → ℝ) (n : ℤ) (m : ℕ) (u ℓ₀ : ℤ) (ℓ : Fin m → ℤ) :
    pathProdM A n (m + 1) u (Fin.cons ℓ₀ ℓ : Fin (m + 1) → ℤ) =
      A (u + ℓ₀) / (Int.natAbs (ℓ₀ - n) : ℝ) * pathProdM A n m ℓ₀ ℓ := by
  have h0 : argM A n (m + 1) u (Fin.cons ℓ₀ ℓ : Fin (m + 1) → ℤ) 0 = A (u + ℓ₀) := by
    simp [argM, extP_cons_zero]
  have hj : ∀ j : Fin (m + 1), argM A n (m + 1) u (Fin.cons ℓ₀ ℓ : Fin (m + 1) → ℤ) (j.val + 1) =
      argM A n m ℓ₀ ℓ j.val := by
    intro j
    unfold argM
    rw [extP_cons_succ]
    congr 1
    rcases Nat.eq_zero_or_pos j.val with h | h
    · rw [h]; simp [extP_cons_zero]
    · obtain ⟨i, hi⟩ : ∃ i, j.val = i + 1 := ⟨j.val - 1, by omega⟩
      rw [hi]
      simp [extP_cons_succ]
  have hnum : ∏ j : Fin (m + 1 + 1), argM A n (m + 1) u (Fin.cons ℓ₀ ℓ : Fin (m + 1) → ℤ) j.val =
      A (u + ℓ₀) * ∏ j : Fin (m + 1), argM A n m ℓ₀ ℓ j.val := by
    rw [Fin.prod_univ_succ, Fin.val_zero, h0]
    congr 1
    exact Finset.prod_congr rfl (fun j _ => by rw [Fin.val_succ]; exact hj j)
  have hden : ∏ i : Fin (m + 1), (((Fin.cons ℓ₀ ℓ : Fin (m + 1) → ℤ) i - n).natAbs : ℝ) =
      (Int.natAbs (ℓ₀ - n) : ℝ) * ∏ i : Fin m, ((ℓ i - n).natAbs : ℝ) := by
    rw [Fin.prod_univ_succ]
    simp
  unfold pathProdM
  rw [hnum, hden, mul_div_mul_comm]

theorem pathArgument_eq_argM (φ : Potential) (n : ℤ) {k : ℕ} (hk : 0 < k) (ℓ : Path k)
    (j : Fin (2 * k + 1)) :
    majorantCoeff φ (pathArgument hk n ℓ j) = argM (majorantCoeff φ) n (2 * k) n ℓ j.val := by
  unfold pathArgument argM
  congr 1
  by_cases h0 : j.val = 0
  · have hh : 0 < 2 * k := by omega
    simp only [h0, if_true]
    rw [vertexIndex_eq_mk hk (i := 0) hh]
    simp [extP, hh]
  · by_cases h1 : j.val < 2 * k
    · simp only [h0, h1, if_false, if_true]
      have a1 : j.val - 1 < 2 * k := by omega
      rw [vertexIndex_eq_mk hk a1, vertexIndex_eq_mk hk h1]
      simp [extP, a1, h1]
    · have hj : j.val = 2 * k := by have := j.isLt; omega
      simp only [h0, h1, if_false]
      have a1 : 2 * k - 1 < 2 * k := by omega
      rw [vertexIndex_eq_mk hk a1]
      simp [extP, a1, hj]


noncomputable def PB (φ : Potential) (n : ℤ) (m : ℕ) (u : ℤ) : ℝ≥0∞ :=
  ∑' ℓ : Fin m → ℤ, ENNReal.ofReal (pathProdM (majorantCoeff φ) n m u ℓ)

theorem PB_eq_Prec (φ : Potential) (n : ℤ) (m : ℕ) (u : ℤ) : PB φ n m u = Prec φ n m u := by
  induction m generalizing u with
  | zero =>
    haveI : Unique (Fin 0 → ℤ) := inferInstance
    unfold PB
    rw [tsum_eq_single default (fun b hb => absurd (Subsingleton.elim b default) hb)]
    simp [pathProdM, argM, extP, Prec]
  | succ m ih =>
    unfold PB
    have e := (Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)).tsum_eq
      (fun ℓ : Fin (m + 1) → ℤ => ENNReal.ofReal (pathProdM (majorantCoeff φ) n (m + 1) u ℓ))
    rw [← e, ENNReal.tsum_prod']
    unfold Prec
    refine tsum_congr (fun ℓ₀ => ?_)
    have h1 : ∀ ℓt : Fin m → ℤ,
        ENNReal.ofReal (pathProdM (majorantCoeff φ) n (m + 1) u
          ((Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)) (ℓ₀, ℓt))) =
        ENNReal.ofReal (majorantCoeff φ (u + ℓ₀) / (Int.natAbs (ℓ₀ - n) : ℝ)) *
          ENNReal.ofReal (pathProdM (majorantCoeff φ) n m ℓ₀ ℓt) := by
      intro ℓt
      have : (Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)) (ℓ₀, ℓt) = (Fin.cons ℓ₀ ℓt : Fin (m + 1) → ℤ) := rfl
      rw [this, pathProdM_cons, ENNReal.ofReal_mul (div_nonneg (majorant_nonneg φ _) (by positivity))]
    simp only [h1]
    rw [ENNReal.tsum_mul_left, ← ih ℓ₀]
    try rfl

theorem pathBlock_eq_PB (φ : Potential) (n : ℤ) {k : ℕ} (hk : 0 < k) :
    pathBlock hk (majorantCoeff φ) n = PB φ n (2 * k) n := by
  unfold pathBlock PB
  refine tsum_congr (fun ℓ => ?_)
  have hp : pathProduct hk (majorantCoeff φ) n ℓ = pathProdM (majorantCoeff φ) n (2 * k) n ℓ := by
    unfold pathProduct pathProdM
    congr 1
    exact Finset.prod_congr rfl (fun j _ => pathArgument_eq_argM φ n hk ℓ j)
  rw [hp]
  by_cases hadm : admissiblePath n ℓ
  · rw [if_pos hadm]
  · rw [if_neg hadm]
    unfold admissiblePath at hadm
    push_neg at hadm
    obtain ⟨i, hi⟩ := hadm
    have hz : ∏ i : Fin (2 * k), ((ℓ i - n).natAbs : ℝ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    unfold pathProdM
    rw [hz, div_zero, ENNReal.ofReal_zero]

theorem sgn_even_two_mul (k : ℕ) : sgn (2 * k) = 1 := by
  simp [sgn]

theorem pathBlock_eq_ofReal (φ : Potential) (n : ℤ) (j : ℕ) :
    pathBlock (Nat.succ_pos j) (majorantCoeff φ) n = ENNReal.ofReal (Rv φ n (2 * (j + 1)) n) := by
  rw [pathBlock_eq_PB, PB_eq_Prec, Prec_eq, sgn_even_two_mul, one_mul]
  try rfl

theorem ppt_eq_Rv (φ : Potential) (n : ℤ) (j : ℕ) :
    positivePathTerm φ n j = (Rv φ n (2 * (j + 1)) n : ℂ) := by
  unfold positivePathTerm
  rw [wch_pow, ← Rv_spec]
  exact (spectralBasis_repr_inner _ n).symm


/-! ### Assembly: KST-021 -/

theorem kst021 (φ : Potential) :
  ∃ N₀ : ℕ, 5 ≤ N₀ ∧ ∀ n : ℤ, N₀ ≤ n.natAbs →
    pathMajorant (majorantCoeff φ) n < ⊤ ∧
    Summable (fun j : ℕ => ‖positivePathTerm φ n j‖) ∧
    (∀ j : ℕ,
      positivePathTerm φ n j =
        ((pathBlock (Nat.succ_pos j) (majorantCoeff φ) n).toReal : ℂ)) ∧
    (∑' j : ℕ, positivePathTerm φ n j) =
      ((pathMajorant (majorantCoeff φ) n).toReal : ℂ) ∧
    ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
      Summable (fun j : ℕ => ‖pathTerm φ n z hz (2*j+2) false true‖) ∧
      Summable (fun j : ℕ => ‖pathTerm φ n z hz (2*j+2) true false‖) ∧
      ‖remainderB φ n z hz‖ ≤ (pathMajorant (majorantCoeff φ) n).toReal ∧
      ‖remainderC φ n z hz‖ ≤ (pathMajorant (majorantCoeff φ) n).toReal ∧
      ‖reducedB φ n z hz-coveredCoeff φ false (2*n)‖ ≤
        (pathMajorant (majorantCoeff φ) n).toReal ∧
      ‖reducedC φ n z hz-coveredCoeff φ true (-2*n)‖ ≤
        (pathMajorant (majorantCoeff φ) n).toReal := by
  obtain ⟨ε, hε, N₁, hN₁, hloc⟩ := reducedBC_uniform_local φ
  obtain ⟨ε2, hε2, N₂, hN₂, hhs⟩ := NlsGge.Atomic.KST011.hs_qOperator_sq_decay φ
  refine ⟨max N₁ N₂, le_trans hN₁ (le_max_left _ _), ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n.natAbs := le_trans (le_max_right _ _) hn
  have hM : ‖(positiveBlock φ n false) * (positiveBlock φ n true)‖ ≤ 1 / 4 :=
    hsNorm_block_le φ n ((hhs φ (by simpa using hε2) n hn2).1 false)
  have hsum := ppt_summable φ n hM
  have hpp : ∀ j : ℕ, positivePathTerm φ n j = (Rv φ n (2 * (j + 1)) n : ℂ) := ppt_eq_Rv φ n
  have hr0 : ∀ j : ℕ, 0 ≤ Rv φ n (2 * (j + 1)) n := fun j => Rv_nonneg φ n _ _
  have hnorm : ∀ j : ℕ, ‖positivePathTerm φ n j‖ = Rv φ n (2 * (j + 1)) n := by
    intro j
    rw [hpp j, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 j)]
  have hsumR : Summable (fun j : ℕ => Rv φ n (2 * (j + 1)) n) := hsum.congr hnorm
  have hmaj : pathMajorant (majorantCoeff φ) n =
      ENNReal.ofReal (∑' j : ℕ, Rv φ n (2 * (j + 1)) n) := by
    unfold pathMajorant
    rw [ENNReal.ofReal_tsum_of_nonneg hr0 hsumR]
    exact tsum_congr (fun j => pathBlock_eq_ofReal φ n j)
  have hMtoReal : (pathMajorant (majorantCoeff φ) n).toReal = ∑' j : ℕ, Rv φ n (2 * (j + 1)) n := by
    rw [hmaj, ENNReal.toReal_ofReal (tsum_nonneg hr0)]
  refine ⟨by rw [hmaj]; exact ENNReal.ofReal_lt_top, hsum, ?_, ?_, ?_⟩
  · intro j
    rw [pathBlock_eq_ofReal, ENNReal.toReal_ofReal (hr0 j), hpp j]
  · rw [hMtoReal, Complex.ofReal_tsum]
    exact tsum_congr (fun j => hpp j)
  · intro z hz
    have hq : ‖qOperator φ n z hz ^ 2‖ ≤ 1 / 2 := (hloc φ (by simpa using hε) n hn1 z hz).1
    have hlt : ‖qOperator φ n z hz ^ 2‖ < 1 := lt_of_le_of_lt hq (by norm_num)
    have hsB : Summable (fun j : ℕ => ‖pathTerm φ n z hz (2 * j + 2) false true‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => pathTerm_B_le φ n z hz j) hsum
    have hsC : Summable (fun j : ℕ => ‖pathTerm φ n z hz (2 * j + 2) true false‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => pathTerm_C_le φ n z hz j) hsum
    have hremB : ‖remainderB φ n z hz‖ ≤ (pathMajorant (majorantCoeff φ) n).toReal := by
      rw [hMtoReal]
      calc ‖remainderB φ n z hz‖ ≤ ∑' j : ℕ, ‖pathTerm φ n z hz (2 * j + 2) false true‖ :=
            norm_tsum_le_tsum_norm hsB
        _ ≤ ∑' j : ℕ, ‖positivePathTerm φ n j‖ :=
            hsB.tsum_le_tsum (fun j => pathTerm_B_le φ n z hz j) hsum
        _ = _ := tsum_congr hnorm
    have hremC : ‖remainderC φ n z hz‖ ≤ (pathMajorant (majorantCoeff φ) n).toReal := by
      rw [hMtoReal]
      calc ‖remainderC φ n z hz‖ ≤ ∑' j : ℕ, ‖pathTerm φ n z hz (2 * j + 2) true false‖ :=
            norm_tsum_le_tsum_norm hsC
        _ ≤ ∑' j : ℕ, ‖positivePathTerm φ n j‖ :=
            hsC.tsum_le_tsum (fun j => pathTerm_C_le φ n z hz j) hsum
        _ = _ := tsum_congr hnorm
    obtain ⟨-, -, hB, hC⟩ := reducedBC_fourier_remainders φ n z hz hlt
    refine ⟨hsB, hsC, hremB, hremC, ?_, ?_⟩
    · rw [hB, add_sub_cancel_left]; exact hremB
    · rw [hC, add_sub_cancel_left]; exact hremC

end NlsGge.ThirdConsultation.KST

