import Mathlib
import NlsGge.Atomic.KST.KST013
import NlsGge.Atomic.KST.KST011
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.LIB.LIB023

set_option autoImplicit false

/-! KST-016 part 1 (proof development, AUTHOR; not self-reviewed): nodes KST016.01-06 of the GPT-6 Pro supplemental design. -/

noncomputable section

open MeasureTheory
open scoped InnerProduct InnerProductSpace ENNReal

namespace NlsGge.Atomic.KST016

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003
open NlsGge.Atomic.KST004 NlsGge.Atomic.KST006
open NlsGge.Atomic.KST012 NlsGge.Atomic.KST013
open NlsGge.Analysis NlsGge.Pilot NlsGge.Schur

abbrev H := KSTPairL2
abbrev Potential := PhysicalPairLp
abbrev EndH := H →L[ℂ] H

def frame (n : ℤ) (b : Bool) : resonantSubspace n :=
  if b then ⟨kstPnUpper n, ⟨kstPnUpper n, spectralPn_upper n⟩⟩
  else ⟨kstPnLower n, ⟨kstPnLower n, spectralPn_lower n⟩⟩

def entry (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (i j : Bool) : ℂ :=
  inner ℂ (frame n i : H) (reducedS φ n z hz (frame n j) : H)

def reducedA (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) : ℂ :=
  (z - (n : ℂ) * Real.pi) - entry φ n z hz false false

def reducedB (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) : ℂ :=
  -entry φ n z hz false true

def reducedC (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) : ℂ :=
  -entry φ n z hz true false

def coveredCoeff (φ : Potential) (b : Bool) (k : ℤ) : ℂ :=
  fourierCoeff (naturalPhysicalCoverL2 (φ b)) k

def pathTerm (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (m : ℕ) (i j : Bool) : ℂ :=
  inner ℂ (frame n i : H)
    ((qOperator φ n z hz ^ m) (potentialOnPn φ n (frame n j : H)))

def remainderB (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) : ℂ :=
  ∑' j : ℕ, pathTerm φ n z hz (2 * j + 2) false true

def remainderC (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) : ℂ :=
  ∑' j : ℕ, pathTerm φ n z hz (2 * j + 2) true false

/-! ### KST016.02 -/

def correction (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) : EndH :=
  (spectralPn n) * Ring.inverse (1 - qOperator φ n z hz) * potentialOnPn φ n

theorem frame_coe (n : ℤ) (b : Bool) : (frame n b : H) = kstPnFrame n b := by
  cases b <;> rfl

theorem frame_inner (n : ℤ) (i j : Bool) :
    inner ℂ (frame n i : H) (frame n j : H) = if i = j then (1 : ℂ) else 0 := by
  rw [frame_coe, frame_coe]
  exact orthonormal_iff_ite.mp (kstPnFrame_orthonormal n) i j

theorem frame_norm (n : ℤ) (b : Bool) : ‖(frame n b : H)‖ = 1 := by
  rw [frame_coe]
  exact (kstPnFrame_orthonormal n).1 b

theorem inner_frame_Pn (n : ℤ) (b : Bool) (y : H) :
    inner ℂ (kstPnFrame n b) (spectralPn n y) = inner ℂ (kstPnFrame n b) y := by
  have h := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by simpa [kstPnFrame] using h true true
  have hul : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by simpa [kstPnFrame] using h true false
  have hlu : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by simpa [kstPnFrame] using h false true
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by simpa [kstPnFrame] using h false false
  rw [spectralPn_apply]
  cases b
  · simp only [kstPnFrame, Bool.false_eq_true, if_false, inner_add_right, inner_smul_right, hlu, hll]
    ring
  · simp only [kstPnFrame, if_true, inner_add_right, inner_smul_right, huu, hul]
    ring

theorem entry_eq (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (i j : Bool) :
    entry φ n z hz i j =
      (z - (n : ℂ) * Real.pi) * inner ℂ (frame n i : H) (frame n j : H) -
        inner ℂ (frame n i : H) (correction φ n z hz (frame n j : H)) := by
  unfold entry
  change inner ℂ (frame n i : H) ((z - (n : ℂ) * (Real.pi : ℂ)) • (frame n j : H) -
      spectralPn n (Ring.inverse (1 - qOperator φ n z hz) (potentialOnPn φ n (frame n j : H)))) = _
  rw [inner_sub_right, inner_smul_right]
  rfl

theorem entries_correction (φ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
  reducedA φ n z hz =
      inner ℂ (frame n false : H) (correction φ n z hz (frame n false : H)) ∧
  reducedB φ n z hz =
      inner ℂ (frame n false : H) (correction φ n z hz (frame n true : H)) ∧
  reducedC φ n z hz =
      inner ℂ (frame n true : H) (correction φ n z hz (frame n false : H)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold reducedA
    rw [entry_eq, frame_inner]
    simp
  · unfold reducedB
    rw [entry_eq, frame_inner]
    simp
  · unfold reducedC
    rw [entry_eq, frame_inner]
    simp

/-! ### KST016.03 channel parity -/

def InChannel (b : Bool) (f : H) : Prop :=
  ∀ c : Bool, c ≠ b → f c = 0

theorem inner_single_left (b : Bool) (x : SpectralScalarL2) (f : H) :
    inner ℂ (PiLp.single 2 b x : H) f = inner ℂ x (f b) := by
  rw [PiLp.inner_apply, Fintype.sum_bool]
  cases b <;> simp [PiLp.single_apply]

theorem pot_apply (φ : Potential) (n : ℤ) (f : H) :
    potentialOnPn φ n f =
      inner ℂ (kstPnLower n) f •
        (PiLp.single 2 true
          (NlsGge.Schur.fourierMultiplier n
            (NlsGge.Analysis.naturalPhysicalCoverL2 (φ true))) : H) +
      inner ℂ (kstPnUpper n) f •
        (PiLp.single 2 false
          (NlsGge.Schur.fourierMultiplier (-n)
            (NlsGge.Analysis.naturalPhysicalCoverL2 (φ false))) : H) := by
  simp [potentialOnPn, InnerProductSpace.rankOne_apply]

theorem potentialOnPn_flips (φ : Potential) (n : ℤ) (b : Bool)
    (f : H) (hf : InChannel b f) :
  InChannel (!b) (potentialOnPn φ n f) := by
  intro c hc
  have hl : inner ℂ (kstPnLower n) f = inner ℂ (spectralBasis n) (f false) := by
    unfold kstPnLower
    rw [inner_single_left]
  have hu : inner ℂ (kstPnUpper n) f = inner ℂ (spectralBasis (-n)) (f true) := by
    unfold kstPnUpper
    rw [inner_single_left]
  rw [pot_apply]
  cases b
  · -- f in channel false, so f true = 0
    have hft : f true = 0 := hf true (by simp)
    have hc' : c = false := by cases c <;> simp_all
    subst hc'
    rw [hu, hft]
    simp [PiLp.single_apply]
  · have hff : f false = 0 := hf false (by simp)
    have hc' : c = true := by cases c <;> simp_all
    subst hc'
    rw [hl, hff]
    simp [PiLp.single_apply]

theorem qOperator_flips (φ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (b : Bool)
    (f : H) (hf : InChannel b f) :
  InChannel (!b) (qOperator φ n z hz f) := by
  intro c hc
  have hcb : c = b := by cases b <;> cases c <;> simp_all
  subst hcb
  have hz0 : (fourierBasis (T := (2 : ℝ))).repr (0 : SpectralScalarL2) = 0 :=
    LinearIsometryEquiv.map_zero _
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext l
  cases c
  · rw [qOperator_lower_coeff]
    have : f true = 0 := hf true (by simp)
    simp [this, hz0, lp.coeFn_zero, WithLp.ofLp_zero, Pi.zero_apply]
  · rw [qOperator_upper_coeff]
    have : f false = 0 := hf false (by simp)
    simp [this, hz0, lp.coeFn_zero, WithLp.ofLp_zero, Pi.zero_apply]

theorem qOperator_pow_even (φ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (m : ℕ) :
    ∀ (b : Bool) (f : H), InChannel b f → InChannel b ((qOperator φ n z hz ^ (2 * m)) f) := by
  induction m with
  | zero =>
    intro b f hf
    simpa using hf
  | succ m ih =>
    intro b f hf
    have h2 : (qOperator φ n z hz ^ (2 * (m + 1))) f =
        qOperator φ n z hz (qOperator φ n z hz ((qOperator φ n z hz ^ (2 * m)) f)) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ', pow_succ']
      rfl
    rw [h2]
    have h1 := qOperator_flips φ n z hz b _ (ih b f hf)
    have h3 := qOperator_flips φ n z hz (!b) _ h1
    simpa using h3

theorem qOperator_pow_odd (φ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (m : ℕ) (b : Bool) (f : H) (hf : InChannel b f) :
    InChannel (!b) ((qOperator φ n z hz ^ (2 * m + 1)) f) := by
  have h2 : (qOperator φ n z hz ^ (2 * m + 1)) f =
      qOperator φ n z hz ((qOperator φ n z hz ^ (2 * m)) f) := by
    rw [pow_succ']
    rfl
  rw [h2]
  exact qOperator_flips φ n z hz b _ (qOperator_pow_even φ n z hz m b f hf)

theorem frame_inChannel (n : ℤ) (b : Bool) : InChannel b (frame n b : H) := by
  intro c hc
  rw [frame_coe]
  cases b <;> cases c <;> simp_all [kstPnFrame, kstPnUpper, kstPnLower, PiLp.single_apply]

theorem inner_frame_of_channel (n : ℤ) (b : Bool) (w : H) (hw : InChannel (!b) w) :
    inner ℂ (frame n b : H) w = 0 := by
  rw [frame_coe]
  cases b
  · have : w false = 0 := hw false (by simp)
    simp only [kstPnFrame, Bool.false_eq_true, if_false]
    unfold kstPnLower
    rw [inner_single_left, this]
    simp
  · have : w true = 0 := hw true (by simp)
    simp only [kstPnFrame, if_true]
    unfold kstPnUpper
    rw [inner_single_left, this]
    simp

theorem odd_offDiagonal_path_zero (φ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (j : ℕ) :
  pathTerm φ n z hz (2 * j + 1) false true = 0 ∧
  pathTerm φ n z hz (2 * j + 1) true false = 0 := by
  constructor
  · unfold pathTerm
    apply inner_frame_of_channel
    have h1 := potentialOnPn_flips φ n true (frame n true : H) (frame_inChannel n true)
    have h2 := qOperator_pow_odd φ n z hz j false _ (by simpa using h1)
    simpa using h2
  · unfold pathTerm
    apply inner_frame_of_channel
    have h1 := potentialOnPn_flips φ n false (frame n false : H) (frame_inChannel n false)
    have h2 := qOperator_pow_odd φ n z hz j true _ (by simpa using h1)
    simpa using h2

/-! ### KST016.04 -/

theorem fmValue_comp_inv (k : ℤ) (g : SpectralScalarL2) :
    NlsGge.Schur.fourierMultiplierValue (-k) (NlsGge.Schur.fourierMultiplierValue k g) = g := by
  apply Lp.ext
  filter_upwards [NlsGge.Schur.fourierMultiplierValue_ae (-k)
      (NlsGge.Schur.fourierMultiplierValue k g),
    NlsGge.Schur.fourierMultiplierValue_ae k g] with x h1 h2
  rw [h1, h2, ← mul_assoc, ← fourier_add, neg_add_cancel, fourier_zero, one_mul]

theorem fm_comp_inv (k : ℤ) (g : SpectralScalarL2) :
    NlsGge.Schur.fourierMultiplier (-k) (NlsGge.Schur.fourierMultiplier k g) = g :=
  fmValue_comp_inv k g

theorem inner_basis_mul (a k : ℤ) (g : SpectralScalarL2) :
    inner ℂ (spectralBasis a) (NlsGge.Schur.fourierMultiplier k g) = fourierCoeff g (a - k) := by
  let M : SpectralScalarL2 →ₗᵢ[ℂ] SpectralScalarL2 :=
    ⟨(NlsGge.Schur.fourierMultiplier (-k)).toLinearMap,
      fun f => NlsGge.Schur.fourierMultiplier_norm_apply (-k) f⟩
  have h1 : inner ℂ (spectralBasis a) (NlsGge.Schur.fourierMultiplier k g) =
      inner ℂ (M (spectralBasis a)) (M (NlsGge.Schur.fourierMultiplier k g)) :=
    (LinearIsometry.inner_map_map M _ _).symm
  have h2 : M (spectralBasis a) = spectralBasis (-k + a) := by
    change NlsGge.Schur.fourierMultiplier (-k) (spectralBasis a) = _
    exact NlsGge.Schur.fourierMultiplier_basis (-k) a
  have h3 : M (NlsGge.Schur.fourierMultiplier k g) = g := fm_comp_inv k g
  rw [h1, h2, h3]
  have h4 : inner ℂ ((fourierBasis (T := (2 : ℝ))) (-k + a)) g = fourierCoeff g (-k + a) :=
    ((fourierBasis (T := (2 : ℝ))).repr_apply_apply g (-k + a)).symm.trans
      (fourierBasis_repr g (-k + a))
  have e : -k + a = a - k := by ring
  rw [e] at h4 ⊢
  have hb : (fourierBasis (T := (2 : ℝ))) (a - k) = spectralBasis (a - k) := by
    simp [spectralBasis]
  rw [hb] at h4
  exact h4

theorem zeroth_offDiagonal_path (φ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
  pathTerm φ n z hz 0 false true = coveredCoeff φ false (2 * n) ∧
  pathTerm φ n z hz 0 true false = coveredCoeff φ true (-2 * n) := by
  have h := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by simpa [kstPnFrame] using h true true
  have hlu : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by simpa [kstPnFrame] using h false true
  have hul : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by simpa [kstPnFrame] using h true false
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by simpa [kstPnFrame] using h false false
  constructor
  · unfold pathTerm coveredCoeff
    rw [frame_coe, frame_coe]
    simp only [pow_zero, ContinuousLinearMap.one_apply]
    simp only [kstPnFrame, if_true, Bool.false_eq_true, if_false]
    rw [pot_apply, huu, hlu]
    simp only [zero_smul, one_smul, zero_add]
    unfold kstPnLower
    rw [inner_single_left]
    simp only [PiLp.single_apply, if_true]
    rw [inner_basis_mul]
    congr 1
    ring
  · unfold pathTerm coveredCoeff
    rw [frame_coe, frame_coe]
    simp only [pow_zero, ContinuousLinearMap.one_apply]
    simp only [kstPnFrame, if_true, Bool.false_eq_true, if_false]
    rw [pot_apply, hll, hul]
    simp only [zero_smul, one_smul, add_zero]
    unfold kstPnUpper
    rw [inner_single_left]
    simp only [PiLp.single_apply, if_true]
    rw [inner_basis_mul]
    congr 1
    ring


/-! ### KST016.05 -/

theorem inverse_series_of_square_small
    (T : EndH) (hT : ‖T ^ 2‖ < 1) :
  Summable (fun m : ℕ => ‖T ^ m‖) ∧
    HasSum (fun m : ℕ => T ^ m) (Ring.inverse (1 - T)) := by
  have hS : HasSum (fun k : ℕ => (T ^ 2) ^ k) (Ring.inverse (1 - T ^ 2)) :=
    hasSum_geom_series_inverse (T ^ 2) hT
  obtain ⟨_, hinv, _, _⟩ := NlsGge.Atomic.KST012.inverse_one_sub_of_sq_norm_lt T hT
  constructor
  · have hg : Summable (fun k : ℕ => ‖T ^ 2‖ ^ k) := summable_geometric_of_lt_one (norm_nonneg _) hT
    have he : Summable (fun k : ℕ => ‖T ^ (2 * k)‖) := by
      refine Summable.of_norm_bounded_eventually hg ?_
      filter_upwards [Filter.eventually_cofinite_ne 0] with k hk
      rw [norm_norm, pow_mul]
      exact norm_pow_le' _ (Nat.pos_of_ne_zero hk)
    have ho : Summable (fun k : ℕ => ‖T ^ (2 * k + 1)‖) := by
      refine Summable.of_norm_bounded_eventually (hg.mul_left ‖T‖) ?_
      filter_upwards [Filter.eventually_cofinite_ne 0] with k hk
      rw [norm_norm, pow_succ' T (2 * k), pow_mul]
      calc ‖T * (T ^ 2) ^ k‖ ≤ ‖T‖ * ‖(T ^ 2) ^ k‖ := norm_mul_le _ _
        _ ≤ ‖T‖ * ‖T ^ 2‖ ^ k := by
          gcongr
          exact norm_pow_le' _ (Nat.pos_of_ne_zero hk)
    exact Summable.even_add_odd he ho
  · have hev : HasSum (fun k : ℕ => T ^ (2 * k)) (Ring.inverse (1 - T ^ 2)) := by
      simpa only [pow_mul] using hS
    have hod : HasSum (fun k : ℕ => T ^ (2 * k + 1)) (T * Ring.inverse (1 - T ^ 2)) := by
      have h := hS.mul_left T
      have e : (fun k : ℕ => T * (T ^ 2) ^ k) = fun k : ℕ => T ^ (2 * k + 1) := by
        funext k
        rw [pow_succ' T (2 * k), pow_mul]
      rw [e] at h
      exact h
    have h := hev.even_add_odd hod
    have e2 : Ring.inverse (1 - T ^ 2) + T * Ring.inverse (1 - T ^ 2) = Ring.inverse (1 - T) := by
      rw [hinv, add_mul, one_mul]
    rw [e2] at h
    exact h

theorem pathTerm_norm_summable (φ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (hT : ‖qOperator φ n z hz ^ 2‖ < 1)
    (i j : Bool) :
  Summable (fun m : ℕ => ‖pathTerm φ n z hz m i j‖) := by
  have hs := (inverse_series_of_square_small _ hT).1
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    (hs.mul_right ‖potentialOnPn φ n (frame n j : H)‖)
  calc ‖pathTerm φ n z hz m i j‖
      ≤ ‖(frame n i : H)‖ * ‖(qOperator φ n z hz ^ m) (potentialOnPn φ n (frame n j : H))‖ :=
        norm_inner_le_norm _ _
    _ ≤ 1 * (‖qOperator φ n z hz ^ m‖ * ‖potentialOnPn φ n (frame n j : H)‖) := by
        rw [frame_norm]
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖qOperator φ n z hz ^ m‖ * ‖potentialOnPn φ n (frame n j : H)‖ := one_mul _

theorem opNorm_le_actual_hsNorm (S : EndH)
    (hS : NlsGge.Pilot.IsComplexHilbertSchmidt S) :
    ‖S‖ ≤ NlsGge.Pilot.complexHilbertSchmidtNorm S := by
  let b := NlsGge.Pilot.chosenComplexHilbertBasis (E := KSTPairL2)
  have hs := NlsGge.Pilot.summable_basis_of_isComplexHilbertSchmidt b hS
  calc
    ‖S‖ ≤ Real.sqrt (∑' i, ‖S (b i)‖ ^ 2) :=
      NlsGge.Atomic.LIB023.opNorm_le_sqrt_columns b S hs
    _ = NlsGge.Pilot.complexHilbertSchmidtNorm S :=
      (NlsGge.Pilot.complexHilbertSchmidtNorm_eq_basis b hs).symm

/-! ### KST016.06 -/

theorem tsum_even_split (f : ℕ → ℂ) (hs : Summable (fun m => ‖f m‖))
    (hodd : ∀ j : ℕ, f (2 * j + 1) = 0) :
    ∑' m, f m = f 0 + ∑' j : ℕ, f (2 * j + 2) := by
  have hf : Summable f := hs.of_norm
  have he : Summable (fun k : ℕ => f (2 * k)) :=
    hf.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simp at h; omega)
  have ho : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hf.comp_injective (i := fun k : ℕ => 2 * k + 1) (fun a b h => by simp at h; omega)
  rw [← tsum_even_add_odd he ho]
  have hodd0 : ∑' k : ℕ, f (2 * k + 1) = 0 := by simp [hodd]
  rw [hodd0, add_zero, he.tsum_eq_zero_add]
  simp [mul_add]

theorem reducedBC_fourier_remainders (φ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (hT : ‖qOperator φ n z hz ^ 2‖ < 1) :
  Summable (fun j : ℕ => ‖pathTerm φ n z hz (2 * j + 2) false true‖) ∧
  Summable (fun j : ℕ => ‖pathTerm φ n z hz (2 * j + 2) true false‖) ∧
  reducedB φ n z hz = coveredCoeff φ false (2 * n) + remainderB φ n z hz ∧
  reducedC φ n z hz = coveredCoeff φ true (-2 * n) + remainderC φ n z hz := by
  have hseries := (inverse_series_of_square_small _ hT).2
  have hhas : ∀ i j : Bool, HasSum (fun m : ℕ => pathTerm φ n z hz m i j)
      (inner ℂ (frame n i : H)
        (Ring.inverse (1 - qOperator φ n z hz) (potentialOnPn φ n (frame n j : H)))) := by
    intro i j
    let L : EndH →L[ℂ] ℂ := (innerSL ℂ (frame n i : H)).comp
      (ContinuousLinearMap.apply ℂ H (potentialOnPn φ n (frame n j : H)))
    exact hseries.mapL L
  have hcorr : ∀ i j : Bool, inner ℂ (frame n i : H) (correction φ n z hz (frame n j : H)) =
      inner ℂ (frame n i : H)
        (Ring.inverse (1 - qOperator φ n z hz) (potentialOnPn φ n (frame n j : H))) := by
    intro i j
    change inner ℂ (frame n i : H) (spectralPn n
      (Ring.inverse (1 - qOperator φ n z hz) (potentialOnPn φ n (frame n j : H)))) = _
    rw [frame_coe, inner_frame_Pn]
  have hsm := pathTerm_norm_summable φ n z hz hT
  have hent := entries_correction φ n z hz
  have hodd := odd_offDiagonal_path_zero φ n z hz
  have hzero := zeroth_offDiagonal_path φ n z hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hsm false true).comp_injective (i := fun j : ℕ => 2 * j + 2)
      (fun a b h => by simp at h; omega)
  · exact (hsm true false).comp_injective (i := fun j : ℕ => 2 * j + 2)
      (fun a b h => by simp at h; omega)
  · rw [hent.2.1, hcorr, ← (hhas false true).tsum_eq,
      tsum_even_split _ (hsm false true) (fun j => (hodd j).1), hzero.1]
    rfl
  · rw [hent.2.2, hcorr, ← (hhas true false).tsum_eq,
      tsum_even_split _ (hsm true false) (fun j => (hodd j).2), hzero.2]
    rfl



/-! ### KST016.07 L2-linear parameter maps -/

theorem fc_repr (g : SpectralScalarL2) (k : ℤ) :
    fourierCoeff g k = (fourierBasis (T := (2 : ℝ))).repr g k := (fourierBasis_repr g k).symm

theorem sq_summable_repr (g : SpectralScalarL2) :
    Summable (fun k : ℤ => ‖fourierCoeff g k‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num)
    ((fourierBasis (T := (2 : ℝ))).repr g)
  have h2 := h.summable
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, fc_repr] using h2

theorem cr_le_one (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (k : ℤ) :
    ‖complementaryResolventCoeff n z k‖ ≤ 1 := by
  by_cases hk : k = n
  · subst hk
    simp
  · have hb := complementaryResolventCoeff_bound n k z hz
    have hn : (1 : ℝ) ≤ (Int.natAbs (k - n) : ℝ) := by
      have : 0 < Int.natAbs (k - n) := Int.natAbs_pos.mpr (sub_ne_zero.mpr hk)
      exact_mod_cast this
    calc ‖complementaryResolventCoeff n z k‖ ≤ 1 / (Int.natAbs (k - n) : ℝ) := hb
      _ ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact hn

theorem conv_summable (a b c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1)
    (ha : Summable (fun k => ‖a k‖ ^ 2)) (hb : Summable (fun m => ‖b m‖ ^ 2)) (l : ℤ) :
    Summable (fun m : ℤ => a (l - m) * (c m * b m)) := by
  have ha' : Summable (fun m : ℤ => ‖a (l - m)‖ ^ 2) :=
    ha.comp_injective (sub_right_injective (b := l))
  refine Summable.of_norm_bounded (ha'.add hb) (fun m => ?_)
  rw [norm_mul, norm_mul]
  have h1 : ‖c m‖ * ‖b m‖ ≤ ‖b m‖ := by
    nlinarith [norm_nonneg (b m), hc m]
  nlinarith [sq_nonneg (‖a (l - m)‖ - ‖b m‖), norm_nonneg (a (l - m)), norm_nonneg (b m),
    mul_le_mul_of_nonneg_left h1 (norm_nonneg (a (l - m)))]

theorem coe_repr_add (x y : SpectralScalarL2) (k : ℤ) :
    (fourierBasis (T := (2 : ℝ))).repr (x + y) k =
      (fourierBasis (T := (2 : ℝ))).repr x k + (fourierBasis (T := (2 : ℝ))).repr y k := by
  have h := congrArg (fun w : lp (fun _ : ℤ => ℂ) 2 => (w : ℤ → ℂ) k)
    ((fourierBasis (T := (2 : ℝ))).repr.map_add x y)
  exact h

theorem coe_repr_smul (c : ℂ) (x : SpectralScalarL2) (k : ℤ) :
    (fourierBasis (T := (2 : ℝ))).repr (c • x) k = c * (fourierBasis (T := (2 : ℝ))).repr x k := by
  have h := congrArg (fun w : lp (fun _ : ℤ => ℂ) 2 => (w : ℤ → ℂ) k)
    ((fourierBasis (T := (2 : ℝ))).repr.map_smul c x)
  exact h

theorem A_add (φ ψ : Potential) (b : Bool) (k : ℤ) :
    fourierCoeff (naturalPhysicalCoverL2 ((φ + ψ) b)) k =
      fourierCoeff (naturalPhysicalCoverL2 (φ b)) k +
        fourierCoeff (naturalPhysicalCoverL2 (ψ b)) k := by
  rw [fc_repr, fc_repr, fc_repr]
  have h : (φ + ψ) b = φ b + ψ b := rfl
  rw [h, map_add, coe_repr_add]

theorem A_smul (c : ℂ) (φ : Potential) (b : Bool) (k : ℤ) :
    fourierCoeff (naturalPhysicalCoverL2 ((c • φ) b)) k =
      c * fourierCoeff (naturalPhysicalCoverL2 (φ b)) k := by
  rw [fc_repr, fc_repr]
  have h : (c • φ) b = c • φ b := rfl
  rw [h, map_smul, coe_repr_smul]

theorem qOperator_add (φ ψ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
  qOperator (φ + ψ) n z hz = qOperator φ n z hz + qOperator ψ n z hz := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro c
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext l
  have hcr := cr_le_one n z hz
  have hfsq : ∀ b : Bool, Summable (fun m : ℤ =>
      ‖(fourierBasis (T := (2 : ℝ))).repr (f b) m‖ ^ 2) := fun b => by
    simpa only [fc_repr] using sq_summable_repr (f b)
  cases c
  · have hR : ((qOperator φ n z hz + qOperator ψ n z hz) f) false =
        (qOperator φ n z hz f) false + (qOperator ψ n z hz f) false := rfl
    have hsum : ∀ χ : Potential, Summable (fun m : ℤ =>
        fourierCoeff (naturalPhysicalCoverL2 (χ false)) (l - m) *
          (complementaryResolventCoeff n z (-m) *
            (fourierBasis (T := (2 : ℝ))).repr (f true) m)) := fun χ =>
      conv_summable (fun k => fourierCoeff (naturalPhysicalCoverL2 (χ false)) k)
        (fun m => (fourierBasis (T := (2 : ℝ))).repr (f true) m)
        (fun m => complementaryResolventCoeff n z (-m)) (fun m => hcr _)
        (sq_summable_repr _) (hfsq true) l
    rw [hR, coe_repr_add, qOperator_lower_coeff, qOperator_lower_coeff, qOperator_lower_coeff,
      ← (hsum φ).tsum_add (hsum ψ)]
    congr 1
    funext m
    rw [A_add]
    ring
  · have hR : ((qOperator φ n z hz + qOperator ψ n z hz) f) true =
        (qOperator φ n z hz f) true + (qOperator ψ n z hz f) true := rfl
    have hsum : ∀ χ : Potential, Summable (fun m : ℤ =>
        fourierCoeff (naturalPhysicalCoverL2 (χ true)) (l - m) *
          (complementaryResolventCoeff n z m *
            (fourierBasis (T := (2 : ℝ))).repr (f false) m)) := fun χ =>
      conv_summable (fun k => fourierCoeff (naturalPhysicalCoverL2 (χ true)) k)
        (fun m => (fourierBasis (T := (2 : ℝ))).repr (f false) m)
        (fun m => complementaryResolventCoeff n z m) (fun m => hcr _)
        (sq_summable_repr _) (hfsq false) l
    rw [hR, coe_repr_add, qOperator_upper_coeff, qOperator_upper_coeff, qOperator_upper_coeff,
      ← (hsum φ).tsum_add (hsum ψ)]
    congr 1
    funext m
    rw [A_add]
    ring

theorem qOperator_smul (c : ℂ) (φ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
  qOperator (c • φ) n z hz = c • qOperator φ n z hz := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro b
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext l
  cases b
  · have hR : ((c • qOperator φ n z hz) f) false = c • (qOperator φ n z hz f) false := rfl
    rw [hR, coe_repr_smul, qOperator_lower_coeff, qOperator_lower_coeff, ← tsum_mul_left]
    congr 1
    funext m
    rw [A_smul]
    ring
  · have hR : ((c • qOperator φ n z hz) f) true = c • (qOperator φ n z hz f) true := rfl
    rw [hR, coe_repr_smul, qOperator_upper_coeff, qOperator_upper_coeff, ← tsum_mul_left]
    congr 1
    funext m
    rw [A_smul]
    ring

theorem single_add' (b : Bool) (x y : SpectralScalarL2) :
    (PiLp.single 2 b (x + y) : H) = PiLp.single 2 b x + PiLp.single 2 b y := by
  apply PiLp.ext
  intro c
  cases b <;> cases c <;> simp [PiLp.single_apply]

theorem single_smul' (b : Bool) (a : ℂ) (x : SpectralScalarL2) :
    (PiLp.single 2 b (a • x) : H) = a • PiLp.single 2 b x := by
  apply PiLp.ext
  intro c
  cases b <;> cases c <;> simp [PiLp.single_apply]

theorem potentialOnPn_add (φ ψ : Potential) (n : ℤ) :
  potentialOnPn (φ + ψ) n = potentialOnPn φ n + potentialOnPn ψ n := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.add_apply, pot_apply, pot_apply, pot_apply]
  have h1 : (φ + ψ) true = φ true + ψ true := rfl
  have h2 : (φ + ψ) false = φ false + ψ false := rfl
  rw [h1, h2]
  simp only [map_add, single_add', smul_add]
  abel

theorem potentialOnPn_smul (c : ℂ) (φ : Potential) (n : ℤ) :
  potentialOnPn (c • φ) n = c • potentialOnPn φ n := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.smul_apply, pot_apply, pot_apply]
  have h1 : (c • φ) true = c • φ true := rfl
  have h2 : (c • φ) false = c • φ false := rfl
  rw [h1, h2]
  simp only [map_smul, single_smul', smul_add, smul_comm c]

theorem potentialOnPn_norm_le (φ : Potential) (n : ℤ) :
  ‖potentialOnPn φ n‖ ≤ 2 * ‖φ‖ := by
  unfold potentialOnPn
  refine (norm_add_le _ _).trans ?_
  rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne, PiLp.norm_single,
    PiLp.norm_single]
  have hl : ‖kstPnLower n‖ = 1 := by simpa [kstPnFrame] using (kstPnFrame_orthonormal n).1 false
  have hu : ‖kstPnUpper n‖ = 1 := by simpa [kstPnFrame] using (kstPnFrame_orthonormal n).1 true
  rw [hl, hu, mul_one, mul_one, NlsGge.Schur.fourierMultiplier_norm_apply,
    NlsGge.Schur.fourierMultiplier_norm_apply, LinearIsometry.norm_map, LinearIsometry.norm_map]
  have ht : ‖φ true‖ ≤ ‖φ‖ := PiLp.norm_apply_le φ true
  have hf : ‖φ false‖ ≤ ‖φ‖ := PiLp.norm_apply_le φ false
  linarith

/-! ### KST016.08 -/

def qParameter (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n) :
    Potential →L[ℂ] EndH :=
  LinearMap.mkContinuous
    { toFun := fun φ => qOperator φ n z₀ hz₀
      map_add' := fun φ ψ => qOperator_add φ ψ n z₀ hz₀
      map_smul' := fun c φ => qOperator_smul c φ n z₀ hz₀ }
    2 (fun φ => NlsGge.Atomic.KST006.norm_qOperator_le φ n z₀ hz₀)

def potentialParameter (n : ℤ) : Potential →L[ℂ] EndH :=
  LinearMap.mkContinuous
    { toFun := fun φ => potentialOnPn φ n
      map_add' := fun φ ψ => potentialOnPn_add φ ψ n
      map_smul' := fun c φ => potentialOnPn_smul c φ n }
    2 (fun φ => potentialOnPn_norm_le φ n)

def localFreeFactor (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n)
    (p : ℂ × Potential) : EndH :=
  1 + (p.1 - z₀) • complementaryMultiplier n z₀ hz₀

def localQ (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n)
    (p : ℂ × Potential) : EndH :=
  qParameter n z₀ hz₀ p.2 * Ring.inverse (localFreeFactor n z₀ hz₀ p)

def localCorrection (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n)
    (p : ℂ × Potential) : EndH :=
  spectralPn n * Ring.inverse (1 - localQ n z₀ hz₀ p) * potentialParameter n p.2

def localABC (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n)
    (p : ℂ × Potential) : ℂ × ℂ × ℂ :=
  (inner ℂ (frame n false : H) (localCorrection n z₀ hz₀ p (frame n false : H)),
   inner ℂ (frame n false : H) (localCorrection n z₀ hz₀ p (frame n true : H)),
   inner ℂ (frame n true : H) (localCorrection n z₀ hz₀ p (frame n false : H)))

def localInverseDomain (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n) :
    Set (ℂ × Potential) :=
  {p | IsUnit (localFreeFactor n z₀ hz₀ p) ∧
    IsUnit (1 - localQ n z₀ hz₀ p)}

theorem qParameter_apply (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n) (φ : Potential) :
    qParameter n z₀ hz₀ φ = qOperator φ n z₀ hz₀ := rfl

theorem potentialParameter_apply (n : ℤ) (φ : Potential) :
    potentialParameter n φ = potentialOnPn φ n := rfl

/-! ### KST016.09 -/

theorem cr_identity (n : ℤ) (z₀ z : ℂ) (hz₀ : z₀ ∈ spectralStrip n) (hz : z ∈ spectralStrip n)
    (k : ℤ) :
    complementaryResolventCoeff n z k *
      (1 + (z - z₀) * complementaryResolventCoeff n z₀ k) =
      complementaryResolventCoeff n z₀ k := by
  by_cases hk : k = n
  · subst hk
    simp
  · have h1 := complementary_denominator_ne_zero n k z hz hk
    have h0 := complementary_denominator_ne_zero n k z₀ hz₀ hk
    simp only [complementaryResolventCoeff, hk, if_false]
    field_simp
    ring

theorem compMult_component (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (f : H) (c : Bool) :
    (complementaryMultiplier n z hz f) c = scalarComplementaryMultiplier n z hz c (f c) := rfl

theorem compMult_repr (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (f : H) (c : Bool) (m : ℤ) :
    (fourierBasis (T := (2 : ℝ))).repr ((complementaryMultiplier n z hz f) c) m =
      complementaryResolventCoeff n z (sourceModeIndex c m) *
        (fourierBasis (T := (2 : ℝ))).repr (f c) m := by
  rw [compMult_component, scalarComplementaryMultiplier_repr]

theorem compMult_comp_free (n : ℤ) (z₀ z : ℂ) (hz₀ : z₀ ∈ spectralStrip n)
    (hz : z ∈ spectralStrip n) :
    complementaryMultiplier n z hz * (1 + (z - z₀) • complementaryMultiplier n z₀ hz₀) =
      complementaryMultiplier n z₀ hz₀ := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro c
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext m
  have hF : ((1 + (z - z₀) • complementaryMultiplier n z₀ hz₀) f) c =
      f c + (z - z₀) • (complementaryMultiplier n z₀ hz₀ f) c := rfl
  have e1 : (complementaryMultiplier n z hz * (1 + (z - z₀) • complementaryMultiplier n z₀ hz₀)) f =
      complementaryMultiplier n z hz ((1 + (z - z₀) • complementaryMultiplier n z₀ hz₀) f) := rfl
  rw [e1, compMult_repr, hF, coe_repr_add, coe_repr_smul, compMult_repr]
  have h := cr_identity n z₀ z hz₀ hz (sourceModeIndex c m)
  linear_combination ((fourierBasis (T := (2 : ℝ))).repr (f c) m) * h

theorem q_coeff_via_D (φ : Potential) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (f : H)
    (c : Bool) (l : ℤ) :
    (fourierBasis (T := (2 : ℝ))).repr ((qOperator φ n z hz f) c) l =
      ∑' m : ℤ, fourierCoeff (naturalPhysicalCoverL2 (φ c)) (l - m) *
        (fourierBasis (T := (2 : ℝ))).repr ((complementaryMultiplier n z hz f) (!c)) m := by
  cases c
  · rw [qOperator_lower_coeff]
    refine tsum_congr (fun m => ?_)
    rw [compMult_repr]
    simp [sourceModeIndex]
  · rw [qOperator_upper_coeff]
    refine tsum_congr (fun m => ?_)
    rw [compMult_repr]
    simp [sourceModeIndex]

theorem qOperator_eq_comp_inv (φ : Potential) (n : ℤ) (z₀ z : ℂ)
    (hz₀ : z₀ ∈ spectralStrip n) (hz : z ∈ spectralStrip n)
    (hfree : IsUnit (1 + (z - z₀) • complementaryMultiplier n z₀ hz₀)) :
    qOperator φ n z hz =
      qOperator φ n z₀ hz₀ * Ring.inverse (1 + (z - z₀) • complementaryMultiplier n z₀ hz₀) := by
  set F : EndH := 1 + (z - z₀) • complementaryMultiplier n z₀ hz₀ with hFdef
  apply ContinuousLinearMap.ext
  intro f
  have hD : complementaryMultiplier n z₀ hz₀ (Ring.inverse F f) =
      complementaryMultiplier n z hz f := by
    have h1 := compMult_comp_free n z₀ z hz₀ hz
    have h2 : F * Ring.inverse F = 1 := Ring.mul_inverse_cancel F hfree
    calc complementaryMultiplier n z₀ hz₀ (Ring.inverse F f)
        = (complementaryMultiplier n z hz * F) (Ring.inverse F f) := by rw [h1]
      _ = complementaryMultiplier n z hz ((F * Ring.inverse F) f) := rfl
      _ = complementaryMultiplier n z hz f := by rw [h2]; rfl
  apply PiLp.ext
  intro c
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext l
  have e : (qOperator φ n z₀ hz₀ * Ring.inverse F) f = qOperator φ n z₀ hz₀ (Ring.inverse F f) := rfl
  rw [e, q_coeff_via_D, q_coeff_via_D, hD]

theorem qOperator_local_resolvent_identity
    (φ : Potential) (n : ℤ) (z₀ z : ℂ)
    (hz₀ : z₀ ∈ spectralStrip n) (hz : z ∈ spectralStrip n)
    (hfree : IsUnit (localFreeFactor n z₀ hz₀ (z, φ))) :
  localQ n z₀ hz₀ (z, φ) = qOperator φ n z hz := by
  unfold localQ
  rw [qParameter_apply]
  exact (qOperator_eq_comp_inv φ n z₀ z hz₀ hz hfree).symm

theorem localABC_agrees
    (φ : Potential) (n : ℤ) (z₀ z : ℂ)
    (hz₀ : z₀ ∈ spectralStrip n) (hz : z ∈ spectralStrip n)
    (hfree : IsUnit (localFreeFactor n z₀ hz₀ (z, φ))) :
  localABC n z₀ hz₀ (z, φ) =
    (reducedA φ n z hz, reducedB φ n z hz, reducedC φ n z hz) := by
  have hq := qOperator_local_resolvent_identity φ n z₀ z hz₀ hz hfree
  have hc : localCorrection n z₀ hz₀ (z, φ) = correction φ n z hz := by
    unfold localCorrection correction
    rw [hq]
    rfl
  obtain ⟨hA, hB, hC⟩ := entries_correction φ n z hz
  unfold localABC
  rw [hc, hA, hB, hC]

/-! ### KST016.10 -/

theorem isOpen_isUnit_endH : IsOpen {T : EndH | IsUnit T} := Units.isOpen

theorem continuous_localFreeFactor (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n) :
    Continuous (localFreeFactor n z₀ hz₀) := by
  unfold localFreeFactor
  exact continuous_const.add ((continuous_fst.sub continuous_const).smul continuous_const)

theorem localInverseDomain_open (n : ℤ) (z₀ : ℂ)
    (hz₀ : z₀ ∈ spectralStrip n) :
  IsOpen (localInverseDomain n z₀ hz₀) := by
  have hFc := continuous_localFreeFactor n z₀ hz₀
  have hU1 : IsOpen {p : ℂ × Potential | IsUnit (localFreeFactor n z₀ hz₀ p)} :=
    isOpen_isUnit_endH.preimage hFc
  have hQc : ContinuousOn (fun p : ℂ × Potential => 1 - localQ n z₀ hz₀ p)
      {p | IsUnit (localFreeFactor n z₀ hz₀ p)} := by
    intro p hp
    have hinv : ContinuousAt (fun p : ℂ × Potential => Ring.inverse (localFreeFactor n z₀ hz₀ p)) p := by
      have h1 := NormedRing.inverse_continuousAt hp.unit
      have h2 : ContinuousAt (localFreeFactor n z₀ hz₀) p := hFc.continuousAt
      have h3 : (hp.unit : EndH) = localFreeFactor n z₀ hz₀ p := hp.unit_spec
      rw [h3] at h1
      exact h1.comp h2
    have hq : ContinuousAt (fun p : ℂ × Potential => qParameter n z₀ hz₀ p.2) p :=
      ((qParameter n z₀ hz₀).continuous.comp continuous_snd).continuousAt
    exact (continuousAt_const.sub (hq.mul hinv)).continuousWithinAt
  have := hQc.isOpen_inter_preimage hU1 isOpen_isUnit_endH
  convert this using 1
  ext p
  simp [localInverseDomain, Set.mem_inter_iff, and_comm]


theorem analyticAt_localFreeFactor (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n)
    (p : ℂ × Potential) : AnalyticAt ℂ (localFreeFactor n z₀ hz₀) p := by
  unfold localFreeFactor
  exact analyticAt_const.add ((analyticAt_fst.sub analyticAt_const).smul analyticAt_const)

theorem analyticAt_localQ (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n) (p : ℂ × Potential)
    (hp : IsUnit (localFreeFactor n z₀ hz₀ p)) : AnalyticAt ℂ (localQ n z₀ hz₀) p := by
  have hF := analyticAt_localFreeFactor n z₀ hz₀ p
  have hinv : AnalyticAt ℂ (fun q => Ring.inverse (localFreeFactor n z₀ hz₀ q)) p := by
    have h1 := analyticAt_inverse (𝕜 := ℂ) (A := EndH) hp.unit
    rw [IsUnit.unit_spec] at h1
    exact h1.comp hF
  have hq : AnalyticAt ℂ (fun q : ℂ × Potential => qParameter n z₀ hz₀ q.2) p :=
    ((qParameter n z₀ hz₀).analyticAt _).comp analyticAt_snd
  have hdef : localQ n z₀ hz₀ = fun q => qParameter n z₀ hz₀ q.2 *
      Ring.inverse (localFreeFactor n z₀ hz₀ q) := rfl
  rw [hdef]
  exact hq.mul hinv

theorem analyticAt_localCorrection (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n)
    (p : ℂ × Potential) (hp : p ∈ localInverseDomain n z₀ hz₀) :
    AnalyticAt ℂ (localCorrection n z₀ hz₀) p := by
  have hq := analyticAt_localQ n z₀ hz₀ p hp.1
  have hinv : AnalyticAt ℂ (fun q => Ring.inverse (1 - localQ n z₀ hz₀ q)) p := by
    have h1 := analyticAt_inverse (𝕜 := ℂ) (A := EndH) hp.2.unit
    rw [IsUnit.unit_spec] at h1
    have hsub : AnalyticAt ℂ (fun q => (1 : EndH) - localQ n z₀ hz₀ q) p :=
      analyticAt_const.sub hq
    exact h1.comp_of_eq hsub rfl
  have hpot : AnalyticAt ℂ (fun q : ℂ × Potential => potentialParameter n q.2) p :=
    ((potentialParameter n).analyticAt _).comp analyticAt_snd
  have hdef : localCorrection n z₀ hz₀ = fun q => spectralPn n * Ring.inverse (1 - localQ n z₀ hz₀ q) *
      potentialParameter n q.2 := rfl
  rw [hdef]
  exact (analyticAt_const.mul hinv).mul hpot

theorem localABC_analyticOnNhd (n : ℤ) (z₀ : ℂ)
    (hz₀ : z₀ ∈ spectralStrip n) :
  AnalyticOnNhd ℂ (localABC n z₀ hz₀) (localInverseDomain n z₀ hz₀) := by
  intro p hp
  have hC := analyticAt_localCorrection n z₀ hz₀ p hp
  have hcomp : ∀ i j : Bool, AnalyticAt ℂ (fun q : ℂ × Potential =>
      inner ℂ (frame n i : H) (localCorrection n z₀ hz₀ q (frame n j : H))) p := by
    intro i j
    let L : EndH →L[ℂ] ℂ := (innerSL ℂ (frame n i : H)).comp
      (ContinuousLinearMap.apply ℂ H (frame n j : H))
    have hL : AnalyticAt ℂ L (localCorrection n z₀ hz₀ p) := L.analyticAt _
    have hc := hL.comp hC
    have e : (fun q : ℂ × Potential =>
        inner ℂ (frame n i : H) (localCorrection n z₀ hz₀ q (frame n j : H))) =
        L ∘ localCorrection n z₀ hz₀ := by
      funext q
      rfl
    rw [e]
    exact hc
  show AnalyticAt ℂ (fun q : ℂ × Potential =>
    (inner ℂ (frame n false : H) (localCorrection n z₀ hz₀ q (frame n false : H)),
     inner ℂ (frame n false : H) (localCorrection n z₀ hz₀ q (frame n true : H)),
     inner ℂ (frame n true : H) (localCorrection n z₀ hz₀ q (frame n false : H)))) p
  exact (hcomp false false).prod ((hcomp false true).prod (hcomp true false))

theorem reducedABC_joint_analytic (φ : Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n)
    (hunit : IsUnit (1 - qOperator φ n z hz)) :
  AnalyticAt ℂ (localABC n z hz) (z, φ) := by
  have hF : localFreeFactor n z hz (z, φ) = 1 := by
    have h0 : ((z - z) • complementaryMultiplier n z hz : EndH) = 0 := by
      apply ContinuousLinearMap.ext
      intro f
      simp
    show (1 : EndH) + (z - z) • complementaryMultiplier n z hz = 1
    rw [h0, add_zero]
  have hmem : (z, φ) ∈ localInverseDomain n z hz := by
    refine ⟨?_, ?_⟩
    · rw [hF]
      exact isUnit_one
    · have : localQ n z hz (z, φ) = qOperator φ n z hz := by
        unfold localQ
        rw [hF, Ring.inverse_one, mul_one]
        rfl
      rw [this]
      exact hunit
  exact localABC_analyticOnNhd n z hz _ hmem

/-! ### KST016.11 -/

theorem reducedBC_uniform_local (φ₀ : Potential) :
  ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, 5 ≤ N₀ ∧
    ∀ φ : Potential, ‖φ - φ₀‖ < ε →
      ∀ n : ℤ, N₀ ≤ n.natAbs →
        ∀ z : ℂ, ∀ hz : z ∈ spectralStrip n,
          ‖qOperator φ n z hz ^ 2‖ ≤ (1 / 2 : ℝ) ∧
          reducedB φ n z hz =
            coveredCoeff φ false (2 * n) + remainderB φ n z hz ∧
          reducedC φ n z hz =
            coveredCoeff φ true (-2 * n) + remainderC φ n z hz ∧
          AnalyticAt ℂ (localABC n z hz) (z, φ) := by
  obtain ⟨ε, hε, N₀, hN₀, hlocal⟩ := NlsGge.Atomic.KST011.hs_qOperator_sq_decay φ₀
  refine ⟨ε, hε, N₀, hN₀, ?_⟩
  intro φ hφ n hn z hz
  have hsq := (hlocal φ hφ n hn).2 z hz
  have hfinite : NlsGge.Pilot.IsComplexHilbertSchmidt (qOperator φ n z hz ^ 2) := by
    simpa only [pow_two, ContinuousLinearMap.mul_def] using hsq.1
  have hbound : NlsGge.Pilot.complexHilbertSchmidtNorm (qOperator φ n z hz ^ 2) ≤ (1 / 2 : ℝ) := by
    simpa only [pow_two, ContinuousLinearMap.mul_def] using hsq.2
  have hn2 : ‖qOperator φ n z hz ^ 2‖ ≤ (1 / 2 : ℝ) :=
    (opNorm_le_actual_hsNorm _ hfinite).trans hbound
  have hlt : ‖qOperator φ n z hz ^ 2‖ < 1 := lt_of_le_of_lt hn2 (by norm_num)
  obtain ⟨_, _, hB, hC⟩ := reducedBC_fourier_remainders φ n z hz hlt
  obtain ⟨hunit, -⟩ := NlsGge.Atomic.KST012.inverse_one_sub_of_sq_norm_lt (qOperator φ n z hz) hlt
  exact ⟨hn2, hB, hC, reducedABC_joint_analytic φ n z hz hunit⟩

end NlsGge.Atomic.KST016
