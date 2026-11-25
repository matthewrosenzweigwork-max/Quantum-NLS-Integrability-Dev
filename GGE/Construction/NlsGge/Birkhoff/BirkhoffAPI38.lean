import NlsGge.Birkhoff.BirkhoffInput38
import NlsGge.Spectral.ActualActionSumE02_38
import NlsGge.Spectral.ActualGapActionAllNE02_38
import Mathlib.Tactic

/-! # Birkhoff API layer A1 (conditional on `B : BirkhoffTop38` (parent of `BirkhoffInput38`))

Design: `campaign/BIRKHOFF_LAYER_DESIGN.md` §5, items A1.1-A1.7; review notes N1-N5 in
`NlsGge/Birkhoff/REVIEW_BIRKHOFF_INPUT_20261012.md`.

Every declaration mentioning `B` / `O` is conditional on those inputs (E01 / E04 stay open).
Declarations not mentioning `B` are unconditional Φ-free facts.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations
open scoped ENNReal

/-! ## A1.1 `seqSobolev38 r ↔ SobolevSquareSummable r`, and the `0` transport (N3) -/

theorem mem_seqSobolev38_iff (r : ℝ) (x : ℤ → ℂ) :
    x ∈ seqSobolev38 r ↔ SobolevSquareSummable r x := by
  change Memℓp (weightedCoordinates (sobolevModeWeight r) x) 2 ↔ _
  rw [weightedCoordinates_mem_l2_iff (sobolevModeWeight r)
    (fun n => (Real.rpow_pos_of_pos (japaneseBracket_pos n) _).le)]
  rfl

theorem seqSobolev38_mono {r s : ℝ} (hrs : r ≤ s) {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 s) :
    x ∈ seqSobolev38 r :=
  (mem_seqSobolev38_iff r x).2
    (sobolevSquareSummable_restrict r s hrs x ((mem_seqSobolev38_iff s x).1 hx))

/-- N3: `seqSobolev38 ((0:ℕ):ℝ) = seqSobolev38 0` (via `Nat.cast_zero`). -/
theorem seqSobolev38_natCast_zero : seqSobolev38 ((0 : ℕ) : ℝ) = seqSobolev38 0 := by
  rw [Nat.cast_zero]

theorem mem_seqSobolev38_natCast_zero_iff (x : ℤ → ℂ) :
    x ∈ seqSobolev38 ((0 : ℕ) : ℝ) ↔ x ∈ seqSobolev38 0 := by
  rw [seqSobolev38_natCast_zero]

theorem seqSobolev38_natCast_mono {m : ℕ} {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 (m : ℝ)) :
    x ∈ seqSobolev38 0 :=
  seqSobolev38_mono (Nat.cast_nonneg m) hx

/-- `h⁰` is the unweighted `ℓ²`. -/
theorem mem_seqSobolev38_zero_iff (x : ℤ → ℂ) :
    x ∈ seqSobolev38 0 ↔ Memℓp x 2 := by
  rw [mem_seqSobolev38_iff, memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [SobolevSquareSummable, mul_zero, Real.rpow_eq_pow, Real.rpow_zero, one_mul,
    ENNReal.toReal_ofNat, Real.rpow_two]

/-- A sequence of `h⁰` as an element of mathlib's `ℓ²`. -/
def seqToLp38 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨x, (mem_seqSobolev38_zero_iff x).1 hx⟩

/-- Transport of a carrier element across `Nat.cast_zero`. -/
def carrierZero38 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) : SobolevCarrier38 ((0 : ℕ) : ℝ) :=
  carrierMk38 ((0 : ℕ) : ℝ) x ((mem_seqSobolev38_natCast_zero_iff x).2 hx)

@[simp] theorem carrierCoe38_carrierZero38 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) :
    carrierCoe38 ((0 : ℕ) : ℝ) (carrierZero38 x hx) = x := rfl

theorem carrierCoe38_mem_zero (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    carrierCoe38 ((0 : ℕ) : ℝ) x ∈ seqSobolev38 0 :=
  (mem_seqSobolev38_natCast_zero_iff _).1 (carrierCoe38_mem _ x)

theorem carrierZero38_coe (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    carrierZero38 (carrierCoe38 ((0 : ℕ) : ℝ) x) (carrierCoe38_mem_zero x) = x := rfl

/-! ## A1.2 Physical side via `reflectedFourierL2` -/

theorem fourierSeq38_apply (u : PhysicalL2) (n : ℤ) :
    fourierSeq38 u n = -physicalFourier u (-n) := by
  show reflectedFourierL2 u n = _
  rw [reflectedFourierL2_apply]; rfl

theorem sobolevModeWeight_neg (r : ℝ) (n : ℤ) : sobolevModeWeight r (-n) = sobolevModeWeight r n := by
  simp [sobolevModeWeight, japaneseBracket]

/-- `𝓕u ∈ h^r ↔ physicalFourier u` is `H^r`-square-summable (reflection invariance of `⟨n⟩`). -/
theorem fourierSeq38_mem_iff (r : ℝ) (u : PhysicalL2) :
    fourierSeq38 u ∈ seqSobolev38 r ↔ SobolevSquareSummable r (physicalFourier u) := by
  rw [mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  rw [← (Equiv.neg ℤ).summable_iff]
  refine summable_congr (fun n => ?_)
  simp only [Function.comp, Equiv.neg_apply, fourierSeq38_apply, norm_neg, neg_neg]
  have hb : japaneseBracket (-n) = japaneseBracket n := by simp [japaneseBracket]
  rw [hb]

theorem fourierSeq38_mem_zero (u : PhysicalL2) : fourierSeq38 u ∈ seqSobolev38 0 :=
  (mem_seqSobolev38_zero_iff _).2 (lp.memℓp (reflectedFourierL2 u))

/-- The physical field with `𝓕 u = x` (inverse of `reflectedFourierL2` on `h⁰`). -/
def physInv38 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) : PhysicalL2 :=
  reflectedFourierL2.symm (seqToLp38 x hx)

@[simp] theorem fourierSeq38_physInv38 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) :
    fourierSeq38 (physInv38 x hx) = x := by
  funext n
  show (reflectedFourierL2 (reflectedFourierL2.symm (seqToLp38 x hx)) : ℤ → ℂ) n = x n
  rw [LinearIsometryEquiv.apply_symm_apply]; rfl

theorem fourierSeq38_injective : Function.Injective fourierSeq38 :=
  fun _ _ h => reflectedFourierL2.injective (lp.ext h)

theorem physInv38_fourierSeq38 (u : PhysicalL2) :
    physInv38 (fourierSeq38 u) (fourierSeq38_mem_zero u) = u :=
  fourierSeq38_injective (fourierSeq38_physInv38 _ _)

theorem norm_physInv38_sq (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) :
    ‖physInv38 x hx‖ ^ 2 = ∑' n : ℤ, ‖x n‖ ^ 2 := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (seqToLp38 x hx)
  have h2 : ‖physInv38 x hx‖ = ‖seqToLp38 x hx‖ := by
    unfold physInv38; exact LinearIsometryEquiv.norm_map _ _
  rw [h2]
  have h3 := h.tsum_eq
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h3
  exact h3.symm


theorem fourierSeq38_sub (u v : PhysicalL2) :
    fourierSeq38 (u - v) = fourierSeq38 u - fourierSeq38 v := by
  funext n
  show (reflectedFourierL2 (u - v) : ℤ → ℂ) n = (reflectedFourierL2 u : ℤ → ℂ) n -
    (reflectedFourierL2 v : ℤ → ℂ) n
  rw [map_sub]; rfl

theorem norm_sq_eq_tsum_fourierSeq38 (u : PhysicalL2) :
    ‖u‖ ^ 2 = ∑' n : ℤ, ‖fourierSeq38 u n‖ ^ 2 := by
  have h := norm_physInv38_sq (fourierSeq38 u) (fourierSeq38_mem_zero u)
  rwa [physInv38_fourierSeq38] at h

/-! ## Carrier infrastructure -/

theorem carrierExt38 {r : ℝ} {x y : SobolevCarrier38 r}
    (h : carrierCoe38 r x = carrierCoe38 r y) : x = y := by
  have : (show weightedSubmodule (sobolevModeWeight r) from x) =
      (show weightedSubmodule (sobolevModeWeight r) from y) := Subtype.ext h
  exact this

theorem carrierCoe38_injective (r : ℝ) : Function.Injective (carrierCoe38 r) :=
  fun _ _ h => carrierExt38 h

theorem sobolevModeWeight_pos (r : ℝ) (n : ℤ) : 0 < sobolevModeWeight r n :=
  Real.rpow_pos_of_pos (japaneseBracket_pos n) _

theorem sobolevModeWeight_mono {r s : ℝ} (h : r ≤ s) (n : ℤ) :
    sobolevModeWeight r n ≤ sobolevModeWeight s n :=
  Real.rpow_le_rpow_of_exponent_le (japaneseBracket_one_le n) (by linarith)

theorem sobolevModeWeight_natCast_zero (n : ℤ) : sobolevModeWeight ((0 : ℕ) : ℝ) n = 1 := by
  simp [sobolevModeWeight]

theorem carrier_hasSum_norm_sq38 (r : ℝ) (x : SobolevCarrier38 r) :
    HasSum (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2) (‖x‖ ^ 2) :=
  weightedHilbert_hasSum (sobolevModeWeight r) (show WeightedHilbert (sobolevModeWeight r) from x)

theorem carrier_hasSum_norm_sq_zero38 (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    HasSum (fun n : ℤ => ‖carrierCoe38 ((0 : ℕ) : ℝ) x n‖ ^ 2) (‖x‖ ^ 2) := by
  have h := carrier_hasSum_norm_sq38 ((0 : ℕ) : ℝ) x
  simpa only [sobolevModeWeight_natCast_zero, one_mul] using h

/-- The identity `SobolevHilbert r → SobolevCarrier38 r` as a continuous real-linear map. -/
def idToCarrier38 (r : ℝ) : SobolevHilbert r →L[ℝ] SobolevCarrier38 r where
  toFun x := toCarrier38 r x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_id

theorem sobolevModeWeight_mono_one {r s : ℝ} (h : r ≤ s) (n : ℤ) :
    sobolevModeWeight r n ≤ 1 * sobolevModeWeight s n := by
  rw [one_mul]; exact sobolevModeWeight_mono h n

/-! ## A1.3 derivative compatibility across carriers -/

/-- The inclusion `h^s → h^r`, `r ≤ s`, as a continuous real-linear map. -/
def carrierIncl38 {r s : ℝ} (h : r ≤ s) : SobolevCarrier38 s →L[ℝ] SobolevCarrier38 r :=
  liftCLM38 ((idToCarrier38 r).comp
    (weightedRealComparisonContinuous (sobolevModeWeight s) (sobolevModeWeight r) 1
      (by norm_num) (sobolevModeWeight_mono_one h)))

theorem carrierCoe38_incl38 {r s : ℝ} (h : r ≤ s) (x : SobolevCarrier38 s) :
    carrierCoe38 r (carrierIncl38 h x) = carrierCoe38 s x := by
  have e1 : carrierIncl38 h x = toCarrier38 r
      (weightedRealComparisonContinuous (sobolevModeWeight s) (sobolevModeWeight r) 1
        (by norm_num) (sobolevModeWeight_mono_one h) (ofCarrier38 s x)) := rfl
  rw [e1]
  exact funext (weightedRealComparison_apply (sobolevModeWeight s) (sobolevModeWeight r) 1
    (by norm_num) (sobolevModeWeight_mono_one h) (ofCarrier38 s x))

/-- Generic derivative compatibility: the `h^s`-derivative of a map defined by one sequence
map `f` is the restriction of its `h^r`-derivative. -/
theorem fderiv_compat38 {r s : ℝ} (h : r ≤ s) (f : (ℤ → ℂ) → (ℤ → ℂ))
    (hs : ∀ x ∈ seqSobolev38 s, f x ∈ seqSobolev38 s)
    (hr : ∀ x ∈ seqSobolev38 r, f x ∈ seqSobolev38 r) (x ξ : SobolevCarrier38 s)
    (hds : DifferentiableAt ℝ (carrierMap38 s s f hs) x)
    (hdr : DifferentiableAt ℝ (carrierMap38 r r f hr) (carrierIncl38 h x)) :
    carrierIncl38 h (fderiv ℝ (carrierMap38 s s f hs) x ξ) =
      fderiv ℝ (carrierMap38 r r f hr) (carrierIncl38 h x) (carrierIncl38 h ξ) := by
  have hcomm : (carrierMap38 r r f hr) ∘ (carrierIncl38 h) =
      (carrierIncl38 h) ∘ (carrierMap38 s s f hs) := funext fun y => carrierExt38 (by
      simp only [Function.comp_apply, carrierMap38_coe, carrierCoe38_incl38])
  have h1 : HasFDerivAt ((carrierMap38 r r f hr) ∘ (carrierIncl38 h))
      ((fderiv ℝ (carrierMap38 r r f hr) (carrierIncl38 h x)).comp (carrierIncl38 h)) x :=
    HasFDerivAt.comp x hdr.hasFDerivAt (carrierIncl38 h).hasFDerivAt
  have h2 : HasFDerivAt ((carrierIncl38 h) ∘ (carrierMap38 s s f hs))
      ((carrierIncl38 h).comp (fderiv ℝ (carrierMap38 s s f hs) x)) x :=
    HasFDerivAt.comp x (carrierIncl38 h).hasFDerivAt hds.hasFDerivAt
  rw [hcomm] at h1
  have := h1.unique h2
  exact (congrArg (fun L => L ξ) this).symm

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

theorem T_mem_zero {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 0) : B.T x ∈ seqSobolev38 0 :=
  (mem_seqSobolev38_natCast_zero_iff _).1
    (B.mapsTo_T 0 x ((mem_seqSobolev38_natCast_zero_iff x).2 hx))

theorem Tinv_mem_zero {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 0) : B.Tinv x ∈ seqSobolev38 0 :=
  (mem_seqSobolev38_natCast_zero_iff _).1
    (B.mapsTo_Tinv 0 x ((mem_seqSobolev38_natCast_zero_iff x).2 hx))

theorem Φ_mem_zero (u : PhysicalL2) : B.Φ u ∈ seqSobolev38 0 :=
  B.T_mem_zero (fourierSeq38_mem_zero u)

/-- `Φ⁻¹ = 𝓕⁻¹ ∘ T⁻¹` on `h⁰`, with values in the physical `L²`. -/
def Φinv (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) : PhysicalL2 :=
  physInv38 (B.Tinv z) (B.Tinv_mem_zero hz)

theorem fourierSeq38_Φinv (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) :
    fourierSeq38 (B.Φinv z hz) = B.Tinv z :=
  fourierSeq38_physInv38 _ _

theorem Φ_Φinv (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) : B.Φ (B.Φinv z hz) = z := by
  rw [Φ_def, fourierSeq38_Φinv]
  exact B.right_inv z hz

theorem Φinv_Φ (u : PhysicalL2) : B.Φinv (B.Φ u) (B.Φ_mem_zero u) = u := by
  apply fourierSeq38_injective
  rw [fourierSeq38_Φinv, Φ_def]
  exact B.left_inv _ (fourierSeq38_mem_zero u)

theorem Φ_injective : Function.Injective B.Φ := by
  intro u v h
  apply fourierSeq38_injective
  have hu := B.left_inv _ (fourierSeq38_mem_zero u)
  have hv := B.left_inv _ (fourierSeq38_mem_zero v)
  rw [← hu, ← hv]
  exact congrArg B.Tinv h

theorem Φ_mem_seqSobolev38 (m : ℕ) (u : PhysicalL2)
    (hu : SobolevSquareSummable (m : ℝ) (physicalFourier u)) : B.Φ u ∈ seqSobolev38 (m : ℝ) :=
  B.mapsTo_T m _ ((fourierSeq38_mem_iff _ u).2 hu)

theorem sobolev_Φinv (m : ℕ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 (m : ℝ)) :
    SobolevSquareSummable (m : ℝ)
      (physicalFourier (B.Φinv z (seqSobolev38_natCast_mono hz))) :=
  (fourierSeq38_mem_iff _ _).1 (by rw [fourierSeq38_Φinv]; exact B.mapsTo_Tinv m z hz)

theorem TinvC_TC (m : ℕ) (x : SobolevCarrier38 (m : ℝ)) : B.TinvC m (B.TC m x) = x := by
  apply carrierExt38
  rw [TinvC_coe, TC_coe]
  exact B.left_inv _ (seqSobolev38_natCast_mono (carrierCoe38_mem _ x))

theorem TC_TinvC (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) : B.TC m (B.TinvC m z) = z := by
  apply carrierExt38
  rw [TC_coe, TinvC_coe]
  exact B.right_inv _ (seqSobolev38_natCast_mono (carrierCoe38_mem _ z))

/-! ### A1.5 `T` is a homeomorphism of each carrier -/

/-- `T : h^m ≃ₜ h^m`. -/
def homeoC (m : ℕ) : SobolevCarrier38 (m : ℝ) ≃ₜ SobolevCarrier38 (m : ℝ) where
  toFun := B.TC m
  invFun := B.TinvC m
  left_inv := B.TinvC_TC m
  right_inv := B.TC_TinvC m
  continuous_toFun := B.continuous_TC m
  continuous_invFun := B.continuous_TinvC m

@[simp] theorem homeoC_apply (m : ℕ) (x : SobolevCarrier38 (m : ℝ)) : B.homeoC m x = B.TC m x := rfl

@[simp] theorem homeoC_symm_apply (m : ℕ) (x : SobolevCarrier38 (m : ℝ)) :
    (B.homeoC m).symm x = B.TinvC m x := rfl

end BirkhoffTop38

namespace BirkhoffAnalytic38

variable {B : BirkhoffTop38} {M : Set ℕ} (hA : BirkhoffAnalytic38 B M)

include hA

/-! ### A1.3 for `T` and `T⁻¹` (needs analyticity, hence differentiability, at both levels) -/

theorem fderiv_TC_compat (k m : ℕ) (hk : k ∈ M) (hm : m ∈ M) (hkm : k ≤ m)
    (x ξ : SobolevCarrier38 (m : ℝ)) :
    carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) (fderiv ℝ (B.TC m) x ξ) =
      fderiv ℝ (B.TC k) (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) x)
        (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) ξ) :=
  fderiv_compat38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) B.T (B.mapsTo_T m) (B.mapsTo_T k) x ξ
    ((hA.analyticOnNhd_TC hm x trivial).differentiableAt)
    ((hA.analyticOnNhd_TC hk _ trivial).differentiableAt)

theorem fderiv_TinvC_compat (k m : ℕ) (hk : k ∈ M) (hm : m ∈ M) (hkm : k ≤ m)
    (x ξ : SobolevCarrier38 (m : ℝ)) :
    carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) (fderiv ℝ (B.TinvC m) x ξ) =
      fderiv ℝ (B.TinvC k) (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) x)
        (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) ξ) :=
  fderiv_compat38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) B.Tinv (B.mapsTo_Tinv m) (B.mapsTo_Tinv k) x ξ
    ((hA.analyticOnNhd_TinvC hm x trivial).differentiableAt)
    ((hA.analyticOnNhd_TinvC hk _ trivial).differentiableAt)

/-- Sequence-level form: the `h^m` derivative of `T` is the restriction of the `h^k` one. -/
theorem fderiv_TC_compat_coe (k m : ℕ) (hk : k ∈ M) (hm : m ∈ M) (hkm : k ≤ m)
    (x ξ : SobolevCarrier38 (m : ℝ)) :
    carrierCoe38 (k : ℝ) (fderiv ℝ (B.TC k) (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) x)
        (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) ξ)) =
      carrierCoe38 (m : ℝ) (fderiv ℝ (B.TC m) x ξ) := by
  rw [← hA.fderiv_TC_compat k m hk hm hkm, carrierCoe38_incl38]

theorem fderiv_TinvC_compat_coe (k m : ℕ) (hk : k ∈ M) (hm : m ∈ M) (hkm : k ≤ m)
    (x ξ : SobolevCarrier38 (m : ℝ)) :
    carrierCoe38 (k : ℝ) (fderiv ℝ (B.TinvC k) (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) x)
        (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) ξ)) =
      carrierCoe38 (m : ℝ) (fderiv ℝ (B.TinvC m) x ξ) := by
  rw [← hA.fderiv_TinvC_compat k m hk hm hkm, carrierCoe38_incl38]

end BirkhoffAnalytic38

namespace BirkhoffInput38

variable (B : BirkhoffInput38)

/-! Full-input forms (all levels), for the consumers that keep `B : BirkhoffInput38`. -/

theorem fderiv_TC_compat (k m : ℕ) (hkm : k ≤ m) (x ξ : SobolevCarrier38 (m : ℝ)) :
    carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) (fderiv ℝ (B.TC m) x ξ) =
      fderiv ℝ (B.TC k) (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) x)
        (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) ξ) :=
  B.toAnalytic.fderiv_TC_compat k m trivial trivial hkm x ξ

theorem fderiv_TinvC_compat (k m : ℕ) (hkm : k ≤ m) (x ξ : SobolevCarrier38 (m : ℝ)) :
    carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) (fderiv ℝ (B.TinvC m) x ξ) =
      fderiv ℝ (B.TinvC k) (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) x)
        (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) ξ) :=
  B.toAnalytic.fderiv_TinvC_compat k m trivial trivial hkm x ξ

theorem fderiv_TC_compat_coe (k m : ℕ) (hkm : k ≤ m) (x ξ : SobolevCarrier38 (m : ℝ)) :
    carrierCoe38 (k : ℝ) (fderiv ℝ (B.TC k) (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) x)
        (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) ξ)) =
      carrierCoe38 (m : ℝ) (fderiv ℝ (B.TC m) x ξ) :=
  B.toAnalytic.fderiv_TC_compat_coe k m trivial trivial hkm x ξ

theorem fderiv_TinvC_compat_coe (k m : ℕ) (hkm : k ≤ m) (x ξ : SobolevCarrier38 (m : ℝ)) :
    carrierCoe38 (k : ℝ) (fderiv ℝ (B.TinvC k) (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) x)
        (carrierIncl38 (Nat.cast_le.2 hkm : (k : ℝ) ≤ m) ξ)) =
      carrierCoe38 (m : ℝ) (fderiv ℝ (B.TinvC m) x ξ) :=
  B.toAnalytic.fderiv_TinvC_compat_coe k m trivial trivial hkm x ξ

end BirkhoffInput38


/-! ## A1.4 Cleaned inverse and measurability (from continuity on the carrier) -/

theorem norm_coe_mul_sqrt_le38 (r : ℝ) (x : SobolevCarrier38 r) (n : ℤ) :
    ‖carrierCoe38 r x n‖ * Real.sqrt (sobolevModeWeight r n) ≤ ‖x‖ := by
  have hw := sobolevModeWeight_pos r n
  have h1 : sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    le_hasSum (carrier_hasSum_norm_sq38 r x) n
      (fun j _ => mul_nonneg (sobolevModeWeight_pos r j).le (sq_nonneg _))
  refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 ?_
  rw [mul_pow, Real.sq_sqrt hw.le]
  linarith

theorem continuous_carrierCoe_apply38 (r : ℝ) (n : ℤ) :
    Continuous (fun x : SobolevCarrier38 r => carrierCoe38 r x n) := by
  have hw := sobolevModeWeight_pos r n
  have hs : 0 < Real.sqrt (sobolevModeWeight r n) := Real.sqrt_pos.2 hw
  refine (LipschitzWith.of_dist_le_mul
    (K := ⟨(Real.sqrt (sobolevModeWeight r n))⁻¹, by positivity⟩) (fun x y => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have h := norm_coe_mul_sqrt_le38 r (x - y) n
  have e : carrierCoe38 r (x - y) n = carrierCoe38 r x n - carrierCoe38 r y n := rfl
  rw [e] at h
  show ‖carrierCoe38 r x n - carrierCoe38 r y n‖ ≤ (Real.sqrt (sobolevModeWeight r n))⁻¹ * ‖x - y‖
  rw [inv_mul_eq_div, le_div_iff₀ hs]
  exact h

theorem continuous_carrierCoe38 (r : ℝ) : Continuous (carrierCoe38 r) :=
  continuous_pi (continuous_carrierCoe_apply38 r)

theorem polishSpace_carrier38 (r : ℝ) : PolishSpace (SobolevCarrier38 r) := by
  haveI : TopologicalSpace.SeparableSpace (SobolevCarrier38 r) :=
    inferInstanceAs (TopologicalSpace.SeparableSpace (SobolevHilbert r))
  haveI : CompleteSpace (SobolevCarrier38 r) :=
    inferInstanceAs (CompleteSpace (SobolevHilbert r))
  haveI : SecondCountableTopology (SobolevCarrier38 r) :=
    UniformSpace.secondCountable_of_separable (SobolevCarrier38 r)
  infer_instance

theorem measurableEmbedding_carrierCoe38 (r : ℝ) [MeasurableSpace (SobolevCarrier38 r)]
    [BorelSpace (SobolevCarrier38 r)] : MeasurableEmbedding (carrierCoe38 r) := by
  haveI := polishSpace_carrier38 r
  exact (continuous_carrierCoe38 r).measurableEmbedding (carrierCoe38_injective r)

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- Cleaned inverse into the carrier `h^m`: `z ↦ T⁻¹ z` on `h^m`, and `0` off `h^m`. -/
def cleanTinvC (m : ℕ) (z : ℤ → ℂ) : SobolevCarrier38 (m : ℝ) :=
  Function.extend (carrierCoe38 (m : ℝ)) (B.TinvC m) (fun _ => 0) z

theorem cleanTinvC_of_mem (m : ℕ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 (m : ℝ)) :
    B.cleanTinvC m z = B.TinvC m (carrierMk38 (m : ℝ) z hz) :=
  (carrierCoe38_injective (m : ℝ)).extend_apply (B.TinvC m) (fun _ => 0)
    (carrierMk38 (m : ℝ) z hz)

theorem cleanTinvC_of_not_mem (m : ℕ) (z : ℤ → ℂ) (hz : z ∉ seqSobolev38 (m : ℝ)) :
    B.cleanTinvC m z = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨a, rfl⟩
  exact hz (carrierCoe38_mem _ a)

theorem measurable_cleanTinvC (m : ℕ) [MeasurableSpace (SobolevCarrier38 (m : ℝ))]
    [BorelSpace (SobolevCarrier38 (m : ℝ))] : Measurable (B.cleanTinvC m) :=
  (measurableEmbedding_carrierCoe38 (m : ℝ)).measurable_extend
    (B.continuous_TinvC m).measurable measurable_const

/-- Cleaned inverse on sequences: `T⁻¹` on `h⁰`, `0` elsewhere. -/
def cleanTinv (z : ℤ → ℂ) : ℤ → ℂ := by
  classical exact if z ∈ seqSobolev38 0 then B.Tinv z else 0

theorem cleanTinv_of_mem (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) : B.cleanTinv z = B.Tinv z := by
  unfold cleanTinv; rw [if_pos hz]

theorem cleanTinv_of_not_mem (z : ℤ → ℂ) (hz : z ∉ seqSobolev38 0) : B.cleanTinv z = 0 := by
  unfold cleanTinv; rw [if_neg hz]

theorem cleanTinv_eq_coe (z : ℤ → ℂ) :
    B.cleanTinv z = carrierCoe38 ((0 : ℕ) : ℝ) (B.cleanTinvC 0 z) := by
  by_cases hz : z ∈ seqSobolev38 0
  · have hz' : z ∈ seqSobolev38 ((0 : ℕ) : ℝ) := (mem_seqSobolev38_natCast_zero_iff z).2 hz
    rw [B.cleanTinv_of_mem z hz, B.cleanTinvC_of_mem 0 z hz']
    rfl
  · have hz' : z ∉ seqSobolev38 ((0 : ℕ) : ℝ) := fun h => hz ((mem_seqSobolev38_natCast_zero_iff z).1 h)
    rw [B.cleanTinv_of_not_mem z hz, B.cleanTinvC_of_not_mem 0 z hz']
    rfl

/-- Measurability of the cleaned inverse `ℤ → ℂ → ℤ → ℂ` for the product σ-algebras. -/
theorem measurable_cleanTinv : Measurable B.cleanTinv := by
  letI : MeasurableSpace (SobolevCarrier38 ((0 : ℕ) : ℝ)) := borel _
  haveI : BorelSpace (SobolevCarrier38 ((0 : ℕ) : ℝ)) := ⟨rfl⟩
  have : B.cleanTinv = fun z => carrierCoe38 ((0 : ℕ) : ℝ) (B.cleanTinvC 0 z) :=
    funext B.cleanTinv_eq_coe
  rw [this]
  exact (continuous_carrierCoe38 _).measurable.comp (B.measurable_cleanTinvC 0)

end BirkhoffTop38

/-- `h⁰ → L²`, `x ↦ 𝓕⁻¹ x`, on the carrier at `((0:ℕ):ℝ)`. -/
def carrierToPhys38 (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) : PhysicalL2 :=
  physInv38 (carrierCoe38 ((0 : ℕ) : ℝ) x) (carrierCoe38_mem_zero x)

theorem norm_carrierToPhys38_sub (x y : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    ‖carrierToPhys38 x - carrierToPhys38 y‖ = ‖x - y‖ := by
  have h1 := norm_sq_eq_tsum_fourierSeq38 (carrierToPhys38 x - carrierToPhys38 y)
  have h2 := (carrier_hasSum_norm_sq_zero38 (x - y)).tsum_eq
  have e : ∀ n, fourierSeq38 (carrierToPhys38 x - carrierToPhys38 y) n =
      carrierCoe38 ((0 : ℕ) : ℝ) (x - y) n := by
    intro n
    rw [fourierSeq38_sub]
    show fourierSeq38 (physInv38 _ _) n - fourierSeq38 (physInv38 _ _) n = _
    rw [fourierSeq38_physInv38, fourierSeq38_physInv38]
    rfl
  simp only [e] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.trans h2)

theorem fourierSeq38_zero : fourierSeq38 (0 : PhysicalL2) = 0 := by
  funext n
  show (reflectedFourierL2 (0 : PhysicalL2) : ℤ → ℂ) n = 0
  rw [map_zero]; rfl

theorem carrierToPhys38_zero : carrierToPhys38 0 = 0 := by
  apply fourierSeq38_injective
  unfold carrierToPhys38
  rw [fourierSeq38_physInv38, fourierSeq38_zero]
  rfl

theorem continuous_carrierToPhys38 : Continuous carrierToPhys38 := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm, norm_carrierToPhys38_sub]
  simp

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- Cleaned `Φ⁻¹` on sequences: `Φinv` on `h⁰`, `0` elsewhere. -/
def cleanΦinv (z : ℤ → ℂ) : PhysicalL2 := by
  classical exact if hz : z ∈ seqSobolev38 0 then B.Φinv z hz else 0

theorem cleanΦinv_of_mem (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) :
    B.cleanΦinv z = B.Φinv z hz := by
  unfold cleanΦinv; rw [dif_pos hz]

theorem cleanΦinv_eq (z : ℤ → ℂ) : B.cleanΦinv z = carrierToPhys38 (B.cleanTinvC 0 z) := by
  by_cases hz : z ∈ seqSobolev38 0
  · have hz' : z ∈ seqSobolev38 ((0 : ℕ) : ℝ) := (mem_seqSobolev38_natCast_zero_iff z).2 hz
    rw [B.cleanΦinv_of_mem z hz, B.cleanTinvC_of_mem 0 z hz']
    rfl
  · have hz' : z ∉ seqSobolev38 ((0 : ℕ) : ℝ) := fun h => hz ((mem_seqSobolev38_natCast_zero_iff z).1 h)
    rw [B.cleanTinvC_of_not_mem 0 z hz']
    unfold cleanΦinv; rw [dif_neg hz]
    exact carrierToPhys38_zero.symm

/-- Measurability of the cleaned physical inverse `Φ⁻¹ : (ℤ → ℂ) → L²`. -/
theorem measurable_cleanΦinv [MeasurableSpace PhysicalL2] [BorelSpace PhysicalL2] :
    Measurable B.cleanΦinv := by
  letI : MeasurableSpace (SobolevCarrier38 ((0 : ℕ) : ℝ)) := borel _
  haveI : BorelSpace (SobolevCarrier38 ((0 : ℕ) : ℝ)) := ⟨rfl⟩
  have : B.cleanΦinv = fun z => carrierToPhys38 (B.cleanTinvC 0 z) := funext B.cleanΦinv_eq
  rw [this]
  exact continuous_carrierToPhys38.measurable.comp (B.measurable_cleanTinvC 0)

end BirkhoffTop38

/-! ## A1.6 Finite support, finitely many open gaps (Φ-free gap facts first) -/

theorem actualGapLower_le_upper38 (u : PhysicalL2) (n : ℤ) :
    actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
  obtain ⟨⟨y, hy⟩, hset⟩ := actualGapLevelSet_eq_Icc_E02_38 u n
  rw [hset] at hy
  exact hy.1.trans hy.2

/-- Φ-free positivity of the gap height inside an open gap (from the semicircle lower bound). -/
theorem actualGapHeight_pos_of_mem_Ioo38 (u : PhysicalL2) (n : ℤ) (x : ℝ)
    (hx : x ∈ Set.Ioo (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) :
    0 < actualGapHeightE02_38 u x :=
  lt_of_lt_of_le
    (by
      unfold gapSemicircle
      exact Real.sqrt_pos.2 (mul_pos (sub_pos.2 hx.1) (sub_pos.2 hx.2)))
    (actualGapHeight_ge_semicircle_all_E02_38 u n x ⟨hx.1.le, hx.2.le⟩)

/-- Φ-free: a zero gap action forces a closed gap. -/
theorem actualGap_closed_of_action_eq_zero38 (u : PhysicalL2) (n : ℤ)
    (h : actualGapActionAllE02_38 u n = 0) :
    actualGapUpperAllE02_38 u n = actualGapLowerAllE02_38 u n := by
  have h1 := actualGapAction_ge_sq_div_four_all_E02_38 u n
  have h2 := actualGapLower_le_upper38 u n
  rw [h] at h1
  have h3 : (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  have := pow_eq_zero_iff (two_ne_zero) |>.1 h3
  linarith

/-- Φ-free: an open gap has strictly positive action. -/
theorem actualGapAction_pos_of_open38 (u : PhysicalL2) (n : ℤ)
    (h : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n) :
    0 < actualGapActionAllE02_38 u n := by
  by_contra hn
  have h0 : actualGapActionAllE02_38 u n = 0 := by
    have := actualGapAction_ge_sq_div_four_all_E02_38 u n
    have : 0 ≤ actualGapActionAllE02_38 u n :=
      le_trans (by positivity) this
    linarith
  have := actualGap_closed_of_action_eq_zero38 u n h0
  linarith

theorem finiteSupport_mem_seqSobolev38 (r : ℝ) (z : ℤ → ℂ) (hz : {n : ℤ | z n ≠ 0}.Finite) :
    z ∈ seqSobolev38 r := by
  rw [mem_seqSobolev38_iff]
  refine summable_of_finite_support (hz.subset fun n hn => ?_)
  by_contra h
  simp only [Set.mem_setOf_eq, not_not] at h
  apply hn
  simp [h]

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- Open gaps of an `H¹` field lie in the support of its Birkhoff coordinates. -/
theorem openGaps_subset_support (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n} ⊆
      {n : ℤ | B.Φ u n ≠ 0} := by
  intro n hn hzero
  have h1 := B.sq_norm_Φ_eq_action u hu n
  rw [hzero, norm_zero] at h1
  have h2 := actualGapAction_pos_of_open38 u n hn
  rw [← h1] at h2
  norm_num at h2

theorem finite_openGaps_of_finite_support (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ | B.Φ u n ≠ 0}.Finite) :
    {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite :=
  hfin.subset (B.openGaps_subset_support u hu)

/-- Finitely supported Birkhoff data give a field in every `H^m` with finitely many open gaps
(the `hfin` hypothesis of `actualConvexMoment_E02_38`). -/
theorem finiteSupport_regular_finiteGaps (z : ℤ → ℂ) (hz : {n : ℤ | z n ≠ 0}.Finite) :
    (∀ m : ℕ, B.Tinv z ∈ seqSobolev38 (m : ℝ)) ∧
    (∀ m : ℕ, SobolevSquareSummable (m : ℝ)
      (physicalFourier (B.Φinv z (finiteSupport_mem_seqSobolev38 0 z hz)))) ∧
    B.Φ (B.Φinv z (finiteSupport_mem_seqSobolev38 0 z hz)) = z ∧
    {n : ℤ | actualGapLowerAllE02_38 (B.Φinv z (finiteSupport_mem_seqSobolev38 0 z hz)) n <
      actualGapUpperAllE02_38 (B.Φinv z (finiteSupport_mem_seqSobolev38 0 z hz)) n}.Finite := by
  have hm : ∀ m : ℕ, z ∈ seqSobolev38 (m : ℝ) := fun m => finiteSupport_mem_seqSobolev38 _ z hz
  have hΦ := B.Φ_Φinv z (finiteSupport_mem_seqSobolev38 0 z hz)
  refine ⟨fun m => B.mapsTo_Tinv m z (hm m), fun m => B.sobolev_Φinv m z (hm m), hΦ, ?_⟩
  refine B.finite_openGaps_of_finite_support _ ?_ ?_
  · simpa using B.sobolev_Φinv 1 z (hm 1)
  · rw [hΦ]; exact hz

/-! ## A1.7 `Σ I_n = ‖u‖²` -/

/-- `Σ_n |Φ_n(u)|² = ‖u‖²` for `u ∈ H¹`; the Φ-free sum is `actualGapAction_hasSum_E02_38`. -/
theorem hasSum_normSq_Φ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    HasSum (fun n : ℤ => ‖B.Φ u n‖ ^ 2) (‖u‖ ^ 2) := by
  have e : (fun n : ℤ => ‖B.Φ u n‖ ^ 2) = fun n => actualGapActionAllE02_38 u n :=
    funext (B.sq_norm_Φ_eq_action u hu)
  rw [e]
  exact actualGapAction_hasSum_E02_38 u hu

theorem tsum_normSq_Φ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∑' n : ℤ, ‖B.Φ u n‖ ^ 2 = ‖u‖ ^ 2 :=
  (B.hasSum_normSq_Φ u hu).tsum_eq

/-- `Φ u` has `h⁰` norm `‖u‖` for `u ∈ H¹`. -/
theorem norm_carrier_Φ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖carrierZero38 (B.Φ u) (B.Φ_mem_zero u)‖ = ‖u‖ := by
  have h := (carrier_hasSum_norm_sq_zero38 (carrierZero38 (B.Φ u) (B.Φ_mem_zero u)))
  have h2 := B.hasSum_normSq_Φ u hu
  have := h.unique h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

end BirkhoffTop38

end NlsGge.Birkhoff
end
