import NlsGge.Birkhoff.S01Equivariance38c
import NlsGge.Composition.Main
import NlsGge.Weights.Size

/-! # W04 (`D:thm:weighted`), part 1: the orbit weight and the spaces `E_s`

Source: `paper/v2.tex` l.1482-1498.  This file contains the Birkhoff-free preparation:

* W04.01: `E_s = {x : ∑ a_n ⟨n⟩^{-2s} |x_n|² < ∞}` as the sequence set `seqE38 c s`
  (= membership in `weightedSubmodule (fullModeWeight c s)`) with its coherent real Hilbert carrier
  `ECarrier38 c s`; embedding `E_s ⊆ h^r` for every `r`;
* W04.03: the orbit weight `w_n = √a_n ⟨n⟩^{-s-1}` is two-sided comparable to the W03 source weight
  `exp(2√(2π)√|n|) ⟨n⟩^{-s-1-3/8}` (via W02), hence is an `AdmissibleWeight` for W03.

Nothing in this file mentions `BirkhoffInput38`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Composition
open scoped Real

/-! ## W04.01: the spaces `E_s` -/

section Spaces

variable {lower upper : ℝ}

/-- `E_s` (v2 `D:eq:Es`) as a set of complex sequences: `∑ a_n ⟨n⟩^{-2s} |x_n|² < ∞`, written as
membership in the weighted submodule for the actual weight `fullModeWeight c s n = a_n ⟨n⟩^{-2s}`. -/
def seqE38 (c : BoundedCoefficients lower upper) (s : ℝ) : Set (ℤ → ℂ) :=
  {x | x ∈ weightedSubmodule (fullModeWeight c s)}

/-- The coherent real Hilbert carrier of `E_s`: the same type as `FullWeightedHilbert c s`
(by `rfl`), with only the normed-group and the accepted real inner-product instances (the same
device as `SobolevCarrier38`). -/
def ECarrier38 (c : BoundedCoefficients lower upper) (s : ℝ) : Type := FullWeightedHilbert c s

instance eCarrierNormedAddCommGroup38 (c : BoundedCoefficients lower upper) (s : ℝ) :
    NormedAddCommGroup (ECarrier38 c s) :=
  inferInstanceAs (NormedAddCommGroup (FullWeightedHilbert c s))

instance eCarrierInnerProductSpace38 (c : BoundedCoefficients lower upper) (s : ℝ) :
    InnerProductSpace ℝ (ECarrier38 c s) :=
  weightedRealBasisInnerProductSpace (fullModeWeight c s)

instance eCarrierCompleteSpace38 (c : BoundedCoefficients lower upper) (s : ℝ) :
    CompleteSpace (ECarrier38 c s) :=
  inferInstanceAs (CompleteSpace (FullWeightedHilbert c s))

/-- Underlying sequence of an element of `ECarrier38`. -/
def eCoe38 (c : BoundedCoefficients lower upper) (s : ℝ) (x : ECarrier38 c s) : ℤ → ℂ :=
  ((show weightedSubmodule (fullModeWeight c s) from x) : ℤ → ℂ)

theorem eCoe38_mem (c : BoundedCoefficients lower upper) (s : ℝ) (x : ECarrier38 c s) :
    eCoe38 c s x ∈ seqE38 c s :=
  (show weightedSubmodule (fullModeWeight c s) from x).2

/-- A sequence of `E_s` as an element of the carrier. -/
def eMk38 (c : BoundedCoefficients lower upper) (s : ℝ) (x : ℤ → ℂ) (hx : x ∈ seqE38 c s) :
    ECarrier38 c s :=
  (show ECarrier38 c s from (⟨x, hx⟩ : weightedSubmodule (fullModeWeight c s)))

@[simp] theorem eCoe38_mk (c : BoundedCoefficients lower upper) (s : ℝ) (x : ℤ → ℂ)
    (hx : x ∈ seqE38 c s) : eCoe38 c s (eMk38 c s x hx) = x := rfl

theorem eExt38 (c : BoundedCoefficients lower upper) (s : ℝ) {x y : ECarrier38 c s}
    (h : eCoe38 c s x = eCoe38 c s y) : x = y := by
  have : (show weightedSubmodule (fullModeWeight c s) from x) =
      (show weightedSubmodule (fullModeWeight c s) from y) := Subtype.ext h
  exact this

/-- The map `E_s → E_{s'}` induced by a sequence map sending `E_s` into `E_{s'}`. -/
def eMap38 (c : BoundedCoefficients lower upper) (s s' : ℝ) (f : (ℤ → ℂ) → (ℤ → ℂ))
    (hf : ∀ x ∈ seqE38 c s, f x ∈ seqE38 c s') : ECarrier38 c s → ECarrier38 c s' :=
  fun x => eMk38 c s' (f (eCoe38 c s x)) (hf _ (eCoe38_mem c s x))

@[simp] theorem eCoe38_eMap38 (c : BoundedCoefficients lower upper) (s s' : ℝ)
    (f : (ℤ → ℂ) → (ℤ → ℂ)) (hf : ∀ x ∈ seqE38 c s, f x ∈ seqE38 c s') (x : ECarrier38 c s) :
    eCoe38 c s' (eMap38 c s s' f hf x) = f (eCoe38 c s x) := rfl

/-- Squared norm of `E_s`: `‖x‖² = ∑ a_n ⟨n⟩^{-2s} |x_n|²`. -/
theorem norm_sq_eCarrier38 (c : BoundedCoefficients lower upper) (s : ℝ) (x : ECarrier38 c s) :
    ‖x‖ ^ 2 = ∑' n : ℤ, fullModeWeight c s n * ‖eCoe38 c s x n‖ ^ 2 :=
  weightedHilbert_norm_sq (fullModeWeight c s) x

/-- Membership in `E_s` as the summability `∑ a_n ⟨n⟩^{-2s} |x_n|² < ∞`. -/
theorem mem_seqE38_iff (c : BoundedCoefficients lower upper) (s : ℝ) (x : ℤ → ℂ) :
    x ∈ seqE38 c s ↔ Summable fun n : ℤ => fullModeWeight c s n * ‖x n‖ ^ 2 := by
  change x ∈ weightedSubmodule (fullModeWeight c s) ↔ _
  change Memℓp (weightedCoordinates (fullModeWeight c s) x) 2 ↔ _
  rw [weightedCoordinates_mem_l2_iff (fullModeWeight c s) (fun n => (fullModeWeight_pos c s n).le)]

/-- **W04.01.** `E_s ⊆ h^r` for every real `r` (v2: "each `E_s` is continuously embedded in every
ordinary Sobolev sequence space"; the continuity is `fullWeightedToSobolev_norm_le`). -/
theorem seqE38_subset_seqSobolev38 (c : BoundedCoefficients lower upper) (s r : ℝ) {x : ℤ → ℂ}
    (hx : x ∈ seqE38 c s) : x ∈ seqSobolev38 r := by
  have h1 : WeightedSquareSummable (sourceRate c) s x :=
    (fullWeightedHilbert_membership_iff c s x).1 hx
  exact (mem_seqSobolev38_iff r x).2 (sourceWeightedSquareSummable_sobolev c s r x h1)

end Spaces

/-! ## W04.03: the orbit weight and its comparison with the W03 weight -/

section Weights

variable {lower upper : ℝ}

/-- v2's orbit weight `w_n = √a_n ⟨n⟩^{-s-1}` (`a_n = sourceRate c n = W(2πn)`). -/
def orbitWeight38 (c : BoundedCoefficients lower upper) (s : ℝ) (n : ℤ) : ℝ :=
  Real.sqrt (sourceRate c n) * Real.rpow (japaneseBracket n) (-s - 1)

theorem japaneseBracket_eq_jbr (n : ℤ) : japaneseBracket n = jbr (n : ℝ) := rfl

theorem japaneseBracket_neg (n : ℤ) : japaneseBracket (-n) = japaneseBracket n := by
  unfold japaneseBracket; simp

theorem sourceRate_neg (c : BoundedCoefficients lower upper) (n : ℤ) :
    sourceRate c (-n) = sourceRate c n := by
  unfold sourceRate
  have : 2 * π * ((-n : ℤ) : ℝ) = -(2 * π * (n : ℝ)) := by push_cast; ring
  rw [this, NlsGge.Weights.weight_even]

theorem orbitWeight38_pos (c : BoundedCoefficients lower upper) (s : ℝ) (n : ℤ) :
    0 < orbitWeight38 c s n :=
  mul_pos (Real.sqrt_pos.2 (sourceRate_pos c n))
    (Real.rpow_pos_of_pos (japaneseBracket_pos n) _)

theorem orbitWeight38_neg (c : BoundedCoefficients lower upper) (s : ℝ) (n : ℤ) :
    orbitWeight38 c s (-n) = orbitWeight38 c s n := by
  unfold orbitWeight38; rw [sourceRate_neg, japaneseBracket_neg]

/-- `w_n² ⟨n⟩^{2r} = a_n ⟨n⟩^{-2(s+1-r)}`: the weighted `h^r` norm of the orbit is the `E_{s+1-r}`
norm of the sequence. -/
theorem orbitWeight38_sq_mul (c : BoundedCoefficients lower upper) (s r : ℝ) (n : ℤ) :
    orbitWeight38 c s n ^ 2 * sobolevModeWeight r n = fullModeWeight c (s + 1 - r) n := by
  have hj := japaneseBracket_pos n
  unfold orbitWeight38 sobolevModeWeight fullModeWeight
  rw [mul_pow, Real.sq_sqrt (sourceRate_pos c n).le]
  have h1 : Real.rpow (japaneseBracket n) (-s - 1) ^ 2 =
      Real.rpow (japaneseBracket n) (2 * (-s - 1)) := by
    change (japaneseBracket n ^ (-s - 1)) ^ 2 = japaneseBracket n ^ (2 * (-s - 1))
    rw [← Real.rpow_natCast, ← Real.rpow_mul hj.le]; norm_num; ring_nf
  rw [h1, mul_assoc]
  congr 1
  change japaneseBracket n ^ (2 * (-s - 1)) * japaneseBracket n ^ (2 * r) =
    japaneseBracket n ^ (-2 * (s + 1 - r))
  rw [← Real.rpow_add hj]; congr 1; ring

/-- Elementary: `⟨n⟩ ≤ 1 + 2π|n| ≤ 2π√2 ⟨n⟩`. -/
theorem japaneseBracket_le_one_add (n : ℤ) : japaneseBracket n ≤ 1 + 2 * π * |(n : ℝ)| := by
  unfold japaneseBracket
  have h1 : 1 + (n : ℝ) ^ 2 ≤ (1 + 2 * π * |(n : ℝ)|) ^ 2 := by
    have := Real.pi_gt_three
    have ha := abs_nonneg (n : ℝ)
    have e : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
    have hp2 : 1 ≤ 4 * π ^ 2 := by nlinarith
    rw [e]; nlinarith [mul_le_mul_of_nonneg_right hp2 (sq_nonneg |(n : ℝ)|),
      mul_nonneg ha (by linarith : (0 : ℝ) ≤ π)]
  calc Real.sqrt (1 + (n : ℝ) ^ 2) ≤ Real.sqrt ((1 + 2 * π * |(n : ℝ)|) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = 1 + 2 * π * |(n : ℝ)| := Real.sqrt_sq (by positivity)

theorem one_add_le_japaneseBracket (n : ℤ) :
    1 + 2 * π * |(n : ℝ)| ≤ 2 * π * Real.sqrt 2 * japaneseBracket n := by
  unfold japaneseBracket
  have hpi := Real.pi_gt_three
  have ha := abs_nonneg (n : ℝ)
  have e : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
  have h1 : (1 + 2 * π * |(n : ℝ)|) ^ 2 ≤ (2 * π * Real.sqrt 2) ^ 2 * (1 + (n : ℝ) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), e]
    have : (1 : ℝ) ≤ π := by linarith
    nlinarith [sq_nonneg (1 - 2 * π * |(n : ℝ)|), mul_nonneg ha (sub_nonneg.2 this),
      sq_nonneg (π * |(n : ℝ)| - 1), sq_nonneg |(n : ℝ)|, sq_nonneg π,
      mul_nonneg (sq_nonneg π) (sq_nonneg |(n : ℝ)|)]
  have h2 : 1 + 2 * π * |(n : ℝ)| ≤ Real.sqrt ((2 * π * Real.sqrt 2) ^ 2 * (1 + (n : ℝ) ^ 2)) :=
    Real.le_sqrt_of_sq_le h1
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at h2

/-- **W04.03 (comparison).** The orbit weight is two-sided comparable to the W03 source weight
`exp(a√|n|) ⟨n⟩^b` with `a = 2√(2π)`, `b = -s-1-3/8` (v2: "by Lemma `D:lem:symbol`, this weight is
equivalent to `e^{2√(2π)√|n|} ⟨n⟩^{-s-1-3/8}`"), with constants independent of `c`. -/
theorem orbitWeight38_comparable (lower upper : ℝ) (hl : 0 < lower) (hlu : lower ≤ upper)
    (s : ℝ) : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ c : BoundedCoefficients lower upper, ∀ n : ℤ,
      A * srcWeight (2 * Real.sqrt (2 * π)) (-s - 1 - 3 / 8) n ≤ orbitWeight38 c s n ∧
      orbitWeight38 c s n ≤ B * srcWeight (2 * Real.sqrt (2 * π)) (-s - 1 - 3 / 8) n := by
  obtain ⟨A₀, B₀, hA₀, hB₀, hsz⟩ := NlsGge.Weights.weight_two_sided_size lower upper hl hlu
  set κ : ℝ := (2 * π * Real.sqrt 2) ^ (-(3 / 8 : ℝ)) with hκ
  have hκpos : 0 < κ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Real.sqrt A₀ * κ, Real.sqrt B₀, by positivity, by positivity, fun c n => ?_⟩
  have hj := japaneseBracket_pos n
  have hjb : jbr (n : ℝ) = japaneseBracket n := rfl
  obtain ⟨hlo, hup⟩ := hsz c.val (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2)
    (2 * π * (n : ℝ))
  have habs : |2 * π * (n : ℝ)| = 2 * π * |(n : ℝ)| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  rw [habs] at hlo hup
  -- the exponential factor
  set t : ℝ := 2 * π * |(n : ℝ)| with ht
  have ht0 : 0 ≤ t := by positivity
  have hsqrt_t : Real.sqrt t = Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)| := by
    rw [ht, Real.sqrt_mul (by positivity)]
  have hexp : Real.sqrt (Real.exp (4 * Real.sqrt t)) =
      Real.exp (2 * Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)|) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_nonneg _) (Real.exp_nonneg _), ← Real.exp_add,
      hsqrt_t]
    congr 1; ring
  -- the power factor
  have hpow : ∀ q : ℝ, 0 ≤ q → Real.sqrt (q ^ (-3 / 4 : ℝ)) = q ^ (-(3 / 8 : ℝ)) := by
    intro q hq
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq]; norm_num
  have hp1 : 0 < 1 + t := by linarith
  have hlow_bd : κ * japaneseBracket n ^ (-(3 / 8 : ℝ)) ≤ (1 + t) ^ (-(3 / 8 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hp1 (one_add_le_japaneseBracket n |>.trans_eq' (by rw [ht]))
      (by norm_num : (-(3 / 8 : ℝ)) ≤ 0)
    rw [Real.mul_rpow (by positivity) hj.le] at h
    exact h
  have hup_bd : (1 + t) ^ (-(3 / 8 : ℝ)) ≤ japaneseBracket n ^ (-(3 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hj (japaneseBracket_le_one_add n) (by norm_num)
  have hsr_pos := sourceRate_pos c n
  have hE : 0 < Real.exp (2 * Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)|) := Real.exp_pos _
  have hbexp : Real.rpow (japaneseBracket n) (-s - 1) * japaneseBracket n ^ (-(3 / 8 : ℝ)) =
      jbr n ^ (-s - 1 - 3 / 8) := by
    rw [hjb]
    change japaneseBracket n ^ (-s - 1) * japaneseBracket n ^ (-(3 / 8 : ℝ)) = _
    rw [← Real.rpow_add hj]; congr 1
  have hsw : srcWeight (2 * Real.sqrt (2 * π)) (-s - 1 - 3 / 8) n =
      Real.exp (2 * Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)|) * jbr n ^ (-s - 1 - 3 / 8) := rfl
  -- bounds on √ sourceRate
  have hsl : Real.sqrt A₀ * (1 + t) ^ (-(3 / 8 : ℝ)) *
      Real.exp (2 * Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)|) ≤ Real.sqrt (sourceRate c n) := by
    have h := Real.sqrt_le_sqrt hlo
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hA₀.le, hpow _ hp1.le, hexp] at h
    exact h
  have hsu : Real.sqrt (sourceRate c n) ≤ Real.sqrt B₀ * (1 + t) ^ (-(3 / 8 : ℝ)) *
      Real.exp (2 * Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)|) := by
    have h := Real.sqrt_le_sqrt hup
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hB₀.le, hpow _ hp1.le, hexp] at h
    exact h
  have hjr : 0 < Real.rpow (japaneseBracket n) (-s - 1) := Real.rpow_pos_of_pos hj _
  have hj38 : 0 < japaneseBracket n ^ (-(3 / 8 : ℝ)) := Real.rpow_pos_of_pos hj _
  constructor
  · rw [hsw, ← hbexp]
    unfold orbitWeight38
    calc Real.sqrt A₀ * κ * (Real.exp (2 * Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)|) *
          (Real.rpow (japaneseBracket n) (-s - 1) * japaneseBracket n ^ (-(3 / 8 : ℝ))))
        = (Real.sqrt A₀ * (κ * japaneseBracket n ^ (-(3 / 8 : ℝ))) *
          Real.exp (2 * Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)|)) *
            Real.rpow (japaneseBracket n) (-s - 1) := by ring
      _ ≤ Real.sqrt (sourceRate c n) * Real.rpow (japaneseBracket n) (-s - 1) := by
        refine mul_le_mul_of_nonneg_right (le_trans ?_ hsl) hjr.le
        gcongr
  · rw [hsw, ← hbexp]
    unfold orbitWeight38
    calc Real.sqrt (sourceRate c n) * Real.rpow (japaneseBracket n) (-s - 1)
        ≤ (Real.sqrt B₀ * (1 + t) ^ (-(3 / 8 : ℝ)) *
          Real.exp (2 * Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)|)) *
            Real.rpow (japaneseBracket n) (-s - 1) := mul_le_mul_of_nonneg_right hsu hjr.le
      _ ≤ (Real.sqrt B₀ * japaneseBracket n ^ (-(3 / 8 : ℝ)) *
          Real.exp (2 * Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)|)) *
            Real.rpow (japaneseBracket n) (-s - 1) := by
        gcongr
      _ = Real.sqrt B₀ * (Real.exp (2 * Real.sqrt (2 * π) * Real.sqrt |(n : ℝ)|) *
          (Real.rpow (japaneseBracket n) (-s - 1) * japaneseBracket n ^ (-(3 / 8 : ℝ)))) := by
        ring

/-- A weight comparable (two-sided, positive constants) to an admissible weight is admissible. -/
theorem AdmissibleWeight.of_comparable {w w' : ℤ → ℝ} (hw' : AdmissibleWeight w')
    (hpos : ∀ n, 0 < w n) (heven : ∀ n, w (-n) = w n) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hlo : ∀ n, A * w' n ≤ w n) (hup : ∀ n, w n ≤ B * w' n) : AdmissibleWeight w where
  pos := hpos
  even := heven
  inv_sq := by
    refine Summable.of_nonneg_of_le (fun n => by have := hpos n; positivity) (fun n => ?_)
      (hw'.inv_sq.mul_left (A⁻¹ ^ 2))
    have h1 : A * w' n ≤ w n := hlo n
    have hp := hw'.pos n
    have hwn := hpos n
    calc (w n)⁻¹ ^ 2 ≤ (A * w' n)⁻¹ ^ 2 := by
          gcongr
      _ = A⁻¹ ^ 2 * (w' n)⁻¹ ^ 2 := by rw [mul_inv, mul_pow]
  ratio := by
    obtain ⟨r', hr'⟩ := hw'.ratio
    refine ⟨fun l => B / A ^ 2 * r' l, ?_⟩
    refine ⟨hpos, fun n => mul_nonneg (by positivity) (hr'.r_nonneg n), ?_, ?_⟩
    · have := hr'.r_sq.mul_left ((B / A ^ 2) ^ 2)
      refine this.congr fun n => ?_
      ring
    · intro k l hkl
      have h1 := hr'.ratio k l hkl
      have hwk := hlo k
      have hwl := hlo l
      have hwk' := hw'.pos k
      have hwl' := hw'.pos l
      have hr0 := hr'.r_nonneg l
      have hwk0 := hpos k
      have hwl0 := hpos l
      calc w (k + l) ≤ B * w' (k + l) := hup _
        _ ≤ B * (r' l * (w' k * w' l)) := by gcongr
        _ = B / A ^ 2 * r' l * ((A * w' k) * (A * w' l)) := by field_simp
        _ ≤ B / A ^ 2 * r' l * (w k * w l) := by
          gcongr
  exp_decay := fun c hc => by
    refine Summable.of_nonneg_of_le (fun n => by have := hpos n; positivity) (fun n => ?_)
      ((hw'.exp_decay c hc).mul_left (B ^ 2))
    have h1 := hup n
    have hp := hpos n
    calc w n ^ 2 * Real.exp (-c * |(n : ℝ)|) ≤ (B * w' n) ^ 2 * Real.exp (-c * |(n : ℝ)|) := by
          gcongr
      _ = B ^ 2 * (w' n ^ 2 * Real.exp (-c * |(n : ℝ)|)) := by ring

/-- **W04.03.** The orbit weight `√a_n ⟨n⟩^{-s-1}` is an admissible weight for the W03 composition
lemma (for every real `s`), by comparison with the W03 source weight. -/
theorem orbitWeight38_admissible (c : BoundedCoefficients lower upper) (s : ℝ) :
    AdmissibleWeight (orbitWeight38 c s) := by
  obtain ⟨A, B, hA, hB, h⟩ := orbitWeight38_comparable lower upper c.property.1 c.property.2.1 s
  have ha : 0 < 2 * Real.sqrt (2 * π) := by positivity
  exact AdmissibleWeight.of_comparable (srcWeight_admissible ha (-s - 1 - 3 / 8))
    (orbitWeight38_pos c s) (orbitWeight38_neg c s) hA hB (fun n => (h c n).1) (fun n => (h c n).2)

end Weights

end NlsGge.Birkhoff
