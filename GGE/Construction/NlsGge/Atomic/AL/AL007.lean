import Mathlib
import NlsGge.Atomic.AL.AL006

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        

/- Definitions opuc*/doubledCmvCoefficients verbatim from DEFINITIONS/AL.lean.md:97-110; cmvRho38/floquetCMV38 imported from production AL006 (not redeclared). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory
open NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

def opucTransfer (β ζ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((cmvRho38 β : ℂ)⁻¹) • !![ζ, -star β; -β * ζ, 1]

def opucPartial {p : ℕ} (β : ZMod p → ℂ) (ζ : ℂ) :
    ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | n+1 => opucTransfer (β (n : ZMod p)) ζ * opucPartial β ζ n

def opucMonodromy {p : ℕ} (β : ZMod p → ℂ) (ζ : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := opucPartial β ζ p

def doubledCmvCoefficients {L : ℕ} [NeZero L]
    (α : ZMod L → ℂ) : ZMod (2*L) → ℂ :=
  fun j => -star (α (j.val : ZMod L))


namespace AL007Aux

theorem rho_neg_star (a : ℂ) : cmvRho38 (-star a) = Real.sqrt (1 - ‖a‖ ^ 2) := by
  unfold cmvRho38
  simp [norm_neg, norm_star]

theorem transfer_conj (a z : ℂ) (hz : z ≠ 0) :
    alTransfer38 a z =
      (!![z, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) *
        (z⁻¹ • opucTransfer (-star a) (z ^ 2)) * (!![z⁻¹, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold alTransfer38 opucTransfer
  rw [rho_neg_star]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem opuc_conj (a z : ℂ) (hz : z ≠ 0) :
    opucTransfer (-star a) (z ^ 2) =
      z • ((!![z⁻¹, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * alTransfer38 a z *
        (!![z, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold alTransfer38 opucTransfer
  rw [rho_neg_star]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem castval (L : ℕ) [NeZero L] (n : ℕ) :
    (((n : ZMod (2 * L)).val : ℕ) : ZMod L) = (n : ZMod L) := by
  rw [ZMod.val_natCast]
  rw [ZMod.natCast_eq_natCast_iff']
  exact Nat.mod_mod_of_dvd n (dvd_mul_left L 2)

theorem opucPartial_eq {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (z : ℂ) (hz : z ≠ 0) (n : ℕ) :
    opucPartial (doubledCmvCoefficients α) (z ^ 2) n =
      z ^ n • ((!![z⁻¹, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * alPartial38 α z n *
        (!![z, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hDD : (!![z, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![z⁻¹, 0; 0, 1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hz]
  have hDD' : (!![z⁻¹, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![z, 0; 0, 1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hz]
  induction n with
  | zero => simp [opucPartial, alPartial38, hDD']
  | succ n ih =>
    have hb : doubledCmvCoefficients α ((n : ℕ) : ZMod (2 * L)) = -star (α (n : ZMod L)) := by
      unfold doubledCmvCoefficients
      rw [castval]
    rw [opucPartial, hb, ih, opuc_conj _ z hz, alPartial38]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ]
    congr 1
    set A := alTransfer38 (α (n : ZMod L)) z
    set P := alPartial38 α z n
    set D : Matrix (Fin 2) (Fin 2) ℂ := !![z, 0; 0, 1]
    set Di : Matrix (Fin 2) (Fin 2) ℂ := !![z⁻¹, 0; 0, 1]
    calc Di * A * D * (Di * P * D) = Di * A * (D * Di) * P * D := by
          simp only [Matrix.mul_assoc]
      _ = Di * (A * P) * D := by rw [hDD]; simp [Matrix.mul_assoc]

theorem alPartial_period {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (z : ℂ) (k : ℕ) :
    alPartial38 α z (L + k) = alPartial38 α z k * alPartial38 α z L := by
  induction k with
  | zero => simp [alPartial38]
  | succ k ih =>
    have hc : ((L + k : ℕ) : ZMod L) = (k : ZMod L) := by
      push_cast; simp
    rw [← add_assoc, alPartial38, hc, ih, alPartial38, Matrix.mul_assoc]

theorem monodromy_sq {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (z : ℂ) :
    alPartial38 α z (2 * L) = (alMonodromy38 α z) ^ 2 := by
  have h := alPartial_period α z L
  rw [two_mul, h, alMonodromy38, pow_two]

end AL007Aux

theorem al007_leaves1 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (hα : IsALField38 α) (z : ℂ) (hz : z ≠ 0) :
  let D : Matrix (Fin 2) (Fin 2) ℂ := !![z,0;0,1]
  let Dinv : Matrix (Fin 2) (Fin 2) ℂ := !![z⁻¹,0;0,1]
  let β := doubledCmvCoefficients α
  (∀ j : ZMod L,
    alTransfer38 (α j) z =
      D * (z⁻¹ • opucTransfer (-star (α j)) (z^2)) * Dinv) ∧
  IsALField38 β ∧
  (z⁻¹)^(2*L) • opucMonodromy β (z^2) =
    Dinv * (alMonodromy38 α z)^2 * D := by
  intro D Dinv β
  refine ⟨fun j => AL007Aux.transfer_conj _ z hz, ?_, ?_⟩
  · intro j
    show ‖-star (α (j.val : ZMod L))‖ < 1
    rw [norm_neg, norm_star]; exact hα _
  · unfold opucMonodromy
    rw [AL007Aux.opucPartial_eq α z hz (2 * L), AL007Aux.monodromy_sq]
    rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hz, one_pow, one_smul]


namespace AL007Aux

theorem det_transfer (a z : ℂ) (ha : ‖a‖ < 1) (hz : z ≠ 0) : (alTransfer38 a z).det = 1 := by
  have h1 : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hs : (0 : ℝ) < Real.sqrt (1 - ‖a‖ ^ 2) := Real.sqrt_pos.2 h1
  have hs2 : ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) ^ 2 = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt h1.le]
  have hsne : ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hne : (1 - ‖a‖ ^ 2 : ℂ) ≠ 0 := by
    have : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
    simpa using this
  have haa : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold alTransfer38
  rw [Matrix.det_smul, Matrix.det_fin_two_of]
  simp only [Fintype.card_fin]
  have : z * z⁻¹ - a * star a = 1 - ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [haa, mul_inv_cancel₀ hz]
  rw [this]
  field_simp
  rw [hs2]
  push_cast
  ring

theorem det_alPartial {L : ℕ} (α : ZMod L → ℂ) (hα : IsALField38 α) (z : ℂ) (hz : z ≠ 0) (n : ℕ) :
    (alPartial38 α z n).det = 1 := by
  induction n with
  | zero => simp [alPartial38]
  | succ n ih => rw [alPartial38, Matrix.det_mul, ih, det_transfer _ z (hα _) hz, one_mul]

end AL007Aux

theorem al007_of_det {L : ℕ} [NeZero L] (hodd : Odd L)
    (α : ZMod L → ℂ) (hα : IsALField38 α) (z : ℂ) (hz : z ≠ 0)
    (hdet : ∀ b : ℂ, b ≠ 0 →
      ((z^2) • (1 : Matrix (ZMod (2*L)) (ZMod (2*L)) ℂ) -
        floquetCMV38 (doubledCmvCoefficients α) b).det =
          (∏ j : ZMod (2*L), (cmvRho38 (doubledCmvCoefficients α j) : ℂ)) * (z^2)^L *
            (((alMonodromy38 α z)^2).trace - (b+b⁻¹))) :
  let D : Matrix (Fin 2) (Fin 2) ℂ := !![z,0;0,1]
  let Dinv : Matrix (Fin 2) (Fin 2) ℂ := !![z⁻¹,0;0,1]
  let β := doubledCmvCoefficients α
  (∀ j : ZMod L,
    alTransfer38 (α j) z =
      D * (z⁻¹ • opucTransfer (-star (α j)) (z^2)) * Dinv) ∧
  IsALField38 β ∧
  (z⁻¹)^(2*L) • opucMonodromy β (z^2) =
    Dinv * (alMonodromy38 α z)^2 * D ∧
  (∀ b : ℂ, b ≠ 0 →
    ((z^2) • (1 : Matrix (ZMod (2*L)) (ZMod (2*L)) ℂ) -
      floquetCMV38 β b).det =
        (∏ j : ZMod (2*L), (cmvRho38 (β j) : ℂ)) * (z^2)^L *
          (((alMonodromy38 α z)^2).trace - (b+b⁻¹))) ∧
  (∀ (w : ℂ) (u : Fin 2 → ℂ), ‖w‖ = 1 → u ≠ 0 →
    (alMonodromy38 α z).mulVec u = w • u →
      ‖w^2‖ = 1 ∧ ∃ v : EuclideanSpace ℂ (ZMod (2*L)),
        v ≠ 0 ∧ Matrix.toEuclideanLin (floquetCMV38 β (w^2)) v = (z^2) • v) := by
  intro D Dinv β
  obtain ⟨h1, h2, h3⟩ := al007_leaves1 α hα z hz
  refine ⟨h1, h2, h3, hdet, ?_⟩
  intro w u hw hu hMu
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  refine ⟨by rw [norm_pow, hw, one_pow], ?_⟩
  set M := alMonodromy38 α z with hM
  have hdM : M.det = 1 := AL007Aux.det_alPartial α hα z hz L
  have hker : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (M - w • (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec v = 0 :=
    ⟨u, hu, by rw [Matrix.sub_mulVec, hMu, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]⟩
  have hdz : (M - w • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp hker
  have htr : ((M ^ 2).trace) - (w ^ 2 + (w ^ 2)⁻¹) = 0 := by
    rw [Matrix.det_fin_two] at hdz hdM
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
      Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, smul_eq_mul, mul_one, mul_zero,
      sub_zero] at hdz
    have hs : (M 0 0 + M 1 1) * w = w ^ 2 + 1 := by linear_combination hdM - hdz
    have e : (M ^ 2).trace = (M 0 0 + M 1 1) ^ 2 - 2 := by
      rw [Matrix.trace_fin_two, pow_two]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-2) * hdM
    have hs' : M 0 0 + M 1 1 = w + w⁻¹ := by
      field_simp
      linear_combination hs
    rw [e, hs']
    field_simp
    ring
  have hdet0 : ((z^2) • (1 : Matrix (ZMod (2*L)) (ZMod (2*L)) ℂ) - floquetCMV38 β (w^2)).det = 0 := by
    rw [hdet (w^2) (pow_ne_zero 2 hw0), htr, mul_zero]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  refine ⟨WithLp.toLp 2 v, ?_, ?_⟩
  · intro h
    apply hv0
    have := congrArg WithLp.ofLp h
    simpa using this
  · rw [Matrix.sub_mulVec] at hv
    have h' : (floquetCMV38 β (w^2)).mulVec v = (z^2) • v := by
      have h'' := sub_eq_zero.mp hv
      rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h''
      exact h''.symm
    rw [Matrix.toLpLin_apply]
    simp only [WithLp.ofLp_toLp]
    rw [h']
    rfl

namespace AL007Aux

theorem natCast_eq_iff {p : ℕ} [NeZero p] (a b : ℕ) (ha : a < p) (hb : b < p) :
    ((a : ZMod p) = (b : ZMod p)) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem embed_entries {p : ℕ} {a c : ZMod p} (hac : a ≠ c) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    cmvPairEmbed38 a c B a a = B 0 0 ∧ cmvPairEmbed38 a c B a c = B 0 1 ∧
    cmvPairEmbed38 a c B c a = B 1 0 ∧ cmvPairEmbed38 a c B c c = B 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cmvPairEmbed38, hac, hac.symm]

theorem embed_apply_ite {p : ℕ} (a c x y : ZMod p) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    cmvPairEmbed38 a c B x y =
      if x = a then (if y = a then B 0 0 else if y = c then B 0 1 else 0)
      else if x = c then (if y = a then B 1 0 else if y = c then B 1 1 else 0) else 0 := rfl

/-- Entry of the even block, row `i < p`, column `j < p` (naturals cast to `ZMod p`). -/
theorem even_apply {p : ℕ} [NeZero p] (hp : p % 2 = 0) (β : ZMod p → ℂ) (i j : ℕ)
    (hi : i < p) (hj : j < p) :
    cmvEven38 β (i : ZMod p) (j : ZMod p) =
      if i % 2 = 0 then
        (if j = i then star (β (i : ZMod p))
         else if j = i + 1 then (cmvRho38 (β (i : ZMod p)) : ℂ) else 0)
      else
        (if j + 1 = i then (cmvRho38 (β ((i - 1 : ℕ) : ZMod p)) : ℂ)
         else if j = i then -β ((i - 1 : ℕ) : ZMod p) else 0) := by
  unfold cmvEven38
  rw [Matrix.sum_apply]
  obtain ⟨k, hk⟩ := Nat.even_or_odd' i
  have hkp : k < p / 2 := by rcases hk with hk | hk <;> omega
  rw [Finset.sum_eq_single (⟨k, hkp⟩ : Fin (p / 2))]
  · rcases hk with hk | hk
    · subst hk
      rw [embed_apply_ite]
      simp (disch := omega) only [natCast_eq_iff, cmvTheta38, Fin.val_mk]
      have h1 : (2 * k) % 2 = 0 := by omega
      simp only [h1, if_true]
      split_ifs <;> first | rfl | (exfalso; omega) | simp [Matrix.of_apply]
    · subst hk
      rw [embed_apply_ite]
      simp (disch := omega) only [natCast_eq_iff, cmvTheta38, Fin.val_mk]
      have h1 : ¬ (2 * k + 1) % 2 = 0 := by omega
      simp only [h1, if_false, Nat.add_sub_cancel]
      split_ifs <;> first | rfl | (exfalso; omega) | simp [Matrix.of_apply]
  · intro r _ hr
    apply P_row_zero
    · intro h
      have := (natCast_eq_iff (p := p) i (2 * r.val) hi (by have := r.isLt; omega)).1 h
      apply hr; apply Fin.ext; have := r.isLt; simp only; omega
    · intro h
      have := (natCast_eq_iff (p := p) i (2 * r.val + 1) hi (by have := r.isLt; omega)).1 h
      apply hr; apply Fin.ext; have := r.isLt; simp only; omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem c_val {p : ℕ} [NeZero p] (hp : p % 2 = 0) (r : ℕ) (hr : r < p / 2) :
    ∃ v : ℕ, v < p ∧ ((2 * r + 2 : ℕ) : ZMod p) = (v : ZMod p) ∧
      ((v = 2 * r + 2 ∧ 2 * r + 2 < p) ∨ (2 * r + 2 = p ∧ v = 0)) := by
  by_cases h : 2 * r + 2 < p
  · exact ⟨2 * r + 2, h, rfl, Or.inl ⟨rfl, h⟩⟩
  · have h2 : 2 * r + 2 = p := by omega
    refine ⟨0, by have := NeZero.pos p; omega, ?_, Or.inr ⟨h2, rfl⟩⟩
    rw [h2, ZMod.natCast_self]; simp

theorem odd_other {p : ℕ} [NeZero p] (hp : p % 2 = 0) (β : ZMod p → ℂ) (b : ℂ) (i j : ℕ)
    (hi : i < p) (r0 : Fin (p / 2))
    (hh : i = 2 * r0.val + 1 ∨ (i = 2 * r0.val + 2 ∧ 2 * r0.val + 2 < p) ∨
      (i = 0 ∧ 2 * r0.val + 2 = p)) (r : Fin (p / 2)) (hr : r ≠ r0) :
    cmvPairEmbed38 ((2 * r.val + 1 : ℕ) : ZMod p) ((2 * r.val + 2 : ℕ) : ZMod p)
      (cmvTwistedTheta38 (β ((2 * r.val + 1 : ℕ) : ZMod p))
        (if 2 * r.val + 2 = p then b else 1)) (i : ZMod p) (j : ZMod p) = 0 := by
  apply P_row_zero
  · intro h1
    have := (natCast_eq_iff (p := p) i (2 * r.val + 1) hi (by have := r.isLt; omega)).1 h1
    apply hr; apply Fin.ext
    have := r.isLt; have := r0.isLt
    omega
  · obtain ⟨v, hv, hcv, hv2⟩ := c_val hp r.val r.isLt
    intro h1
    rw [hcv] at h1
    have := (natCast_eq_iff (p := p) i v hi hv).1 h1
    apply hr; apply Fin.ext
    have := r.isLt; have := r0.isLt
    omega

/-- Entry of the odd block (twisted by `b` at the wrap-around), row `i < p`, column `j < p`. -/
theorem odd_apply {p : ℕ} [NeZero p] (hp : p % 2 = 0) (β : ZMod p → ℂ) (b : ℂ) (i j : ℕ)
    (hi : i < p) (hj : j < p) :
    cmvOdd38 β b (i : ZMod p) (j : ZMod p) =
      if i % 2 = 1 then
        (if j = i then star (β (i : ZMod p))
         else if i + 1 < p then (if j = i + 1 then (cmvRho38 (β (i : ZMod p)) : ℂ) else 0)
         else (if j = 0 then (cmvRho38 (β (i : ZMod p)) : ℂ) * b⁻¹ else 0))
      else
        (if i = 0 then
          (if j = p - 1 then (cmvRho38 (β ((p - 1 : ℕ) : ZMod p)) : ℂ) * b
           else if j = 0 then -β ((p - 1 : ℕ) : ZMod p) else 0)
         else
          (if j + 1 = i then (cmvRho38 (β ((i - 1 : ℕ) : ZMod p)) : ℂ)
           else if j = i then -β ((i - 1 : ℕ) : ZMod p) else 0)) := by
  unfold cmvOdd38
  rw [Matrix.sum_apply]
  have hpp : 0 < p := NeZero.pos p
  by_cases hodd : i % 2 = 1
  · -- row a of block k = i / 2
    have hk : i / 2 < p / 2 := by omega
    rw [Finset.sum_eq_single (⟨i / 2, hk⟩ : Fin (p / 2))]
    · obtain ⟨v, hv, hcv, hv2⟩ := c_val hp (i / 2) hk
      have hi' : 2 * (i / 2) + 1 = i := by omega
      simp only [hi']
      rw [hcv, embed_apply_ite]
      simp (disch := omega) only [natCast_eq_iff, cmvTwistedTheta38, Fin.val_mk, hi']
      simp only [hodd, if_true]
      rcases hv2 with ⟨hv2, hlt⟩ | ⟨hv2, hv0⟩
      · have h2 : 2 * (i / 2) + 2 = i + 1 := by omega
        have h3 : ¬ (2 * (i / 2) + 2 = p) := by omega
        simp only [h3, if_false, hlt]
        subst hv2
        split_ifs <;> first | rfl | (exfalso; omega) | simp [Matrix.of_apply]
      · have h3 : 2 * (i / 2) + 2 = p := hv2
        have h4 : ¬ (i + 1 < p) := by omega
        simp only [h3, if_true, h4, if_false, hv0]
        split_ifs <;> first | rfl | (exfalso; omega) | simp [Matrix.of_apply]
    · intro r _ hr
      exact odd_other hp β b i j hi ⟨i / 2, hk⟩ (Or.inl (by simp; omega)) r hr
    · intro h; exact absurd (Finset.mem_univ _) h
  · by_cases hi0 : i = 0
    · subst hi0
      have hk : p / 2 - 1 < p / 2 := by omega
      rw [Finset.sum_eq_single (⟨p / 2 - 1, hk⟩ : Fin (p / 2))]
      · obtain ⟨v, hv, hcv, hv2⟩ := c_val hp (p / 2 - 1) hk
        have h3 : 2 * (p / 2 - 1) + 2 = p := by omega
        have h4 : 2 * (p / 2 - 1) + 1 = p - 1 := by omega
        rcases hv2 with ⟨_, hlt⟩ | ⟨_, hv0⟩
        · omega
        · simp only [Fin.val_mk, h4]
          rw [hcv, embed_apply_ite]
          simp only [hv0, h3, if_true]
          simp (disch := omega) only [natCast_eq_iff, cmvTwistedTheta38, Fin.val_mk]
          simp only [hodd, if_false, if_true]
          split_ifs <;> first | rfl | (exfalso; omega) | simp [Matrix.of_apply]
      · intro r _ hr
        exact odd_other hp β b 0 j hi ⟨p / 2 - 1, hk⟩ (Or.inr (Or.inr ⟨rfl, by show 2 * (p / 2 - 1) + 2 = p; omega⟩)) r hr
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hk : i / 2 - 1 < p / 2 := by omega
      rw [Finset.sum_eq_single (⟨i / 2 - 1, hk⟩ : Fin (p / 2))]
      · obtain ⟨v, hv, hcv, hv2⟩ := c_val hp (i / 2 - 1) hk
        have h3 : 2 * (i / 2 - 1) + 2 = i := by omega
        have h4 : 2 * (i / 2 - 1) + 1 = i - 1 := by omega
        have h5 : ¬ (2 * (i / 2 - 1) + 2 = p) := by omega
        simp only [Fin.val_mk, h4]
        rw [hcv, embed_apply_ite]
        rcases hv2 with ⟨hv2, hlt⟩ | ⟨hv2, _⟩
        · simp only [hv2, h3, h5, if_false]
          simp (disch := omega) only [natCast_eq_iff, cmvTwistedTheta38, Fin.val_mk]
          simp only [hodd, if_false, hi0]
          split_ifs <;> first | rfl | (exfalso; omega) | simp [Matrix.of_apply]
        · omega
      · intro r _ hr
        exact odd_other hp β b i j hi ⟨i / 2 - 1, hk⟩ (Or.inr (Or.inl ⟨by simp; omega, by simp; omega⟩)) r hr
      · intro h; exact absurd (Finset.mem_univ _) h

theorem det_theta (a : ℂ) (ha : ‖a‖ < 1) : (cmvTheta38 a).det = -1 := by
  have h1 : (0 : ℝ) ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hs : ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) ^ 2 = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt h1]
  have haa : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold cmvTheta38 cmvRho38
  rw [Matrix.det_fin_two_of]
  push_cast at hs haa ⊢
  linear_combination (-1 : ℂ) * hs - haa

/-- Reindexing equivalence `Fin L × Fin 2 ≃ ZMod (2L)`. -/
def pairEquiv (L : ℕ) [NeZero L] : Fin L × Fin 2 ≃ ZMod (2 * L) :=
  Equiv.ofBijective (fun x => ((2 * x.1.val + x.2.val : ℕ) : ZMod (2 * L))) (by
    have hL := NeZero.pos L
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · rintro ⟨r, k⟩ ⟨r', k'⟩ h
      have hr := r.isLt; have hr' := r'.isLt; have hk := k.isLt; have hk' := k'.isLt
      have := (natCast_eq_iff (p := 2 * L) _ _ (by omega) (by omega)).1 h
      dsimp only at this
      simp only [Prod.mk.injEq]
      constructor <;> apply Fin.ext <;> omega
    · simp [ZMod.card, mul_comm])

/-- `Fin 2 × Fin L ≃ ZMod (2L)`, `(k,r) ↦ 2r+k`, so that `blockDiagonal` applies. -/
def pairEquiv' (L : ℕ) [NeZero L] : Fin 2 × Fin L ≃ ZMod (2 * L) :=
  (Equiv.prodComm _ _).trans (pairEquiv L)

theorem pairEquiv'_apply (L : ℕ) [NeZero L] (k : Fin 2) (r : Fin L) :
    pairEquiv' L (k, r) = ((2 * r.val + k.val : ℕ) : ZMod (2 * L)) := rfl

theorem det_even (L : ℕ) [NeZero L] (β : ZMod (2 * L) → ℂ) (hβ : ∀ j, ‖β j‖ < 1) :
    (cmvEven38 β).det = (-1) ^ L := by
  have hp : (2 * L) % 2 = 0 := by omega
  rw [← Matrix.det_reindex_self (pairEquiv' L).symm (cmvEven38 β)]
  have hent : Matrix.reindex (pairEquiv' L).symm (pairEquiv' L).symm (cmvEven38 β) =
      Matrix.blockDiagonal (fun r : Fin L => cmvTheta38 (β ((2 * r.val : ℕ) : ZMod (2 * L)))) := by
    ext ⟨k, r⟩ ⟨k', r'⟩
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.blockDiagonal_apply]
    rw [pairEquiv'_apply, pairEquiv'_apply]
    have hr := r.isLt; have hr' := r'.isLt; have hk := k.isLt; have hk' := k'.isLt
    rw [even_apply hp β (2 * r.val + k.val) (2 * r'.val + k'.val) (by omega) (by omega)]
    fin_cases k <;> fin_cases k' <;>
      simp [cmvTheta38] <;> split_ifs <;> first | rfl | (exfalso; omega) | skip
  rw [hent, Matrix.det_blockDiagonal]
  rw [Finset.prod_congr rfl (fun r _ => det_theta _ (hβ _))]
  simp


namespace Tridiag

variable {R : Type*} [CommRing R]

/-- Open tridiagonal matrix with diagonal `d (a+i)`, superdiagonal `u (a+i)` at `(i,i+1)`, subdiagonal `l (a+j)` at `(j+1,j)`. -/
def tri (d u l : ℕ → R) (a n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then d (a + i)
    else if (j : ℕ) = i + 1 then u (a + i)
    else if (i : ℕ) = j + 1 then l (a + j) else 0

/-- Continuant `K(a,m)`. -/
def cont (d u l : ℕ → R) : ℕ → ℕ → R
  | 0, _ => 1
  | 1, a => d a
  | m + 2, a => d a * cont d u l (m + 1) (a + 1) - u a * l a * cont d u l m (a + 2)

theorem tri_minor00 (d u l : ℕ → R) (a n : ℕ) :
    (tri d u l a (n + 1)).submatrix Fin.succ Fin.succ = tri d u l (a + 1) n := by
  ext i j
  simp only [tri, Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ]
  have h1 : a + (↑i + 1) = a + 1 + ↑i := by omega
  have h2 : a + (↑j + 1) = a + 1 + ↑j := by omega
  rw [h1, h2]
  by_cases hij : (i : ℕ) = j
  · simp [hij]
  · have : ¬ ((i : ℕ) + 1 = (j : ℕ) + 1) := by omega
    simp [hij, this]

theorem tri_minor01 (d u l : ℕ → R) (a n : ℕ) :
    ((tri d u l a (n + 2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2)))).submatrix
      Fin.succ Fin.succ = tri d u l (a + 2) n := by
  ext i j
  have e : ((Fin.succAbove (1 : Fin (n + 2)) (Fin.succ j) : Fin (n + 2)) : ℕ) = (j : ℕ) + 2 := by
    simp [Fin.succAbove, Fin.lt_def]
  simp only [tri, Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ, e]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

theorem det_minor01 (d u l : ℕ → R) (a n : ℕ) :
    ((tri d u l a (n + 2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2)))).det =
      l a * (tri d u l (a + 2) n).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz : ∀ i : Fin n, ((tri d u l a (n + 2)).submatrix Fin.succ
      (Fin.succAbove (1 : Fin (n + 2)))) i.succ 0 = 0 := by
    intro i
    have e0 : (Fin.succAbove (1 : Fin (n + 2)) 0 : Fin (n + 2)) = 0 := by
      simp [Fin.succAbove, Fin.lt_def]
    simp only [Matrix.submatrix_apply, e0, tri, Matrix.of_apply, Fin.val_succ, Fin.val_zero]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hrest : ∑ i : Fin n, (-1 : R) ^ (i.succ : ℕ) *
      ((tri d u l a (n + 2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2)))) i.succ 0 *
      Matrix.det (((tri d u l a (n + 2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2)))).submatrix
        i.succ.succAbove Fin.succ) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hz i]; simp
  rw [hrest, add_zero]
  have e1 : ((tri d u l a (n + 2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2)))) 0 0 = l a := by
    have e0 : (Fin.succAbove (1 : Fin (n + 2)) 0 : Fin (n + 2)) = 0 := by
      simp [Fin.succAbove, Fin.lt_def]
    simp [Matrix.submatrix_apply, e0, tri]
  rw [e1]
  have e2 : ((tri d u l a (n + 2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2)))).submatrix
      (Fin.succAbove (0 : Fin (n + 1))) Fin.succ = tri d u l (a + 2) n := by
    rw [Fin.succAbove_zero]; exact tri_minor01 d u l a n
  rw [e2]; simp

theorem det_tri (d u l : ℕ → R) : ∀ n a : ℕ, (tri d u l a n).det = cont d u l n a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a
    match n, ih with
    | 0, _ => simp [cont]
    | 1, _ => simp [cont, tri, Matrix.det_unique]
    | n + 2, ih =>
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
      have hz : ∀ k : Fin n, (tri d u l a (n + 2)) 0 k.succ.succ = 0 := by
        intro k
        simp only [tri, Matrix.of_apply, Fin.val_succ, Fin.val_zero]
        split_ifs <;> first | rfl | (exfalso; omega)
      have hrest : ∑ k : Fin n, (-1 : R) ^ (k.succ.succ : ℕ) * (tri d u l a (n + 2)) 0 k.succ.succ *
          Matrix.det ((tri d u l a (n + 2)).submatrix Fin.succ k.succ.succ.succAbove) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [hz k]; simp
      rw [hrest, add_zero]
      have m00 : (tri d u l a (n + 2)).submatrix Fin.succ (Fin.succAbove (0 : Fin (n + 2))) =
          tri d u l (a + 1) (n + 1) := by
        rw [Fin.succAbove_zero]; exact tri_minor00 d u l a (n + 1)
      have m01 := det_minor01 d u l a n
      have a00 : (tri d u l a (n + 2)) 0 0 = d a := by simp [tri]
      have a01 : (tri d u l a (n + 2)) 0 (Fin.succ 0) = u a := by simp [tri]
      rw [m00, a00, a01]
      rw [show (Fin.succ (0 : Fin (n + 1))) = (1 : Fin (n + 2)) from rfl, m01,
        ih (n + 1) (by omega), ih n (by omega)]
      simp [cont]
      ring

theorem det_tri_super (d u l : ℕ → R) (a m : ℕ) :
    ((tri d u l a (m + 1)).submatrix Fin.castSucc Fin.succ).det = ∏ i : Fin m, u (a + i) := by
  have hT : ((tri d u l a (m + 1)).submatrix Fin.castSucc Fin.succ).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := by simpa using hij
    simp only [Matrix.submatrix_apply, tri, Matrix.of_apply, Fin.val_succ, Fin.coe_castSucc]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [Matrix.det_of_lowerTriangular _ hT]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Matrix.submatrix_apply, tri, Matrix.of_apply, Fin.val_succ, Fin.coe_castSucc]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem det_tri_sub (d u l : ℕ → R) (a m : ℕ) :
    ((tri d u l a (m + 1)).submatrix Fin.succ Fin.castSucc).det = ∏ i : Fin m, l (a + i) := by
  have hT : ((tri d u l a (m + 1)).submatrix Fin.succ Fin.castSucc).BlockTriangular id := by
    intro i j hij
    have hij' : (j : ℕ) < (i : ℕ) := by simpa using hij
    simp only [Matrix.submatrix_apply, tri, Matrix.of_apply, Fin.val_succ, Fin.coe_castSucc]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [Matrix.det_of_upperTriangular hT]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Matrix.submatrix_apply, tri, Matrix.of_apply, Fin.val_succ, Fin.coe_castSucc]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Cyclic tridiagonal matrix with ADDITIVE corners `s` at `(0,n-1)` and `t` at `(n-1,0)`. -/
def cyc (d u l : ℕ → R) (s t : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => tri d u l 0 n i j + (if (i : ℕ) = 0 ∧ (j : ℕ) = n - 1 then s else 0) +
    (if (i : ℕ) = n - 1 ∧ (j : ℕ) = 0 then t else 0)

theorem sa1_val {k : ℕ} (j : Fin k) : ((Fin.succAbove (1 : Fin (k + 2)) j.succ : Fin (k + 2)) : ℕ) = (j : ℕ) + 2 := by
  simp [Fin.succAbove, Fin.lt_def]

theorem sa1_zero {k : ℕ} : (Fin.succAbove (1 : Fin (k + 2)) 0 : Fin (k + 2)) = 0 := by
  simp [Fin.succAbove, Fin.lt_def]

theorem cyc_sub_eq (d u l : ℕ → R) (s t : R) (n m : ℕ) (f g : Fin m → Fin n)
    (hc : ∀ i j, ¬ (((f i : Fin n) : ℕ) = 0 ∧ ((g j : Fin n) : ℕ) = n - 1) ∧
      ¬ (((f i : Fin n) : ℕ) = n - 1 ∧ ((g j : Fin n) : ℕ) = 0)) :
    (cyc d u l s t n).submatrix f g = (tri d u l 0 n).submatrix f g := by
  ext i j
  obtain ⟨h1, h2⟩ := hc i j
  simp [cyc, h1, h2]

theorem cyc_m00 (d u l : ℕ → R) (s t : R) (n : ℕ) :
    (cyc d u l s t (n + 3)).submatrix Fin.succ Fin.succ = tri d u l 1 (n + 2) := by
  rw [cyc_sub_eq d u l s t (n + 3) (n + 2) Fin.succ Fin.succ (by
    intro i j; simp only [Fin.val_succ]; omega)]
  simpa using tri_minor00 d u l 0 (n + 2)

theorem sa1_comp (n : ℕ) :
    (Fin.succAbove (1 : Fin (n + 3)) ∘ Fin.succ : Fin (n + 1) → Fin (n + 3)) = Fin.succ ∘ Fin.succ := by
  funext j
  apply Fin.ext
  simp [sa1_val]

theorem cyc_m01a (d u l : ℕ → R) (s t : R) (n : ℕ) :
    ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 3)))).submatrix
      (Fin.succAbove (0 : Fin (n + 2))) Fin.succ = tri d u l 2 (n + 1) := by
  rw [Matrix.submatrix_submatrix, cyc_sub_eq d u l s t (n + 3) (n + 1) _ _ (by
    intro i j
    simp only [Function.comp, Fin.succAbove_zero, Fin.val_succ, sa1_val]; omega)]
  rw [Fin.succAbove_zero, sa1_comp]
  have h0 := tri_minor00 d u l 0 (n + 2)
  have h1 := tri_minor00 d u l 1 (n + 1)
  rw [zero_add] at h0
  rw [← Matrix.submatrix_submatrix, h0]
  exact h1

theorem cyc_m01b (d u l : ℕ → R) (s t : R) (n : ℕ) :
    ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 3)))).submatrix
      (Fin.succAbove (Fin.last (n + 1))) Fin.succ = (tri d u l 1 (n + 2)).submatrix Fin.castSucc Fin.succ := by
  rw [Matrix.submatrix_submatrix, cyc_sub_eq d u l s t (n + 3) (n + 1) _ _ (by
    intro i j
    simp only [Function.comp, Fin.succAbove_last, Fin.val_succ, Fin.coe_castSucc, sa1_val]; omega)]
  rw [Fin.succAbove_last, sa1_comp]
  have h0 := tri_minor00 d u l 0 (n + 2)
  rw [zero_add] at h0
  rw [← h0, Matrix.submatrix_submatrix]

theorem tri_castSucc (d u l : ℕ → R) (a n : ℕ) :
    (tri d u l a (n + 1)).submatrix Fin.castSucc Fin.castSucc = tri d u l a n := by
  ext i j
  simp [tri]

theorem col0_expand {n : ℕ} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (h : ∀ i : Fin n, M (Fin.castSucc i).succ 0 = 0) :
    M.det = M 0 0 * (M.submatrix (Fin.succAbove (0 : Fin (n + 2))) Fin.succ).det +
      (-1) ^ (n + 1) * M (Fin.last (n + 1)) 0 *
        (M.submatrix (Fin.succAbove (Fin.last (n + 1))) Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hz : ∑ i : Fin n, (-1 : R) ^ ((Fin.castSucc i).succ : ℕ) * M (Fin.castSucc i).succ 0 *
      (M.submatrix (Fin.castSucc i).succ.succAbove Fin.succ).det = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [h i]; simp
  rw [hz]
  simp [Fin.succ_last]

theorem det_M01 (d u l : ℕ → R) (s t : R) (n : ℕ) :
    ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 3)))).det =
      l 0 * cont d u l (n + 1) 2 + (-1) ^ (n + 1) * t * ∏ i : Fin (n + 1), u (1 + i) := by
  rw [col0_expand, cyc_m01a, cyc_m01b, det_tri, det_tri_super]
  · have e0 : ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 3)))) 0 0 = l 0 := by
      simp [Matrix.submatrix_apply, sa1_zero, cyc, tri]
    have e1 : ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 3))))
        (Fin.last (n + 1)) 0 = t := by
      simp [Matrix.submatrix_apply, sa1_zero, cyc, tri]
    rw [e0, e1]
  · intro i
    simp [Matrix.submatrix_apply, sa1_zero, cyc, tri]
    omega

theorem cyc_m0na (d u l : ℕ → R) (s t : R) (n : ℕ) :
    ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.castSucc : Fin (n + 2) → Fin (n + 3))).submatrix
      (Fin.succAbove (0 : Fin (n + 2))) Fin.succ = (tri d u l 1 (n + 2)).submatrix Fin.succ Fin.castSucc := by
  rw [Matrix.submatrix_submatrix, cyc_sub_eq d u l s t (n + 3) (n + 1) _ _ (by
    intro i j
    simp only [Function.comp, Fin.succAbove_zero, Fin.val_succ, Fin.coe_castSucc]; omega)]
  have h0 := tri_minor00 d u l 0 (n + 2)
  rw [zero_add] at h0
  rw [← h0, Matrix.submatrix_submatrix, Fin.succAbove_zero]
  have hc : (Fin.castSucc ∘ Fin.succ : Fin (n + 1) → Fin (n + 3)) = Fin.succ ∘ Fin.castSucc := by
    funext j; exact (Fin.succ_castSucc j).symm
  rw [hc]

theorem cyc_m0nb (d u l : ℕ → R) (s t : R) (n : ℕ) :
    ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.castSucc : Fin (n + 2) → Fin (n + 3))).submatrix
      (Fin.succAbove (Fin.last (n + 1))) Fin.succ = tri d u l 1 (n + 1) := by
  rw [Matrix.submatrix_submatrix, cyc_sub_eq d u l s t (n + 3) (n + 1) _ _ (by
    intro i j
    simp only [Function.comp, Fin.succAbove_last, Fin.val_succ, Fin.coe_castSucc]; omega)]
  have h0 := tri_minor00 d u l 0 (n + 2)
  rw [zero_add] at h0
  have h1 := tri_castSucc d u l 1 (n + 1)
  rw [← h1, ← h0, Matrix.submatrix_submatrix, Fin.succAbove_last]
  have hc : (Fin.castSucc ∘ Fin.succ : Fin (n + 1) → Fin (n + 3)) = Fin.succ ∘ Fin.castSucc := by
    funext j; exact (Fin.succ_castSucc j).symm
  rw [hc]

theorem det_M0n (d u l : ℕ → R) (s t : R) (n : ℕ) :
    ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.castSucc : Fin (n + 2) → Fin (n + 3))).det =
      l 0 * ∏ i : Fin (n + 1), l (1 + i) + (-1) ^ (n + 1) * t * cont d u l (n + 1) 1 := by
  rw [col0_expand, cyc_m0na, cyc_m0nb, det_tri, det_tri_sub]
  · have e0 : ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.castSucc : Fin (n + 2) → Fin (n + 3))) 0 0 = l 0 := by
      simp [Matrix.submatrix_apply, cyc, tri]
    have e1 : ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.castSucc : Fin (n + 2) → Fin (n + 3)))
        (Fin.last (n + 1)) 0 = t := by
      simp [Matrix.submatrix_apply, cyc, tri]
    rw [e0, e1]
  · intro i
    simp [Matrix.submatrix_apply, cyc, tri]
    omega

theorem det_cyc3 (d u l : ℕ → R) (s t : R) (n : ℕ) :
    (cyc d u l s t (n + 3)).det =
      cont d u l (n + 3) 0 - s * t * cont d u l (n + 1) 1 +
        (-1) ^ n * (s * ∏ i : Fin (n + 2), l (0 + i) + t * ∏ i : Fin (n + 2), u (0 + i)) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hz : ∀ k : Fin n, (cyc d u l s t (n + 3)) 0 (Fin.castSucc k).succ.succ = 0 := by
    intro k
    simp [cyc, tri]
    omega
  have hzs : ∑ k : Fin n, (-1 : R) ^ ((Fin.castSucc k).succ.succ : ℕ) *
      (cyc d u l s t (n + 3)) 0 (Fin.castSucc k).succ.succ *
      Matrix.det ((cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.castSucc k).succ.succ.succAbove) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hz k]; simp
  rw [hzs, zero_add]
  have a00 : (cyc d u l s t (n + 3)) 0 0 = d 0 := by simp [cyc, tri]
  have a01 : (cyc d u l s t (n + 3)) 0 (Fin.succ 0) = u 0 := by simp [cyc, tri]
  have a0n : (cyc d u l s t (n + 3)) 0 (Fin.last n).succ.succ = s := by
    simp [cyc, tri]
  have m00 : (cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.succAbove (0 : Fin (n + 3))) =
      tri d u l 1 (n + 2) := by
    rw [Fin.succAbove_zero]; exact cyc_m00 d u l s t n
  have m0n : (cyc d u l s t (n + 3)).submatrix Fin.succ
      (Fin.succAbove (Fin.last n).succ.succ) =
      (cyc d u l s t (n + 3)).submatrix Fin.succ (Fin.castSucc : Fin (n + 2) → Fin (n + 3)) := by
    have : (Fin.last n).succ.succ = Fin.last (n + 2) := by simp
    rw [this, Fin.succAbove_last]
  rw [a00, a01, a0n, m00, m0n, show (Fin.succ (0 : Fin (n + 2))) = (1 : Fin (n + 3)) from rfl]
  rw [det_M01, det_M0n, det_tri]
  have pl : ∏ i : Fin (n + 2), l (0 + i) = l 0 * ∏ i : Fin (n + 1), l (1 + i) := by
    rw [Fin.prod_univ_succ]; simp [add_comm]
  have pu : ∏ i : Fin (n + 2), u (0 + i) = u 0 * ∏ i : Fin (n + 1), u (1 + i) := by
    rw [Fin.prod_univ_succ]; simp [add_comm]
  rw [pl, pu]
  rw [show cont d u l (n + 3) 0 = d 0 * cont d u l (n + 2) 1 - u 0 * l 0 * cont d u l (n + 1) 2 from rfl]
  have hsq : ((-1 : R) ^ n) * ((-1 : R) ^ n) = 1 := by rw [← mul_pow]; simp
  simp only [Fin.val_succ, Fin.val_zero, Fin.val_last, Fin.val_one, pow_succ, pow_zero]
  linear_combination (-(t * s * cont d u l (n + 1) 1)) * hsq

theorem det_cyc2 (d u l : ℕ → R) (s t : R) :
    (cyc d u l s t 2).det = cont d u l 2 0 - s * t * cont d u l 0 1 - (s * l 0 + t * u 0) := by
  rw [Matrix.det_fin_two]
  simp [cyc, tri, cont]
  ring


theorem det_cyc3r (d u l : ℕ → R) (s t : R) (n : ℕ) :
    (cyc d u l s t (n + 3)).det =
      cont d u l (n + 3) 0 - s * t * cont d u l (n + 1) 1 +
        (-1) ^ n * (s * ∏ i ∈ Finset.range (n + 2), l i + t * ∏ i ∈ Finset.range (n + 2), u i) := by
  rw [det_cyc3]
  have h1 := Fin.prod_univ_eq_prod_range (fun i => l (0 + i)) (n + 2)
  have h2 := Fin.prod_univ_eq_prod_range (fun i => u (0 + i)) (n + 2)
  simp only [zero_add] at h1 h2 ⊢
  rw [h1, h2]

theorem det_cyc_ge3 (d u l : ℕ → R) (s t : R) (p : ℕ) (hp : 3 ≤ p) :
    (cyc d u l s t p).det =
      cont d u l p 0 - s * t * cont d u l (p - 2) 1 +
        (-1) ^ (p - 3) * (s * ∏ i ∈ Finset.range (p - 1), l i + t * ∏ i ∈ Finset.range (p - 1), u i) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 3 := ⟨p - 3, by omega⟩
  have := det_cyc3r d u l s t n
  simpa using this

end Tridiag

section Neq
variable {p : ℕ} [NeZero p]

def Nmat (β : ZMod p → ℂ) (ζ b : ℂ) : Matrix (ZMod p) (ZMod p) ℂ :=
  cmvOdd38 β b - ζ • (cmvEven38 β)ᴴ

theorem shift_cast (n : ℕ) (hn : 0 < n) : ((n + p - 1 : ℕ) : ZMod p) = ((n - 1 : ℕ) : ZMod p) := by
  have hp0 := NeZero.pos p
  have : n + p - 1 = (n - 1) + p := by omega
  rw [this]; push_cast; simp

theorem Nmat_apply (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ b : ℂ) (n m : ℕ) (hn : n < p) (hm : m < p) :
    Nmat β ζ b (n : ZMod p) (m : ZMod p) =
      cmvOdd38 β b (n : ZMod p) (m : ZMod p) - ζ * star (cmvEven38 β (m : ZMod p) (n : ZMod p)) := by
  unfold Nmat
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.conjTranspose_apply, smul_eq_mul]

theorem NE (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ b : ℂ) (n : ℕ) (hn : n < p) (hn2 : n % 2 = 0) :
    Nmat β ζ b (n : ZMod p) (n : ZMod p) = -β ((n + p - 1 : ℕ) : ZMod p) - ζ * β (n : ZMod p) := by
  have hp0 := NeZero.pos p
  rw [Nmat_apply hp β ζ b n n hn hn, odd_apply hp β b n n hn hn, even_apply hp β n n hn hn]
  by_cases hn0 : n = 0
  · subst hn0
    simp [show (0:ℕ) ≠ p - 1 by omega]
  · have hs := shift_cast (p := p) n (by omega)
    rw [hs]
    have h1 : ¬ n % 2 = 1 := by omega
    simp [h1, hn2, hn0]

theorem NO (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ b : ℂ) (n : ℕ) (hn : n < p) (hn2 : n % 2 = 1) :
    Nmat β ζ b (n : ZMod p) (n : ZMod p) = star (β (n : ZMod p)) + ζ * star (β ((n + p - 1 : ℕ) : ZMod p)) := by
  have hp0 := NeZero.pos p
  rw [Nmat_apply hp β ζ b n n hn hn, odd_apply hp β b n n hn hn, even_apply hp β n n hn hn]
  have hs := shift_cast (p := p) n (by omega)
  rw [hs]
  have h1 : ¬ n % 2 = 0 := by omega
  simp [h1, hn2]

theorem SE (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ b : ℂ) (n : ℕ) (hn : n + 1 < p) (hn2 : n % 2 = 0)
    (hp4 : 4 ≤ p) :
    Nmat β ζ b (n : ZMod p) ((n + 1 : ℕ) : ZMod p) = -ζ * (cmvRho38 (β (n : ZMod p)) : ℂ) := by
  have hp0 := NeZero.pos p
  rw [Nmat_apply hp β ζ b n (n + 1) (by omega) hn, odd_apply hp β b n (n + 1) (by omega) hn,
    even_apply hp β (n + 1) n hn (by omega)]
  have h1 : ¬ n % 2 = 1 := by omega
  have h2 : ¬ (n + 1) % 2 = 0 := by omega
  by_cases hn0 : n = 0
  · subst hn0
    simp [show (1:ℕ) ≠ p - 1 by omega]
  · simp [h1, h2, hn0, show ¬ (n + 1 + 1 = n) from by omega]

theorem SO (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ b : ℂ) (n : ℕ) (hn : n + 1 < p) (hn2 : n % 2 = 1)
    (hp4 : 4 ≤ p) :
    Nmat β ζ b (n : ZMod p) ((n + 1 : ℕ) : ZMod p) = (cmvRho38 (β (n : ZMod p)) : ℂ) := by
  have hp0 := NeZero.pos p
  rw [Nmat_apply hp β ζ b n (n + 1) (by omega) hn, odd_apply hp β b n (n + 1) (by omega) hn,
    even_apply hp β (n + 1) n hn (by omega)]
  have h1 : n % 2 = 1 := hn2
  have h2 : (n + 1) % 2 = 0 := by omega
  simp [h1, h2, hn, show ¬ (n = n + 1 + 1) from by omega, show ¬ (n + 1 = n) from by omega]

theorem LE (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ b : ℂ) (m : ℕ) (hn : m + 1 < p) (hm2 : m % 2 = 0)
    (hp4 : 4 ≤ p) :
    Nmat β ζ b ((m + 1 : ℕ) : ZMod p) (m : ZMod p) = -ζ * (cmvRho38 (β (m : ZMod p)) : ℂ) := by
  have hp0 := NeZero.pos p
  rw [Nmat_apply hp β ζ b (m + 1) m hn (by omega), odd_apply hp β b (m + 1) m hn (by omega),
    even_apply hp β m (m + 1) (by omega) hn]
  have h1 : (m + 1) % 2 = 1 := by omega
  have h2 : m % 2 = 0 := hm2
  by_cases hlt : m + 1 + 1 < p
  · simp [h1, h2, hlt, show ¬ (m = m + 1) from by omega, show ¬ (m = m + 1 + 1) from by omega]
  · have hmp : m + 2 = p := by omega
    simp [h1, h2, hlt, show ¬ (m = m + 1) from by omega, show ¬ (m = 0) from by omega]

theorem LO (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ b : ℂ) (m : ℕ) (hn : m + 1 < p) (hm2 : m % 2 = 1)
    (hp4 : 4 ≤ p) :
    Nmat β ζ b ((m + 1 : ℕ) : ZMod p) (m : ZMod p) = (cmvRho38 (β (m : ZMod p)) : ℂ) := by
  have hp0 := NeZero.pos p
  rw [Nmat_apply hp β ζ b (m + 1) m hn (by omega), odd_apply hp β b (m + 1) m hn (by omega),
    even_apply hp β m (m + 1) (by omega) hn]
  have h1 : ¬ (m + 1) % 2 = 1 := by omega
  have h2 : ¬ m % 2 = 0 := by omega
  simp [h1, h2, show ¬ (m + 1 = 0) from by omega, show ¬ (m + 1 = m + 1 + 1) from by omega,
    show ¬ (m + 1 + 1 = m) from by omega]

theorem CS (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ b : ℂ) (hp4 : 4 ≤ p) :
    Nmat β ζ b ((0 : ℕ) : ZMod p) ((p - 1 : ℕ) : ZMod p) =
      (cmvRho38 (β ((p - 1 : ℕ) : ZMod p)) : ℂ) * b := by
  have hp0 := NeZero.pos p
  rw [Nmat_apply hp β ζ b 0 (p - 1) hp0 (by omega), odd_apply hp β b 0 (p - 1) hp0 (by omega),
    even_apply hp β (p - 1) 0 (by omega) hp0]
  have h1 : (p - 1) % 2 = 1 := by omega
  simp [h1, show ¬ (p - 1 = 0) from by omega, show ¬ (p - 1 + 1 = 0) from by omega,
    show ¬ (1 = p - 1) from by omega, show ¬ (0 = p - 1) from by omega]

theorem CT (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ b : ℂ) (hp4 : 4 ≤ p) :
    Nmat β ζ b ((p - 1 : ℕ) : ZMod p) ((0 : ℕ) : ZMod p) =
      (cmvRho38 (β ((p - 1 : ℕ) : ZMod p)) : ℂ) * b⁻¹ := by
  have hp0 := NeZero.pos p
  rw [Nmat_apply hp β ζ b (p - 1) 0 (by omega) hp0, odd_apply hp β b (p - 1) 0 (by omega) hp0,
    even_apply hp β 0 (p - 1) hp0 (by omega)]
  have h1 : (p - 1) % 2 = 1 := by omega
  simp [h1, show ¬ (p - 1 + 1 < p) from by omega, show ¬ (p - 1 = 0) from by omega,
    show ¬ (p - 1 = 1) from by omega, show ¬ (0 = p - 1) from by omega]

theorem ZR (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ b : ℂ) (n m : ℕ) (hn : n < p) (hm : m < p)
    (hp4 : 4 ≤ p) (h1 : m ≠ n) (h2 : m ≠ n + 1) (h3 : n ≠ m + 1)
    (h4 : ¬ (n = 0 ∧ m = p - 1)) (h5 : ¬ (n = p - 1 ∧ m = 0)) :
    Nmat β ζ b (n : ZMod p) (m : ZMod p) = 0 := by
  have hp0 := NeZero.pos p
  rw [Nmat_apply hp β ζ b n m hn hm, odd_apply hp β b n m hn hm, even_apply hp β m n hm hn]
  split_ifs <;> first | (exfalso; omega) | simp

def dseq (β : ZMod p → ℂ) (ζ : ℂ) (n : ℕ) : ℂ :=
  if n % 2 = 0 then -β ((n + p - 1 : ℕ) : ZMod p) - ζ * β (n : ZMod p)
  else star (β (n : ZMod p)) + ζ * star (β ((n + p - 1 : ℕ) : ZMod p))

def useq (β : ZMod p → ℂ) (ζ : ℂ) (n : ℕ) : ℂ :=
  if n % 2 = 0 then -ζ * (cmvRho38 (β (n : ZMod p)) : ℂ) else (cmvRho38 (β (n : ZMod p)) : ℂ)

theorem Nmat_eq_cyc (hp : p % 2 = 0) (hp4 : 4 ≤ p) (β : ZMod p → ℂ) (ζ b : ℂ) (i j : Fin p) :
    Nmat β ζ b ((i : ℕ) : ZMod p) ((j : ℕ) : ZMod p) =
      Tridiag.cyc (dseq β ζ) (useq β ζ) (useq β ζ)
        ((cmvRho38 (β ((p - 1 : ℕ) : ZMod p)) : ℂ) * b)
        ((cmvRho38 (β ((p - 1 : ℕ) : ZMod p)) : ℂ) * b⁻¹) p i j := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Tridiag.cyc Tridiag.tri
  simp only [Matrix.of_apply, zero_add]
  generalize (i : ℕ) = n at hi ⊢
  generalize (j : ℕ) = m at hj ⊢
  by_cases hmn : m = n
  · subst hmn
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [NE hp β ζ b m hi h]
      simp [dseq, h, show ¬ (m = 0 ∧ m = p - 1) from by omega, show ¬ (m = p - 1 ∧ m = 0) from by omega]
    · rw [NO hp β ζ b m hi h]
      simp [dseq, h, show ¬ (m = 0 ∧ m = p - 1) from by omega, show ¬ (m = p - 1 ∧ m = 0) from by omega]
  · by_cases h2 : m = n + 1
    · subst h2
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · rw [SE hp β ζ b n hj h hp4]
        simp [useq, h, show ¬ (n + 1 = n) from by omega, show ¬ (n = 0 ∧ n + 1 = p - 1) from by omega,
          show ¬ (n = p - 1 ∧ n + 1 = 0) from by omega]
      · rw [SO hp β ζ b n hj h hp4]
        simp [useq, h, show ¬ (n + 1 = n) from by omega, show ¬ (n = 0 ∧ n + 1 = p - 1) from by omega,
          show ¬ (n = p - 1 ∧ n + 1 = 0) from by omega]
    · by_cases h3 : n = m + 1
      · subst h3
        rcases Nat.mod_two_eq_zero_or_one m with h | h
        · rw [LE hp β ζ b m hi h hp4]
          simp [useq, h, show ¬ (m = m + 1) from by omega, show ¬ (m + 1 = m) from by omega,
            show ¬ (m = m + 1 + 1) from by omega,
            show ¬ (m + 1 = 0 ∧ m = p - 1) from by omega, show ¬ (m + 1 = p - 1 ∧ m = 0) from by omega]
        · rw [LO hp β ζ b m hi h hp4]
          simp [useq, h, show ¬ (m = m + 1) from by omega, show ¬ (m + 1 = m) from by omega,
            show ¬ (m = m + 1 + 1) from by omega,
            show ¬ (m + 1 = 0 ∧ m = p - 1) from by omega, show ¬ (m + 1 = p - 1 ∧ m = 0) from by omega]
      · by_cases h4 : n = 0 ∧ m = p - 1
        · obtain ⟨rfl, rfl⟩ := h4
          rw [CS hp β ζ b hp4]
          simp [show ¬ (p - 1 = 0) from by omega, show ¬ (p - 1 = 0 + 1) from by omega,
            show ¬ (0 = p - 1 + 1) from by omega, show ¬ (0 = p - 1) from by omega]
        · by_cases h5 : n = p - 1 ∧ m = 0
          · obtain ⟨rfl, rfl⟩ := h5
            rw [CT hp β ζ b hp4]
            simp [show ¬ (p - 1 = 0) from by omega, show ¬ (0 = p - 1 + 1) from by omega,
              show ¬ (p - 1 = 0 + 1) from by omega, show ¬ (0 = p - 1) from by omega]
          · rw [ZR hp β ζ b n m hi hj hp4 hmn h2 h3 h4 h5]
            have h6 : ¬ n = m := fun h => hmn h.symm
            simp [h6, hmn, h2, h3, h4, h5]

theorem finZMod_inj (p : ℕ) [NeZero p] : Function.Injective (fun i : Fin p => ((i : ℕ) : ZMod p)) := by
  intro i j h
  exact Fin.ext ((natCast_eq_iff (p := p) _ _ i.isLt j.isLt).1 h)

/-- `Fin p ≃ ZMod p`, `i ↦ (i : ZMod p)`. -/
def finZMod (p : ℕ) [NeZero p] : Fin p ≃ ZMod p :=
  Equiv.ofBijective (fun i : Fin p => ((i : ℕ) : ZMod p))
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨finZMod_inj p, by simp [ZMod.card]⟩)

theorem det_Nmat (hp : p % 2 = 0) (hp4 : 4 ≤ p) (β : ZMod p → ℂ) (ζ b : ℂ) :
    (Nmat β ζ b).det = (Tridiag.cyc (dseq β ζ) (useq β ζ) (useq β ζ)
        ((cmvRho38 (β ((p - 1 : ℕ) : ZMod p)) : ℂ) * b)
        ((cmvRho38 (β ((p - 1 : ℕ) : ZMod p)) : ℂ) * b⁻¹) p).det := by
  have h : Tridiag.cyc (dseq β ζ) (useq β ζ) (useq β ζ)
        ((cmvRho38 (β ((p - 1 : ℕ) : ZMod p)) : ℂ) * b)
        ((cmvRho38 (β ((p - 1 : ℕ) : ZMod p)) : ℂ) * b⁻¹) p =
      (Nmat β ζ b).submatrix (finZMod p) (finZMod p) := by
    ext i j
    exact (Nmat_eq_cyc hp hp4 β ζ b i j).symm
  rw [h, Matrix.det_submatrix_equiv_self]

theorem det_floquet_eq (L : ℕ) [NeZero L] (hL : 2 ≤ L) (β : ZMod (2 * L) → ℂ)
    (hβ : ∀ j, ‖β j‖ < 1) (ζ b : ℂ) :
    (ζ • (1 : Matrix (ZMod (2 * L)) (ZMod (2 * L)) ℂ) - floquetCMV38 β b).det =
      (-1) ^ L * (Tridiag.cyc (dseq β ζ) (useq β ζ) (useq β ζ)
        ((cmvRho38 (β ((2 * L - 1 : ℕ) : ZMod (2 * L))) : ℂ) * b)
        ((cmvRho38 (β ((2 * L - 1 : ℕ) : ZMod (2 * L))) : ℂ) * b⁻¹) (2 * L)).det := by
  have hp : (2 * L) % 2 = 0 := by omega
  have hp4 : 4 ≤ 2 * L := by omega
  have hE : cmvEven38 β * (cmvEven38 β)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 (cmv_even_mem hp β hβ)
    simpa [Matrix.star_eq_conjTranspose] using this
  have hfac : ζ • (1 : Matrix (ZMod (2 * L)) (ZMod (2 * L)) ℂ) - floquetCMV38 β b =
      cmvEven38 β * (ζ • (cmvEven38 β)ᴴ - cmvOdd38 β b) := by
    unfold floquetCMV38
    rw [Matrix.mul_sub, Matrix.mul_smul, hE]
  rw [hfac, Matrix.det_mul, det_even L β hβ]
  have hneg : ζ • (cmvEven38 β)ᴴ - cmvOdd38 β b = -(Nmat β ζ b) := by
    unfold Nmat; rw [neg_sub]
  rw [hneg, Matrix.det_neg, ZMod.card, det_Nmat hp hp4]
  have : ((-1 : ℂ) ^ (2 * L)) = 1 := by rw [pow_mul]; simp
  rw [this, one_mul]

theorem Nmat_eq_cyc_two (β : ZMod 2 → ℂ) (ζ b : ℂ) (i j : Fin 2) :
    Nmat β ζ b ((i : ℕ) : ZMod 2) ((j : ℕ) : ZMod 2) =
      Tridiag.cyc (dseq β ζ) (useq β ζ) (useq β ζ)
        ((cmvRho38 (β ((2 - 1 : ℕ) : ZMod 2)) : ℂ) * b)
        ((cmvRho38 (β ((2 - 1 : ℕ) : ZMod 2)) : ℂ) * b⁻¹) 2 i j := by
  have hp : (2 : ℕ) % 2 = 0 := by norm_num
  fin_cases i <;> fin_cases j <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.val_zero, Fin.val_one]
    rw [Nmat_apply hp β ζ b _ _ (by norm_num) (by norm_num), odd_apply hp β b _ _ (by norm_num) (by norm_num),
      even_apply hp β _ _ (by norm_num) (by norm_num)]
    simp [dseq, useq, Tridiag.cyc, Tridiag.tri, show (2 : ZMod 2) = 0 from rfl]
    try (left; apply congrArg; apply congrArg; decide)
    try ring

theorem det_floquet_two (β : ZMod 2 → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (ζ b : ℂ) :
    (ζ • (1 : Matrix (ZMod 2) (ZMod 2) ℂ) - floquetCMV38 β b).det =
      (-1) ^ 1 * (Tridiag.cyc (dseq β ζ) (useq β ζ) (useq β ζ)
        ((cmvRho38 (β ((2 - 1 : ℕ) : ZMod 2)) : ℂ) * b)
        ((cmvRho38 (β ((2 - 1 : ℕ) : ZMod 2)) : ℂ) * b⁻¹) 2).det := by
  have hp : (2 : ℕ) % 2 = 0 := by norm_num
  have hE : cmvEven38 β * (cmvEven38 β)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 (cmv_even_mem hp β hβ)
    simpa [Matrix.star_eq_conjTranspose] using this
  have hfac : ζ • (1 : Matrix (ZMod 2) (ZMod 2) ℂ) - floquetCMV38 β b =
      cmvEven38 β * (ζ • (cmvEven38 β)ᴴ - cmvOdd38 β b) := by
    unfold floquetCMV38
    rw [Matrix.mul_sub, Matrix.mul_smul, hE]
  have hdE : (cmvEven38 β).det = (-1) ^ 1 := det_even 1 β hβ
  rw [hfac, Matrix.det_mul, hdE]
  have hneg : ζ • (cmvEven38 β)ᴴ - cmvOdd38 β b = -(Nmat β ζ b) := by
    unfold Nmat; rw [neg_sub]
  rw [hneg, Matrix.det_neg, ZMod.card]
  have h2 : (Tridiag.cyc (dseq β ζ) (useq β ζ) (useq β ζ)
        ((cmvRho38 (β ((2 - 1 : ℕ) : ZMod 2)) : ℂ) * b)
        ((cmvRho38 (β ((2 - 1 : ℕ) : ZMod 2)) : ℂ) * b⁻¹) 2) =
      (Nmat β ζ b).submatrix (finZMod 2) (finZMod 2) := by
    ext i j
    exact (Nmat_eq_cyc_two β ζ b i j).symm
  rw [h2, Matrix.det_submatrix_equiv_self]
  have : ((-1 : ℂ) ^ 2) = 1 := by norm_num
  rw [this, one_mul]

end Neq
namespace Eig

/-- Szego/OPUC iterate `w_n = τ_{n-1} ⋯ τ_0 w₀`, `τ_n = [[ζ, -conj β_n],[-β_n ζ, 1]]`. -/
def Wseq (β : ℕ → ℂ) (ζ : ℂ) (w0 : ℂ × ℂ) : ℕ → ℂ × ℂ
  | 0 => w0
  | n + 1 => (ζ * (Wseq β ζ w0 n).1 - star (β n) * (Wseq β ζ w0 n).2,
      -(β n) * ζ * (Wseq β ζ w0 n).1 + (Wseq β ζ w0 n).2)

/-- `Ĉ_n = ζ^{-⌊n/2⌋} s_n`, `s_n = (w_n)_2` for even `n`, `(w_n)_1` for odd `n`. -/
def Chat (β : ℕ → ℂ) (ζ : ℂ) (w0 : ℂ × ℂ) (n : ℕ) : ℂ :=
  (ζ⁻¹) ^ (n / 2) * (if n % 2 = 0 then (Wseq β ζ w0 n).2 else (Wseq β ζ w0 n).1)

/-- `Ỹ_{2k} = conj β_{2k} Ĉ_{2k} + Ĉ_{2k+1}`, `Ỹ_{2k+1} = ρ_{2k}² Ĉ_{2k} − β_{2k} Ĉ_{2k+1}`. -/
def Ytil (β ρ : ℕ → ℂ) (ζ : ℂ) (w0 : ℂ × ℂ) (n : ℕ) : ℂ :=
  if n % 2 = 0 then star (β n) * Chat β ζ w0 n + Chat β ζ w0 (n + 1)
  else ρ (n - 1) * ρ (n - 1) * Chat β ζ w0 (n - 1) - β (n - 1) * Chat β ζ w0 n

def W1 (β : ℕ → ℂ) (ζ : ℂ) (n : ℕ) : ℂ × ℂ := Wseq β ζ (1, 0) n
def W2 (β : ℕ → ℂ) (ζ : ℂ) (n : ℕ) : ℂ × ℂ := Wseq β ζ (0, 1) n

theorem Wseq_lin (β : ℕ → ℂ) (ζ x y : ℂ) (n : ℕ) :
    Wseq β ζ (x, y) n = (x * (W1 β ζ n).1 + y * (W2 β ζ n).1, x * (W1 β ζ n).2 + y * (W2 β ζ n).2) := by
  induction n with
  | zero => simp [Wseq, W1, W2]
  | succ n ih =>
    simp only [Wseq, W1, W2] at ih ⊢
    rw [ih]
    ext <;> simp <;> ring

theorem det_W (β : ℕ → ℂ) (ζ : ℂ) (n : ℕ) :
    (W1 β ζ n).1 * (W2 β ζ n).2 - (W2 β ζ n).1 * (W1 β ζ n).2 =
      ∏ j ∈ Finset.range n, (ζ * (1 - β j * star (β j))) := by
  induction n with
  | zero => simp [W1, W2, Wseq]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih]
    simp only [W1, W2, Wseq]
    ring

theorem exists_eig (β : ℕ → ℂ) (ζ c : ℂ) (hc : c ≠ 0) (n : ℕ)
    (hdet : (W1 β ζ n).1 * (W2 β ζ n).2 - (W2 β ζ n).1 * (W1 β ζ n).2 = c * c) :
    ∃ μ : ℂ, μ ≠ 0 ∧ μ + μ⁻¹ = ((W1 β ζ n).1 + (W2 β ζ n).2) / c ∧
      ∃ w0 : ℂ × ℂ, w0 ≠ 0 ∧ Wseq β ζ w0 n = (c * μ * w0.1, c * μ * w0.2) := by
  set T := (W1 β ζ n).1 + (W2 β ζ n).2 with hT
  obtain ⟨sq, hsq⟩ := IsAlgClosed.exists_eq_mul_self ((T / c) ^ 2 - 4)
  set μ : ℂ := (T / c + sq) / 2 with hμ
  have hquad : μ ^ 2 - (T / c) * μ + 1 = 0 := by
    rw [hμ]; linear_combination (-1 / 4 : ℂ) * hsq
  have hμ0 : μ ≠ 0 := by
    intro h; rw [h] at hquad; simp at hquad
  refine ⟨μ, hμ0, ?_, ?_⟩
  · field_simp; field_simp at hquad; linear_combination hquad
  · set Mx : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(W1 β ζ n).1 - c * μ, (W2 β ζ n).1; (W1 β ζ n).2, (W2 β ζ n).2 - c * μ] with hMx
    have hdz : Mx.det = 0 := by
      rw [hMx, Matrix.det_fin_two_of]
      have hTc : (W1 β ζ n).1 + (W2 β ζ n).2 = c * (T / c) := by
        rw [← hT]; field_simp
      linear_combination hdet - (c * μ) * hTc + c ^ 2 * hquad
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdz
    refine ⟨(v 0, v 1), ?_, ?_⟩
    · intro h
      apply hv0
      ext i; fin_cases i
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    · rw [Wseq_lin]
      have h0 := congrFun hv 0
      have h1 := congrFun hv 1
      simp [hMx, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
      ext
      · simp only; linear_combination h0
      · simp only; linear_combination h1

variable (β ρ : ℕ → ℂ) (ζ : ℂ) (w0 : ℂ × ℂ)

theorem localA (hζ : ζ ≠ 0) (hρ : ∀ n, ρ n * ρ n = 1 - β n * star (β n)) (k : ℕ) :
    ζ * Chat β ζ w0 (2 * k + 1) =
      star (β (2 * k + 1)) * Ytil β ρ ζ w0 (2 * k + 1) + Ytil β ρ ζ w0 (2 * k + 2) := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 2) % 2 = 0 := by omega
  have h3 : (2 * k + 1) / 2 = k := by omega
  have h4 : (2 * k + 2) / 2 = k + 1 := by omega
  have h5 : (2 * k + 3) / 2 = k + 1 := by omega
  have h6 : (2 * k + 3) % 2 = 1 := by omega
  have h7 : (2 * k) % 2 = 0 := by omega
  have h8 : (2 * k) / 2 = k := by omega
  unfold Ytil
  simp only [h1, h2, show ¬ (2 * k + 1) % 2 = 0 from by omega, if_true, if_false,
    show 2 * k + 1 - 1 = 2 * k from by omega, show 2 * k + 2 + 1 = 2 * k + 3 from by omega]
  unfold Chat
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, if_true, if_false,
    show ¬ (2 * k + 1) % 2 = 0 from by omega, show ¬ (2 * k + 3) % 2 = 0 from by omega,
    show 2 * k + 3 = (2 * k + 2) + 1 from rfl, show 2 * k + 2 = (2 * k + 1) + 1 from rfl,
    show 2 * k + 1 = (2 * k) + 1 from rfl, Wseq]
  rw [hρ (2 * k)]
  simp only [Nat.one_ne_zero, if_false]
  have hz : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ
  linear_combination (-(ζ⁻¹ ^ k) * (β (2 * k) * star (β (2 * k + 1)) * (Wseq β ζ w0 (2 * k)).1 * ζ
    - star (β (2 * k)) * (Wseq β ζ w0 (2 * k)).2 * ζ - star (β (2 * k + 1)) * (Wseq β ζ w0 (2 * k)).2
    + (Wseq β ζ w0 (2 * k)).1 * ζ ^ 2)) * hz

theorem localB (hζ : ζ ≠ 0) (hρ : ∀ n, ρ n * ρ n = 1 - β n * star (β n)) (k : ℕ) :
    ζ * Chat β ζ w0 (2 * k + 2) =
      ρ (2 * k + 1) * ρ (2 * k + 1) * Ytil β ρ ζ w0 (2 * k + 1) - β (2 * k + 1) * Ytil β ρ ζ w0 (2 * k + 2) := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 2) % 2 = 0 := by omega
  have h3 : (2 * k + 1) / 2 = k := by omega
  have h4 : (2 * k + 2) / 2 = k + 1 := by omega
  have h5 : (2 * k + 3) / 2 = k + 1 := by omega
  have h6 : (2 * k + 3) % 2 = 1 := by omega
  have h7 : (2 * k) % 2 = 0 := by omega
  have h8 : (2 * k) / 2 = k := by omega
  unfold Ytil
  simp only [h1, h2, show ¬ (2 * k + 1) % 2 = 0 from by omega, if_true, if_false,
    show 2 * k + 1 - 1 = 2 * k from by omega, show 2 * k + 2 + 1 = 2 * k + 3 from by omega]
  unfold Chat
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, if_true, if_false,
    show ¬ (2 * k + 1) % 2 = 0 from by omega, show ¬ (2 * k + 3) % 2 = 0 from by omega,
    show 2 * k + 3 = (2 * k + 2) + 1 from rfl, show 2 * k + 2 = (2 * k + 1) + 1 from rfl,
    show 2 * k + 1 = (2 * k) + 1 from rfl, Wseq]
  rw [hρ (2 * k + 1), hρ (2 * k)]
  simp only [Nat.one_ne_zero, if_false]
  have hz : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ
  linear_combination ((ζ⁻¹ ^ k) * (β (2 * k + 1) * star (β (2 * k + 1)) - 1) *
    (β (2 * k) * (Wseq β ζ w0 (2 * k)).1 * ζ - (Wseq β ζ w0 (2 * k)).2)) * hz


end Eig

section Vec
variable {p : ℕ} [NeZero p]

theorem zmod_val_eq (x : ZMod p) (n : ℕ) (hn : n < p) : x = (n : ZMod p) ↔ x.val = n := by
  constructor
  · intro h; rw [h, ZMod.val_natCast_of_lt hn]
  · intro h; rw [← h, ZMod.natCast_zmod_val]

def bN (β : ZMod p → ℂ) (n : ℕ) : ℂ := β (n : ZMod p)
def rN (β : ZMod p → ℂ) (n : ℕ) : ℂ := (cmvRho38 (β (n : ZMod p)) : ℂ)
def PN (β : ZMod p → ℂ) (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, rN β j

def chiV (β : ZMod p → ℂ) (ζ : ℂ) (w0 : ℂ × ℂ) : ZMod p → ℂ :=
  fun i => Eig.Chat (bN β) ζ w0 i.val / PN β i.val

def yV (β : ZMod p → ℂ) (ζ : ℂ) (w0 : ℂ × ℂ) : ZMod p → ℂ :=
  fun i => Eig.Ytil (bN β) (rN β) ζ w0 i.val / PN β i.val

theorem Ey_even (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ : ℂ) (w0 : ℂ × ℂ) (n : ℕ) (hn : n < p)
    (hn2 : n % 2 = 0) :
    (cmvEven38 β *ᵥ chiV β ζ w0) (n : ZMod p) =
      star (β (n : ZMod p)) * (Eig.Chat (bN β) ζ w0 n / PN β n) +
        (cmvRho38 (β (n : ZMod p)) : ℂ) * (Eig.Chat (bN β) ζ w0 (n + 1) / PN β (n + 1)) := by
  have hn1 : n + 1 < p := by omega
  have hne : (n : ZMod p) ≠ ((n + 1 : ℕ) : ZMod p) := by
    intro h; have := (natCast_eq_iff (p := p) _ _ hn hn1).1 h; omega
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_add (n : ZMod p) ((n + 1 : ℕ) : ZMod p) hne]
  · rw [even_apply hp β n n hn hn, even_apply hp β n (n + 1) hn hn1]
    have h1 : ¬ (n + 1 = n) := by omega
    simp only [chiV, ZMod.val_natCast_of_lt hn, ZMod.val_natCast_of_lt hn1, hn2, h1, if_true,
      if_false]
  · intro x hx
    have hxv : x = ((x.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val x).symm
    have hxl : x.val < p := ZMod.val_lt x
    rw [hxv, even_apply hp β n x.val hn hxl]
    have h1 : ¬ x.val = n := fun h => hx.1 (by rw [hxv, h])
    have h2 : ¬ x.val = n + 1 := fun h => hx.2 (by rw [hxv, h])
    simp [hn2, h1, h2]

theorem Ey_odd (hp : p % 2 = 0) (β : ZMod p → ℂ) (ζ : ℂ) (w0 : ℂ × ℂ) (n : ℕ) (hn : n < p)
    (hn2 : n % 2 = 1) :
    (cmvEven38 β *ᵥ chiV β ζ w0) (n : ZMod p) =
      (cmvRho38 (β ((n - 1 : ℕ) : ZMod p)) : ℂ) * (Eig.Chat (bN β) ζ w0 (n - 1) / PN β (n - 1)) -
        β ((n - 1 : ℕ) : ZMod p) * (Eig.Chat (bN β) ζ w0 n / PN β n) := by
  have hn1 : n - 1 < p := by omega
  have hne : ((n - 1 : ℕ) : ZMod p) ≠ (n : ZMod p) := by
    intro h; have := (natCast_eq_iff (p := p) _ _ hn1 hn).1 h; omega
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_add ((n - 1 : ℕ) : ZMod p) (n : ZMod p) hne]
  · rw [even_apply hp β n (n - 1) hn hn1, even_apply hp β n n hn hn]
    have h0 : ¬ n % 2 = 0 := by omega
    have h1 : n - 1 + 1 = n := by omega
    have h2 : ¬ n = n - 1 := by omega
    have h4 : ¬ (1 + n = n) := by omega
    have h5 : ¬ (n + 1 = n) := by omega
    simp only [chiV, ZMod.val_natCast_of_lt hn, ZMod.val_natCast_of_lt hn1, h0, h1, h2, h4, h5, if_true, if_false]
    ring
  · intro x hx
    have hxv : x = ((x.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val x).symm
    have hxl : x.val < p := ZMod.val_lt x
    rw [hxv, even_apply hp β n x.val hn hxl]
    have h1 : ¬ x.val = n - 1 := fun h => hx.1 (by rw [hxv, h])
    have h2 : ¬ x.val = n := fun h => hx.2 (by rw [hxv, h])
    have h0 : ¬ n % 2 = 0 := by omega
    have h3 : ¬ x.val + 1 = n := fun h => h1 (by omega)
    simp [h0, h1, h2, h3]

theorem Oy_odd_lt (hp : p % 2 = 0) (β : ZMod p → ℂ) (b ζ : ℂ) (w0 : ℂ × ℂ) (n : ℕ) (hn : n + 1 < p)
    (hn2 : n % 2 = 1) :
    (cmvOdd38 β b *ᵥ yV β ζ w0) (n : ZMod p) =
      star (β (n : ZMod p)) * (Eig.Ytil (bN β) (rN β) ζ w0 n / PN β n) +
        (cmvRho38 (β (n : ZMod p)) : ℂ) * (Eig.Ytil (bN β) (rN β) ζ w0 (n + 1) / PN β (n + 1)) := by
  have hn0 : n < p := by omega
  have hne : (n : ZMod p) ≠ ((n + 1 : ℕ) : ZMod p) := by
    intro h; have := (natCast_eq_iff (p := p) _ _ hn0 hn).1 h; omega
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_add (n : ZMod p) ((n + 1 : ℕ) : ZMod p) hne]
  · rw [odd_apply hp β b n n hn0 hn0, odd_apply hp β b n (n + 1) hn0 hn]
    have h1 : ¬ (n + 1 = n) := by omega
    simp only [yV, ZMod.val_natCast_of_lt hn0, ZMod.val_natCast_of_lt hn, hn2, h1, hn, if_true, if_false]
  · intro x hx
    have hxv : x = ((x.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val x).symm
    have hxl : x.val < p := ZMod.val_lt x
    rw [hxv, odd_apply hp β b n x.val hn0 hxl]
    have h1 : ¬ x.val = n := fun h => hx.1 (by rw [hxv, h])
    have h2 : ¬ x.val = n + 1 := fun h => hx.2 (by rw [hxv, h])
    simp [hn2, h1, h2, hn]

theorem Oy_odd_wrap (hp : p % 2 = 0) (β : ZMod p → ℂ) (b ζ : ℂ) (w0 : ℂ × ℂ) (n : ℕ) (hn : n < p)
    (hn1 : ¬ n + 1 < p) (hn2 : n % 2 = 1) :
    (cmvOdd38 β b *ᵥ yV β ζ w0) (n : ZMod p) =
      star (β (n : ZMod p)) * (Eig.Ytil (bN β) (rN β) ζ w0 n / PN β n) +
        (cmvRho38 (β (n : ZMod p)) : ℂ) * b⁻¹ * (Eig.Ytil (bN β) (rN β) ζ w0 0 / PN β 0) := by
  have hp0 := NeZero.pos p
  have hne : (n : ZMod p) ≠ ((0 : ℕ) : ZMod p) := by
    intro h; have := (natCast_eq_iff (p := p) _ _ hn hp0).1 h; omega
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_add (n : ZMod p) ((0 : ℕ) : ZMod p) hne]
  · rw [odd_apply hp β b n n hn hn, odd_apply hp β b n 0 hn hp0]
    have h1 : ¬ (0 = n) := by omega
    simp only [yV, ZMod.val_natCast_of_lt hn, ZMod.val_natCast_of_lt hp0, hn2, hn1, h1, if_true, if_false]
  · intro x hx
    have hxv : x = ((x.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val x).symm
    have hxl : x.val < p := ZMod.val_lt x
    rw [hxv, odd_apply hp β b n x.val hn hxl]
    have h1 : ¬ x.val = n := fun h => hx.1 (by rw [hxv, h])
    have h2 : ¬ x.val = 0 := fun h => hx.2 (by rw [hxv, h])
    simp [hn2, h1, h2, hn1]

theorem Oy_even_pos (hp : p % 2 = 0) (β : ZMod p → ℂ) (b ζ : ℂ) (w0 : ℂ × ℂ) (n : ℕ) (hn : n < p)
    (hn2 : n % 2 = 0) (hn0 : n ≠ 0) :
    (cmvOdd38 β b *ᵥ yV β ζ w0) (n : ZMod p) =
      (cmvRho38 (β ((n - 1 : ℕ) : ZMod p)) : ℂ) * (Eig.Ytil (bN β) (rN β) ζ w0 (n - 1) / PN β (n - 1)) -
        β ((n - 1 : ℕ) : ZMod p) * (Eig.Ytil (bN β) (rN β) ζ w0 n / PN β n) := by
  have hn1 : n - 1 < p := by omega
  have hne : ((n - 1 : ℕ) : ZMod p) ≠ (n : ZMod p) := by
    intro h; have := (natCast_eq_iff (p := p) _ _ hn1 hn).1 h; omega
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_add ((n - 1 : ℕ) : ZMod p) (n : ZMod p) hne]
  · rw [odd_apply hp β b n (n - 1) hn hn1, odd_apply hp β b n n hn hn]
    have h0 : ¬ n % 2 = 1 := by omega
    have h1 : n - 1 + 1 = n := by omega
    have h2 : ¬ n = n - 1 := by omega
    have h4 : ¬ (1 + n = n) := by omega
    have h5 : ¬ (n + 1 = n) := by omega
    simp only [yV, ZMod.val_natCast_of_lt hn, ZMod.val_natCast_of_lt hn1, h0, h1, h2, h4, h5, hn0, if_true, if_false]
    ring
  · intro x hx
    have hxv : x = ((x.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val x).symm
    have hxl : x.val < p := ZMod.val_lt x
    rw [hxv, odd_apply hp β b n x.val hn hxl]
    have h1 : ¬ x.val = n - 1 := fun h => hx.1 (by rw [hxv, h])
    have h2 : ¬ x.val = n := fun h => hx.2 (by rw [hxv, h])
    have h3 : ¬ x.val + 1 = n := fun h => h1 (by omega)
    simp [hn2, hn0, h1, h2, h3]

theorem Oy_zero (hp : p % 2 = 0) (β : ZMod p → ℂ) (b ζ : ℂ) (w0 : ℂ × ℂ) (hp2 : 2 ≤ p) :
    (cmvOdd38 β b *ᵥ yV β ζ w0) ((0 : ℕ) : ZMod p) =
      (cmvRho38 (β ((p - 1 : ℕ) : ZMod p)) : ℂ) * b *
          (Eig.Ytil (bN β) (rN β) ζ w0 (p - 1) / PN β (p - 1)) -
        β ((p - 1 : ℕ) : ZMod p) * (Eig.Ytil (bN β) (rN β) ζ w0 0 / PN β 0) := by
  have hp0 : 0 < p := by omega
  have hp1 : p - 1 < p := by omega
  have hne : ((p - 1 : ℕ) : ZMod p) ≠ ((0 : ℕ) : ZMod p) := by
    intro h; have := (natCast_eq_iff (p := p) _ _ hp1 hp0).1 h; omega
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_add ((p - 1 : ℕ) : ZMod p) ((0 : ℕ) : ZMod p) hne]
  · rw [odd_apply hp β b 0 (p - 1) hp0 hp1, odd_apply hp β b 0 0 hp0 hp0]
    have h1 : ¬ (0 = p - 1) := by omega
    simp only [yV, ZMod.val_natCast_of_lt hp1, ZMod.val_natCast_of_lt hp0, if_true, if_false, h1,
      show ¬ (0 % 2 = 1) from by omega, show (0 : ℕ) = 0 from rfl]
    ring
  · intro x hx
    have hxv : x = ((x.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val x).symm
    have hxl : x.val < p := ZMod.val_lt x
    rw [hxv, odd_apply hp β b 0 x.val hp0 hxl]
    have h1 : ¬ x.val = p - 1 := fun h => hx.1 (by rw [hxv, h])
    have h2 : ¬ x.val = 0 := fun h => hx.2 (by rw [hxv, h])
    simp [h1, h2]

theorem rN_ne (β : ZMod p → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (n : ℕ) : rN β n ≠ 0 := by
  unfold rN cmvRho38
  have h1 : (0 : ℝ) < 1 - ‖β (n : ZMod p)‖ ^ 2 := by
    have := hβ (n : ZMod p); nlinarith [norm_nonneg (β (n : ZMod p))]
  exact_mod_cast (Real.sqrt_pos.2 h1).ne'

theorem rN_sq (β : ZMod p → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (n : ℕ) :
    rN β n * rN β n = 1 - bN β n * star (bN β n) := by
  unfold rN bN
  rw [cmv_rho_sq (β (n : ZMod p)) (hβ _).le, Complex.star_def]

theorem PN_ne (β : ZMod p → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (n : ℕ) : PN β n ≠ 0 :=
  Finset.prod_ne_zero_iff.2 (fun j _ => rN_ne β hβ j)

theorem PN_succ (β : ZMod p → ℂ) (n : ℕ) : PN β (n + 1) = PN β n * rN β n := Finset.prod_range_succ _ _

theorem Ey_eq (hp : p % 2 = 0) (β : ZMod p → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (ζ : ℂ) (w0 : ℂ × ℂ) (n : ℕ) (hn : n < p) :
    (cmvEven38 β *ᵥ chiV β ζ w0) (n : ZMod p) = yV β ζ w0 (n : ZMod p) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [Ey_even hp β ζ w0 n hn h]
    simp only [yV, ZMod.val_natCast_of_lt hn, Eig.Ytil, h, if_true]
    have h1 := PN_ne β hβ n
    have h2 := rN_ne β hβ n
    rw [PN_succ]
    simp only [rN, bN] at *
    field_simp
  · rw [Ey_odd hp β ζ w0 n hn h]
    simp only [yV, ZMod.val_natCast_of_lt hn, Eig.Ytil, h, show ¬ (1 = 0) from by omega, if_false]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] 
    have h1 := PN_ne β hβ m
    have h2 := rN_ne β hβ m
    rw [PN_succ]
    simp only [rN, bN] at *
    field_simp

theorem locA' (β : ZMod p → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (ζ : ℂ) (hζ : ζ ≠ 0) (w0 : ℂ × ℂ) (k : ℕ) :
    ζ * (Eig.Chat (bN β) ζ w0 (2 * k + 1) / PN β (2 * k + 1)) =
      star (bN β (2 * k + 1)) * (Eig.Ytil (bN β) (rN β) ζ w0 (2 * k + 1) / PN β (2 * k + 1)) +
        rN β (2 * k + 1) * (Eig.Ytil (bN β) (rN β) ζ w0 (2 * k + 2) / PN β (2 * k + 2)) := by
  have h := Eig.localA (bN β) (rN β) ζ w0 hζ (rN_sq β hβ) k
  have e : PN β (2 * k + 2) = PN β (2 * k + 1) * rN β (2 * k + 1) := PN_succ β (2 * k + 1)
  have h1 := PN_ne β hβ (2 * k + 1)
  have h2 := rN_ne β hβ (2 * k + 1)
  rw [e]
  field_simp
  linear_combination h

theorem locB' (β : ZMod p → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (ζ : ℂ) (hζ : ζ ≠ 0) (w0 : ℂ × ℂ) (k : ℕ) :
    ζ * (Eig.Chat (bN β) ζ w0 (2 * k + 2) / PN β (2 * k + 2)) =
      rN β (2 * k + 1) * (Eig.Ytil (bN β) (rN β) ζ w0 (2 * k + 1) / PN β (2 * k + 1)) -
        bN β (2 * k + 1) * (Eig.Ytil (bN β) (rN β) ζ w0 (2 * k + 2) / PN β (2 * k + 2)) := by
  have h := Eig.localB (bN β) (rN β) ζ w0 hζ (rN_sq β hβ) k
  have e : PN β (2 * k + 2) = PN β (2 * k + 1) * rN β (2 * k + 1) := PN_succ β (2 * k + 1)
  have h1 := PN_ne β hβ (2 * k + 1)
  have h2 := rN_ne β hβ (2 * k + 1)
  rw [e]
  field_simp
  linear_combination h

theorem bloch (β : ZMod p → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (ζ : ℂ) (hζ : ζ ≠ 0) (w0 : ℂ × ℂ)
    (L : ℕ) (hL : p = 2 * L) (μ : ℂ)
    (hw : Eig.Wseq (bN β) ζ w0 p = (ζ ^ L * PN β p * μ * w0.1, ζ ^ L * PN β p * μ * w0.2)) :
    Eig.Chat (bN β) ζ w0 p / PN β p = μ * (Eig.Chat (bN β) ζ w0 0 / PN β 0) ∧
    Eig.Ytil (bN β) (rN β) ζ w0 p / PN β p = μ * (Eig.Ytil (bN β) (rN β) ζ w0 0 / PN β 0) := by
  have hP := PN_ne β hβ p
  have h0 : PN β 0 = 1 := by simp [PN]
  have hp2 : p % 2 = 0 := by omega
  have hp3 : p / 2 = L := by omega
  have hp4 : (p + 1) % 2 = 1 := by omega
  have hp5 : (p + 1) / 2 = L := by omega
  have hz : (ζ⁻¹) ^ L * ζ ^ L = 1 := by rw [← mul_pow, inv_mul_cancel₀ hζ, one_pow]
  have hb : bN β p = bN β 0 := by simp [bN, ZMod.natCast_self]
  have hC0 : Eig.Chat (bN β) ζ w0 0 = w0.2 := by simp [Eig.Chat, Eig.Wseq]
  have hC1 : Eig.Chat (bN β) ζ w0 1 = ζ * w0.1 - star (bN β 0) * w0.2 := by
    simp [Eig.Chat, Eig.Wseq]
  have hCp : Eig.Chat (bN β) ζ w0 p = PN β p * μ * w0.2 := by
    unfold Eig.Chat
    rw [hp3, if_pos hp2, hw]
    simp only
    linear_combination (PN β p * μ * w0.2) * hz
  have hCp1 : Eig.Chat (bN β) ζ w0 (p + 1) = PN β p * μ * (ζ * w0.1 - star (bN β 0) * w0.2) := by
    unfold Eig.Chat
    rw [hp5, if_neg (by omega)]
    simp only [Eig.Wseq, hw, hb]
    linear_combination (PN β p * μ * (ζ * w0.1 - star (bN β 0) * w0.2)) * hz
  constructor
  · rw [hCp, hC0, h0]; field_simp
  · unfold Eig.Ytil
    rw [if_pos hp2, if_pos (show 0 % 2 = 0 from rfl), hCp, hCp1, hC0, hC1, hb, h0]
    field_simp

theorem eig_main (hp : p % 2 = 0) (β : ZMod p → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (ζ : ℂ) (hζ : ζ ≠ 0)
    (w0 : ℂ × ℂ) (L : ℕ) (hL : p = 2 * L) (μ b : ℂ) (hbm : b * μ = 1)
    (hw : Eig.Wseq (bN β) ζ w0 p = (ζ ^ L * PN β p * μ * w0.1, ζ ^ L * PN β p * μ * w0.2))
    (n : ℕ) (hn : n < p) :
    (cmvOdd38 β b *ᵥ yV β ζ w0) (n : ZMod p) = ζ * chiV β ζ w0 (n : ZMod p) := by
  have hchi : ∀ m, m < p → chiV β ζ w0 (m : ZMod p) = Eig.Chat (bN β) ζ w0 m / PN β m := by
    intro m hm; simp [chiV, ZMod.val_natCast_of_lt hm]
  obtain ⟨hb1, hb2⟩ := bloch β hβ ζ hζ w0 L hL μ hw
  have hbinv : b⁻¹ = μ := by
    have hb0 : b ≠ 0 := by intro h; rw [h] at hbm; simp at hbm
    field_simp; linear_combination -hbm
  rw [hchi n hn]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · by_cases hn0 : n = 0
    · subst hn0
      rw [Oy_zero hp β b ζ w0 (by omega)]
      have hB := locB' β hβ ζ hζ w0 (L - 1)
      have e1 : 2 * (L - 1) + 2 = p := by omega
      have e2 : 2 * (L - 1) + 1 = p - 1 := by omega
      rw [e1, e2, hb1, hb2] at hB
      simp only [rN, bN] at hB
      simp only [PN, Finset.range_zero, Finset.prod_empty] at hB ⊢
      linear_combination (-b) * hB + (ζ * (Eig.Chat (bN β) ζ w0 0 / 1) +
        β ((p - 1 : ℕ) : ZMod p) * (Eig.Ytil (bN β) (rN β) ζ w0 0 / 1)) * hbm
    · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 2 := ⟨n / 2 - 1, by omega⟩
      subst hk
      rw [Oy_even_pos hp β b ζ w0 (2 * k + 2) hn h hn0]
      have hB := locB' β hβ ζ hζ w0 k
      have e : 2 * k + 2 - 1 = 2 * k + 1 := by omega
      rw [e]
      simpa only [rN, bN] using hB.symm
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    subst hk
    by_cases hlt : 2 * k + 1 + 1 < p
    · rw [Oy_odd_lt hp β b ζ w0 (2 * k + 1) hlt h]
      have hA := locA' β hβ ζ hζ w0 k
      simpa only [rN, bN] using hA.symm
    · rw [Oy_odd_wrap hp β b ζ w0 (2 * k + 1) hn hlt h]
      have hA := locA' β hβ ζ hζ w0 k
      have e : 2 * k + 2 = p := by omega
      rw [e, hb2] at hA
      simp only [rN, bN] at hA
      rw [hbinv]
      simp only [PN, Finset.range_zero, Finset.prod_empty] at hA ⊢
      linear_combination -hA

theorem kernel_exists (hp : p % 2 = 0) (β : ZMod p → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (ζ : ℂ) (hζ : ζ ≠ 0)
    (w0 : ℂ × ℂ) (hw0 : w0 ≠ 0) (L : ℕ) (hL : p = 2 * L) (hp2 : 2 ≤ p) (μ b : ℂ) (hbm : b * μ = 1)
    (hw : Eig.Wseq (bN β) ζ w0 p = (ζ ^ L * PN β p * μ * w0.1, ζ ^ L * PN β p * μ * w0.2)) :
    ∃ y : ZMod p → ℂ, y ≠ 0 ∧ (Nmat β ζ b) *ᵥ y = 0 := by
  have hp0 : 0 < p := by omega
  have hE : (cmvEven38 β)ᴴ * cmvEven38 β = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 (cmv_even_mem hp β hβ)
    simpa [Matrix.star_eq_conjTranspose] using this
  have hEc : cmvEven38 β *ᵥ chiV β ζ w0 = yV β ζ w0 := by
    funext i
    have hi : i = ((i.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val i).symm
    rw [hi]
    exact Ey_eq hp β hβ ζ w0 i.val (ZMod.val_lt i)
  have hOc : cmvOdd38 β b *ᵥ yV β ζ w0 = ζ • chiV β ζ w0 := by
    funext i
    have hi : i = ((i.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val i).symm
    rw [hi]
    simpa using eig_main hp β hβ ζ hζ w0 L hL μ b hbm hw i.val (ZMod.val_lt i)
  have hEy : (cmvEven38 β)ᴴ *ᵥ yV β ζ w0 = chiV β ζ w0 := by
    rw [← hEc, Matrix.mulVec_mulVec, hE, Matrix.one_mulVec]
  refine ⟨yV β ζ w0, ?_, ?_⟩
  · intro h0
    have hc0 : chiV β ζ w0 = 0 := by rw [← hEy, h0, Matrix.mulVec_zero]
    have c0 := congrFun hc0 ((0 : ℕ) : ZMod p)
    have c1 := congrFun hc0 ((1 : ℕ) : ZMod p)
    have hp1 : 1 < p := by omega
    simp only [chiV, ZMod.val_natCast_of_lt hp0, ZMod.val_natCast_of_lt hp1, Pi.zero_apply] at c0 c1
    have h2 : w0.2 = 0 := by simpa [Eig.Chat, Eig.Wseq, PN] using c0
    have hr := rN_ne β hβ 0
    have h1 : ζ * w0.1 = 0 := by
      have : (Eig.Chat (bN β) ζ w0 1) = 0 := by
        have := c1
        rw [div_eq_zero_iff] at this
        rcases this with h | h
        · exact h
        · exfalso; exact PN_ne β hβ 1 h
      simp [Eig.Chat, Eig.Wseq, h2] at this
      simpa [this] using this
    have h3 : w0.1 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hζ
      · exact h
    exact hw0 (Prod.ext h3 h2)
  · unfold Nmat
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hEy, hOc, sub_self]

end Vec

section Fform
variable {p : ℕ} [NeZero p]

theorem prodU (β : ZMod p → ℂ) (ζ : ℂ) (m : ℕ) :
    ∏ i ∈ Finset.range (2 * m + 1), useq β ζ i =
      (-ζ) ^ (m + 1) * ∏ i ∈ Finset.range (2 * m + 1), rN β i := by
  induction m with
  | zero => simp [useq, rN]
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by ring
    have ku : ∏ i ∈ Finset.range ((2 * m + 1) + 1 + 1), useq β ζ i =
        (∏ i ∈ Finset.range (2 * m + 1), useq β ζ i) * useq β ζ (2 * m + 1) * useq β ζ (2 * m + 1 + 1) := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have kr : ∏ i ∈ Finset.range ((2 * m + 1) + 1 + 1), rN β i =
        (∏ i ∈ Finset.range (2 * m + 1), rN β i) * rN β (2 * m + 1) * rN β (2 * m + 1 + 1) := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
    rw [e, ku, kr, ih]
    have h1 : (2 * m + 1) % 2 = 1 := by omega
    have h2 : (2 * m + 1 + 1) % 2 = 0 := by omega
    simp only [useq, rN, h1, h2, if_false, if_true, show ¬ (1 = 0) from by omega]
    ring

def Aval (L : ℕ) [NeZero L] (β : ZMod (2 * L) → ℂ) (ζ : ℂ) : ℂ :=
  (-1) ^ L * (Tridiag.cont (dseq β ζ) (useq β ζ) (useq β ζ) (2 * L) 0 -
    rN β (2 * L - 1) * rN β (2 * L - 1) *
      Tridiag.cont (dseq β ζ) (useq β ζ) (useq β ζ) (2 * L - 2) 1)

theorem Fform_ge2 (L : ℕ) [NeZero L] (hL : 2 ≤ L) (β : ZMod (2 * L) → ℂ) (hβ : ∀ j, ‖β j‖ < 1)
    (ζ b : ℂ) (hb : b ≠ 0) :
    (ζ • (1 : Matrix (ZMod (2 * L)) (ZMod (2 * L)) ℂ) - floquetCMV38 β b).det =
      Aval L β ζ - ζ ^ L * PN β (2 * L) * (b + b⁻¹) := by
  rw [det_floquet_eq L hL β hβ ζ b, Tridiag.det_cyc_ge3 _ _ _ _ _ (2 * L) (by omega)]
  have hm : 2 * L - 1 = 2 * (L - 1) + 1 := by omega
  have hP : ∏ i ∈ Finset.range (2 * L - 1), useq β ζ i =
      (-ζ) ^ L * ∏ i ∈ Finset.range (2 * L - 1), rN β i := by
    rw [hm, prodU β ζ (L - 1)]
    have : L - 1 + 1 = L := by omega
    rw [this]
  have hPN : PN β (2 * L) = (∏ i ∈ Finset.range (2 * L - 1), rN β i) * rN β (2 * L - 1) := by
    have h := PN_succ β (2 * L - 1)
    rw [show 2 * L - 1 + 1 = 2 * L from by omega] at h
    exact h
  have hodd : (-1 : ℂ) ^ (2 * L - 3) = -1 := by
    have : Odd (2 * L - 3) := ⟨L - 2, by omega⟩
    exact this.neg_one_pow
  have hr : ∀ x : ℂ, (cmvRho38 (β ((2 * L - 1 : ℕ) : ZMod (2 * L))) : ℂ) * x = rN β (2 * L - 1) * x := fun x => rfl
  simp only [hr, hP, hodd, Aval]
  have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  rw [hPN]
  have hsq : (-ζ) ^ L = (-1) ^ L * ζ ^ L := by rw [neg_eq_neg_one_mul, mul_pow]
  have hone : ((-1 : ℂ) ^ L) * (-1) ^ L = 1 := by rw [← mul_pow]; simp
  rw [hsq]
  linear_combination (-(Tridiag.cont (dseq β ζ) (useq β ζ) (useq β ζ) (2 * L - 2) 1) * (-1) ^ L * rN β (2 * L - 1) * rN β (2 * L - 1)) * hbb
    + (-(ζ ^ L * (∏ i ∈ Finset.range (2 * L - 1), rN β i) * rN β (2 * L - 1) * (b + b⁻¹))) * hone

theorem Fform_one (β : ZMod 2 → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (ζ b : ℂ) (hb : b ≠ 0) :
    (ζ • (1 : Matrix (ZMod 2) (ZMod 2) ℂ) - floquetCMV38 β b).det =
      (-1) ^ 1 * (Tridiag.cont (dseq β ζ) (useq β ζ) (useq β ζ) 2 0 -
        rN β 1 * rN β 1 * Tridiag.cont (dseq β ζ) (useq β ζ) (useq β ζ) 0 1) -
      ζ ^ 1 * PN β 2 * (b + b⁻¹) := by
  rw [det_floquet_two β hβ ζ b, Tridiag.det_cyc2]
  have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  have hPN : PN β 2 = rN β 0 * rN β 1 := by simp [PN, Finset.prod_range_succ]
  have hu : useq β ζ 0 = -ζ * rN β 0 := by simp [useq, rN]
  have hr : (cmvRho38 (β ((2 - 1 : ℕ) : ZMod 2)) : ℂ) = rN β 1 := rfl
  rw [hPN, hr, hu]
  simp only [Tridiag.cont]
  linear_combination (rN β 1 * rN β 1) * hbb

theorem Fform (L : ℕ) [NeZero L] (hL : 1 ≤ L) (β : ZMod (2 * L) → ℂ) (hβ : ∀ j, ‖β j‖ < 1)
    (ζ b : ℂ) (hb : b ≠ 0) :
    (ζ • (1 : Matrix (ZMod (2 * L)) (ZMod (2 * L)) ℂ) - floquetCMV38 β b).det =
      Aval L β ζ - ζ ^ L * PN β (2 * L) * (b + b⁻¹) := by
  rcases Nat.lt_or_ge L 2 with h | h
  · obtain rfl : L = 1 := by omega
    exact Fform_one β hβ ζ b hb
  · exact Fform_ge2 L h β hβ ζ b hb

theorem det_floquet_Nmat (L : ℕ) [NeZero L] (β : ZMod (2 * L) → ℂ) (hβ : ∀ j, ‖β j‖ < 1) (ζ b : ℂ) :
    (ζ • (1 : Matrix (ZMod (2 * L)) (ZMod (2 * L)) ℂ) - floquetCMV38 β b).det =
      (-1) ^ L * (Nmat β ζ b).det := by
  have hp : (2 * L) % 2 = 0 := by omega
  have hE : cmvEven38 β * (cmvEven38 β)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 (cmv_even_mem hp β hβ)
    simpa [Matrix.star_eq_conjTranspose] using this
  have hfac : ζ • (1 : Matrix (ZMod (2 * L)) (ZMod (2 * L)) ℂ) - floquetCMV38 β b =
      cmvEven38 β * (ζ • (cmvEven38 β)ᴴ - cmvOdd38 β b) := by
    unfold floquetCMV38
    rw [Matrix.mul_sub, Matrix.mul_smul, hE]
  rw [hfac, Matrix.det_mul, det_even L β hβ]
  have hneg : ζ • (cmvEven38 β)ᴴ - cmvOdd38 β b = -(Nmat β ζ b) := by
    unfold Nmat; rw [neg_sub]
  rw [hneg, Matrix.det_neg, ZMod.card]
  have : ((-1 : ℂ) ^ (2 * L)) = 1 := by rw [pow_mul]; simp
  rw [this, one_mul]

def Tm (L : ℕ) [NeZero L] (β : ZMod (2 * L) → ℂ) (ζ : ℂ) : ℂ :=
  (Eig.W1 (bN β) ζ (2 * L)).1 + (Eig.W2 (bN β) ζ (2 * L)).2

theorem crux_det (L : ℕ) [NeZero L] (hL : 1 ≤ L) (β : ZMod (2 * L) → ℂ) (hβ : ∀ j, ‖β j‖ < 1)
    (ζ : ℂ) (hζ : ζ ≠ 0) (b : ℂ) (hb : b ≠ 0) :
    (ζ • (1 : Matrix (ZMod (2 * L)) (ZMod (2 * L)) ℂ) - floquetCMV38 β b).det =
      Tm L β ζ - ζ ^ L * PN β (2 * L) * (b + b⁻¹) := by
  have hp2 : 2 ≤ 2 * L := by omega
  have hc : ζ ^ L * PN β (2 * L) ≠ 0 := mul_ne_zero (pow_ne_zero _ hζ) (PN_ne β hβ (2 * L))
  have hdet : (Eig.W1 (bN β) ζ (2 * L)).1 * (Eig.W2 (bN β) ζ (2 * L)).2 -
      (Eig.W2 (bN β) ζ (2 * L)).1 * (Eig.W1 (bN β) ζ (2 * L)).2 =
        (ζ ^ L * PN β (2 * L)) * (ζ ^ L * PN β (2 * L)) := by
    rw [Eig.det_W, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have h1 : PN β (2 * L) * PN β (2 * L) =
        ∏ j ∈ Finset.range (2 * L), (1 - bN β j * star (bN β j)) := by
      unfold PN
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun j _ => rN_sq β hβ j)
    have e : ζ ^ (2 * L) = ζ ^ L * ζ ^ L := by rw [two_mul, pow_add]
    rw [e, ← h1]
    ring
  obtain ⟨μ, hμ0, hμT, w0, hw0, hw⟩ :=
    Eig.exists_eig (bN β) ζ (ζ ^ L * PN β (2 * L)) hc (2 * L) hdet
  have hbm : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ0
  obtain ⟨y, hy0, hy⟩ := kernel_exists (p := 2 * L) (by omega) β hβ ζ hζ w0 hw0 L rfl hp2 μ μ⁻¹ hbm hw
  have hNd : (Nmat β ζ μ⁻¹).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨y, hy0, hy⟩
  have h0 := Fform L hL β hβ ζ μ⁻¹ (inv_ne_zero hμ0)
  rw [det_floquet_Nmat L β hβ ζ μ⁻¹, hNd, mul_zero] at h0
  have hA : Aval L β ζ = Tm L β ζ := by
    have e : μ⁻¹ + μ⁻¹⁻¹ = (Tm L β ζ) / (ζ ^ L * PN β (2 * L)) := by
      rw [inv_inv, add_comm]; exact hμT
    rw [e] at h0
    have hmul : ζ ^ L * PN β (2 * L) * (Tm L β ζ / (ζ ^ L * PN β (2 * L))) = Tm L β ζ := by
      rw [← mul_div_assoc]; exact mul_div_cancel_left₀ _ hc
    linear_combination -h0 + hmul
  rw [Fform L hL β hβ ζ b hb, hA]

end Fform
end AL007Aux

namespace AL007Aux
section R4
variable {p : ℕ} [NeZero p]

theorem opucPartial_eq_pi (β : ZMod p → ℂ) (ζ : ℂ) (n : ℕ) :
    opucPartial β ζ n = (PN β n)⁻¹ •
      (!![(Eig.W1 (bN β) ζ n).1, (Eig.W2 (bN β) ζ n).1;
          (Eig.W1 (bN β) ζ n).2, (Eig.W2 (bN β) ζ n).2] : Matrix (Fin 2) (Fin 2) ℂ) := by
  induction n with
  | zero =>
    have h0 : PN β 0 = 1 := by simp [PN]
    rw [h0]
    ext i j; fin_cases i <;> fin_cases j <;> simp [opucPartial, Eig.W1, Eig.W2, Eig.Wseq]
  | succ n ih =>
    rw [opucPartial, ih, PN_succ, mul_inv, opucTransfer]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Eig.W1, Eig.W2, Eig.Wseq, bN, rN] <;> ring

theorem trace_opuc (L : ℕ) [NeZero L] (β : ZMod (2 * L) → ℂ) (ζ : ℂ) :
    (opucMonodromy β ζ).trace = (PN β (2 * L))⁻¹ * Tm L β ζ := by
  unfold opucMonodromy Tm
  rw [opucPartial_eq_pi, Matrix.trace_smul, Matrix.trace_fin_two]
  simp

theorem prod_rho (L : ℕ) [NeZero L] (β : ZMod (2 * L) → ℂ) :
    ∏ j : ZMod (2 * L), (cmvRho38 (β j) : ℂ) = PN β (2 * L) := by
  rw [← Equiv.prod_comp (finZMod (2 * L)) (fun j : ZMod (2 * L) => (cmvRho38 (β j) : ℂ))]
  have h := Fin.prod_univ_eq_prod_range (fun i => rN β i) (2 * L)
  unfold PN
  rw [← h]
  rfl

end R4
end AL007Aux

open AL007Aux in
theorem hdet_clause (L : ℕ) [NeZero L] (α : ZMod L → ℂ) (hα : IsALField38 α) (z : ℂ) (hz : z ≠ 0)
    (b : ℂ) (hb : b ≠ 0) :
    ((z ^ 2) • (1 : Matrix (ZMod (2 * L)) (ZMod (2 * L)) ℂ) -
      floquetCMV38 (doubledCmvCoefficients α) b).det =
        (∏ j : ZMod (2 * L), (cmvRho38 (doubledCmvCoefficients α j) : ℂ)) * (z ^ 2) ^ L *
          (((alMonodromy38 α z) ^ 2).trace - (b + b⁻¹)) := by
  obtain ⟨h1, h2, h3⟩ := al007_leaves1 α hα z hz
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  rw [crux_det L hL (doubledCmvCoefficients α) h2 (z ^ 2) hz2 b hb, prod_rho]
  have htr := congrArg Matrix.trace h3
  have hD : (!![z, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![z⁻¹, 0; 0, 1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hz]
  have hconj : (Matrix.trace ((!![z⁻¹, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) *
      (alMonodromy38 α z) ^ 2 * !![z, 0; 0, 1])) = ((alMonodromy38 α z) ^ 2).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hD, Matrix.one_mul]
  rw [Matrix.trace_smul, hconj, trace_opuc L (doubledCmvCoefficients α) (z ^ 2)] at htr
  have hPN := PN_ne (doubledCmvCoefficients α) h2 (2 * L)
  have hzz : (z⁻¹) ^ (2 * L) * (z ^ 2) ^ L = 1 := by
    rw [← pow_mul, ← mul_pow, inv_mul_cancel₀ hz, one_pow]
  have hT : Tm L (doubledCmvCoefficients α) (z ^ 2) =
      PN (doubledCmvCoefficients α) (2 * L) * (z ^ 2) ^ L * ((alMonodromy38 α z) ^ 2).trace := by
    simp only [smul_eq_mul] at htr
    have hinv : PN (doubledCmvCoefficients α) (2 * L) * (PN (doubledCmvCoefficients α) (2 * L))⁻¹ = 1 :=
      mul_inv_cancel₀ hPN
    linear_combination (PN (doubledCmvCoefficients α) (2 * L) * (z ^ 2) ^ L) * htr
      + (-(Tm L (doubledCmvCoefficients α) (z ^ 2) * ((z⁻¹) ^ (2 * L) * (z ^ 2) ^ L))) * hinv
      + (-(Tm L (doubledCmvCoefficients α) (z ^ 2))) * hzz
  rw [hT]
  ring


theorem al007 {L : ℕ} [NeZero L] (hodd : Odd L)
    (α : ZMod L → ℂ) (hα : IsALField38 α) (z : ℂ) (hz : z ≠ 0) :
  let D : Matrix (Fin 2) (Fin 2) ℂ := !![z,0;0,1]
  let Dinv : Matrix (Fin 2) (Fin 2) ℂ := !![z⁻¹,0;0,1]
  let β := doubledCmvCoefficients α
  (∀ j : ZMod L,
    alTransfer38 (α j) z =
      D * (z⁻¹ • opucTransfer (-star (α j)) (z^2)) * Dinv) ∧
  IsALField38 β ∧
  (z⁻¹)^(2*L) • opucMonodromy β (z^2) =
    Dinv * (alMonodromy38 α z)^2 * D ∧
  (∀ b : ℂ, b ≠ 0 →
    ((z^2) • (1 : Matrix (ZMod (2*L)) (ZMod (2*L)) ℂ) -
      floquetCMV38 β b).det =
        (∏ j : ZMod (2*L), (cmvRho38 (β j) : ℂ)) * (z^2)^L *
          (((alMonodromy38 α z)^2).trace - (b+b⁻¹))) ∧
  (∀ (w : ℂ) (u : Fin 2 → ℂ), ‖w‖ = 1 → u ≠ 0 →
    (alMonodromy38 α z).mulVec u = w • u →
      ‖w^2‖ = 1 ∧ ∃ v : EuclideanSpace ℂ (ZMod (2*L)),
        v ≠ 0 ∧ Matrix.toEuclideanLin (floquetCMV38 β (w^2)) v = (z^2) • v) :=
  al007_of_det hodd α hα z hz (fun b hb => hdet_clause L α hα z hz b hb)


end NlsGge.ThirdConsultation.AL
