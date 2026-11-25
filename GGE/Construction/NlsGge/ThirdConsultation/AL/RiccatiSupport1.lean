import Mathlib
import NlsGge.ThirdConsultation.AL.Basic
import NlsGge.Hierarchy.ALExteriorBranch38

                                                                                                     
                                                                                                         
set_option autoImplicit false
open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory Metric
open NlsGge.AblowitzLadik
namespace NlsGge.ThirdConsultation.AL
noncomputable section

theorem al013s_step {a ζ q : ℂ} (ha : ‖a‖ < 1) (hζ : ‖ζ‖ < 1) (h0 : ζ ≠ 0) (hq : ‖q‖ < 1) :
    1 + ζ * a * q ≠ 0 ∧
    (alTransfer38 a ζ⁻¹).mulVec ![1, q] =
      ((((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ))⁻¹ * (ζ⁻¹ + a * q)) •
        ![1, (ζ * star a + ζ ^ 2 * q) / (1 + ζ * a * q)] ∧
    ‖(ζ * star a + ζ ^ 2 * q) / (1 + ζ * a * q)‖ < 1 := by
  have hden : 1 + ζ * a * q ≠ 0 := by
    intro h
    have h1 : ζ * a * q = -1 := by linear_combination h
    have h2 : ‖ζ‖ * ‖a‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg ζ) hζ ha.le
    have h3 : ‖ζ‖ * ‖a‖ * ‖q‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_left
      (mul_nonneg (norm_nonneg ζ) (norm_nonneg a)) h2 hq.le
    have h4 : ‖ζ * a * q‖ < 1 := by rw [norm_mul, norm_mul]; exact h3
    rw [h1] at h4; simp at h4
  have hr : 0 < Real.sqrt (1 - ‖a‖ ^ 2) := Real.sqrt_pos.2 (by nlinarith [norm_nonneg a])
  have hrC : ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have heq : (alTransfer38 a ζ⁻¹).mulVec ![1, q] =
      ((((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ))⁻¹ * (ζ⁻¹ + a * q)) •
        ![1, (ζ * star a + ζ ^ 2 * q) / (1 + ζ * a * q)] := by
    unfold alTransfer38
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · have hden' : 1 + ζ * q * a ≠ 0 := by
        rw [show ζ * q * a = ζ * a * q by ring]; exact hden
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp [hden']
      try ring
  refine ⟨hden, heq, ?_⟩
  have hz : 1 < ‖ζ⁻¹‖ := by
    rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.2 h0)).2 hζ
  have hv : (![1, q] : Fin 2 → ℂ) ≠ 0 := fun h => by have := congrFun h 0; simp at this
  have hJ := alJForm_transfer_gt38 a ζ⁻¹ ha hz _ hv
  rw [heq, alJForm_smul38] at hJ
  generalize (ζ * star a + ζ ^ 2 * q) / (1 + ζ * a * q) = q' at hJ ⊢
  generalize ‖((((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ))⁻¹ * (ζ⁻¹ + a * q))‖ = n at hJ
  have hJ0 : alJForm38 ![1, q] = 1 - ‖q‖ ^ 2 := by simp [alJForm38]
  have hJ1 : alJForm38 ![1, q'] = 1 - ‖q'‖ ^ 2 := by simp [alJForm38]
  rw [hJ0, hJ1] at hJ
  have hq2 : 0 < 1 - ‖q‖ ^ 2 := by nlinarith [norm_nonneg q]
  by_contra hcon
  push Not at hcon
  have h5 : 1 - ‖q'‖ ^ 2 ≤ 0 := by nlinarith
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg n) h5]

theorem al013s_orbit {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ‖ζ‖ < 1) (h0 : ζ ≠ 0) {q : ZMod L → ℂ} (hq : ∀ j, ‖q j‖ < 1)
    (hrec : ∀ j, q (j + 1) = (ζ * star (α j) + ζ ^ 2 * q j) / (1 + ζ * α j * q j)) (k : ℕ) :
    (alPartial38 α ζ⁻¹ k).mulVec ![1, q 0] =
      (∏ i ∈ Finset.range k, ((((Real.sqrt (1 - ‖α (i : ZMod L)‖ ^ 2) : ℝ) : ℂ))⁻¹ *
        (ζ⁻¹ + α (i : ZMod L) * q (i : ZMod L)))) • ![1, q (k : ZMod L)] := by
  induction k with
  | zero => simp [alPartial38]
  | succ k ih =>
    obtain ⟨-, hstep, -⟩ := al013s_step (hα (k : ZMod L)) hζ h0 (hq (k : ZMod L))
    have hk : ((k + 1 : ℕ) : ZMod L) = (k : ZMod L) + 1 := by push_cast; ring
    rw [alPartial38_mulVec_succ, ih, Matrix.mulVec_smul, hstep, Finset.prod_range_succ,
      smul_smul, hk, hrec]

theorem al013s_zero_sol {L : ℕ} [NeZero L] {α : ZMod L → ℂ} {q : ZMod L → ℂ}
    (hrec : ∀ j, q (j + 1) = ((0 : ℂ) * star (α j) + (0 : ℂ) ^ 2 * q j) /
      (1 + (0 : ℂ) * α j * q j)) : q = 0 := by
  funext j
  have := hrec (j - 1)
  rw [sub_add_cancel] at this
  simpa using this

theorem al013s_charpoly (M : Matrix (Fin 2) (Fin 2) ℂ) (hdet : M.det = 1) (c : ℂ)
    (u : Fin 2 → ℂ) (hu : u ≠ 0) (h : M.mulVec u = c • u) :
    c ^ 2 - M.trace * c + 1 = 0 := by
  have h1 : (M - c • (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec u = 0 := by
    rw [Matrix.sub_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have h2 : (M - c • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨u, hu, h1⟩
  rw [Matrix.det_fin_two] at h2 hdet
  rw [Matrix.trace_fin_two]
  simp at h2
  linear_combination h2 - hdet

theorem al013s_eigenvalue_eq {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) (h0 : ζ ≠ 0) {c : ℂ} {u : Fin 2 → ℂ} (hu : u ≠ 0)
    (hJ : 0 < alJForm38 u) (h : (alMonodromy38 α ζ⁻¹).mulVec u = c • u) :
    c = alExtW38 α ζ := by
  have hn : ‖ζ‖ < 1 := by simpa using hζ
  have hz : 1 < ‖ζ⁻¹‖ := by
    rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.2 h0)).2 hn
  have hdet := det_alMonodromy38 hα (inv_ne_zero h0)
  have hc := al013s_charpoly _ hdet c u hu h
  have hw := alExtW38_root hα hζ h0
  have hw1 : 1 < ‖alExtW38 α ζ‖ := (alExteriorG38_multiplier hα hζ h0).2.2
  have hc1 : 1 < ‖c‖ := by
    have := alJForm_eigen_gt38 α hα ζ⁻¹ hz c u hu h
    by_contra hcon; push Not at hcon
    have h2 : ‖c‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg c]
    nlinarith [mul_le_mul_of_nonneg_right h2 hJ.le]
  set w := alExtW38 α ζ
  set tr := Matrix.trace (alMonodromy38 α ζ⁻¹)
  have hprod : (c - w) * (c + w - tr) = 0 := by linear_combination hc - hw
  rcases mul_eq_zero.1 hprod with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have htr : tr = c + w := by linear_combination -h1
    rw [htr] at hw
    have hcw : c * w = 1 := by linear_combination -hw
    have : ‖c‖ * ‖w‖ = 1 := by rw [← norm_mul, hcw, norm_one]
    nlinarith

theorem al013s_eigen_unique {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {z w : ℂ}
    (hz : 1 < ‖z‖) (hw : 1 < ‖w‖) {q q' : ℂ}
    (h : (alMonodromy38 α z).mulVec ![1, q] = w • ![1, q])
    (h' : (alMonodromy38 α z).mulVec ![1, q'] = w • ![1, q']) : q = q' := by
  by_contra hne
  have hd : (![1, q'] : Fin 2 → ℂ) - ![1, q] = ![0, q' - q] := by
    ext i; fin_cases i <;> simp
  have h'' : (alMonodromy38 α z).mulVec (![0, q' - q] : Fin 2 → ℂ) =
      w • (![0, q' - q] : Fin 2 → ℂ) := by
    rw [← hd, Matrix.mulVec_sub, h, h', smul_sub]
  have hv : (![0, q' - q] : Fin 2 → ℂ) ≠ 0 := by
    intro h0; have := congrFun h0 1; simp at this; exact hne (sub_eq_zero.1 this).symm
  have := alJForm_pos_of_one_lt_norm38 α hα z hz w _ hv h'' hw
  have h1 : 0 < ‖q' - q‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  simp [alJForm38] at this
  nlinarith

theorem al013s_unique {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) {q q' : ZMod L → ℂ}
    (hq : ∀ j, ‖q j‖ < 1)
    (hrec : ∀ j, q (j + 1) = (ζ * star (α j) + ζ ^ 2 * q j) / (1 + ζ * α j * q j))
    (hq' : ∀ j, ‖q' j‖ < 1)
    (hrec' : ∀ j, q' (j + 1) = (ζ * star (α j) + ζ ^ 2 * q' j) / (1 + ζ * α j * q' j)) :
    q = q' := by
  by_cases h0 : ζ = 0
  · subst h0
    rw [al013s_zero_sol hrec, al013s_zero_sol hrec']
  have hn : ‖ζ‖ < 1 := by simpa using hζ
  have hz : 1 < ‖ζ⁻¹‖ := by
    rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.2 h0)).2 hn
  have eig : ∀ p : ZMod L → ℂ, (∀ j, ‖p j‖ < 1) →
      (∀ j, p (j + 1) = (ζ * star (α j) + ζ ^ 2 * p j) / (1 + ζ * α j * p j)) →
      (alMonodromy38 α ζ⁻¹).mulVec ![1, p 0] = alExtW38 α ζ • ![1, p 0] := by
    intro p hp hrp
    have horb := al013s_orbit hα hn h0 hp hrp L
    rw [ZMod.natCast_self] at horb
    have hu : (![1, p 0] : Fin 2 → ℂ) ≠ 0 := fun h => by have := congrFun h 0; simp at this
    have hJ : 0 < alJForm38 ![1, p 0] := by
      simp [alJForm38]; nlinarith [norm_nonneg (p 0), hp 0]
    have hceq := al013s_eigenvalue_eq hα hζ h0 hu hJ horb
    rw [← hceq]; exact horb
  have hw1 : 1 < ‖alExtW38 α ζ‖ := (alExteriorG38_multiplier hα hζ h0).2.2
  have h00 : q 0 = q' 0 :=
    al013s_eigen_unique hα hz hw1 (eig q hq hrec) (eig q' hq' hrec')
  have hall : ∀ k : ℕ, q (k : ZMod L) = q' (k : ZMod L) := by
    intro k
    induction k with
    | zero => simpa using h00
    | succ k ih =>
      have hk : ((k + 1 : ℕ) : ZMod L) = (k : ZMod L) + 1 := by push_cast; ring
      rw [hk, hrec, hrec', ih]
  funext j
  have := hall j.val
  rwa [ZMod.natCast_zmod_val] at this

theorem al013s_partial_add {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) (k : ℕ) :
    alPartial38 α z (k + L) = alPartial38 α z k * alMonodromy38 α z := by
  induction k with
  | zero => simp [alPartial38, alMonodromy38]
  | succ k ih =>
    have e : k + 1 + L = (k + L) + 1 := by ring
    have hc : ((k + L : ℕ) : ZMod L) = (k : ZMod L) := by
      simp [Nat.cast_add, ZMod.natCast_self]
    rw [e, alPartial38, hc, ih, alPartial38, Matrix.mul_assoc]

theorem al013s_exists {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) (h0 : ζ ≠ 0) :
    ∃ q : ZMod L → ℂ, (∀ j, ‖q j‖ < 1) ∧
      (∀ j, q (j + 1) = (ζ * star (α j) + ζ ^ 2 * q j) / (1 + ζ * α j * q j)) ∧
      (alMonodromy38 α ζ⁻¹).mulVec ![1, q 0] = alExtW38 α ζ • ![1, q 0] := by
  have hn : ‖ζ‖ < 1 := by simpa using hζ
  have hz : 1 < ‖ζ⁻¹‖ := by
    rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.2 h0)).2 hn
  obtain ⟨v, hv, hev⟩ := alExtW38_eigen hα hζ h0
  have hw1 : 1 < ‖alExtW38 α ζ‖ := (alExteriorG38_multiplier hα hζ h0).2.2
  have hw0 : alExtW38 α ζ ≠ 0 := norm_pos_iff.1 (by linarith)
  have hJv : 0 < alJForm38 v := alJForm_pos_of_one_lt_norm38 α hα ζ⁻¹ hz _ v hv hev hw1
  set V : ℕ → Fin 2 → ℂ := fun k => (alPartial38 α ζ⁻¹ k).mulVec v with hV
  have hVJ : ∀ k, 0 < alJForm38 (V k) := fun k =>
    lt_of_lt_of_le hJv (alPartial38_ne_zero_ge α hα ζ⁻¹ hz v hv k).2
  have hV0 : ∀ k, V k 0 ≠ 0 := by
    intro k h
    have := hVJ k
    unfold alJForm38 at this
    rw [h, norm_zero] at this
    nlinarith [sq_nonneg ‖V k 1‖]
  have hVn : ∀ k, ‖V k 1 / V k 0‖ < 1 := by
    intro k
    rw [norm_div, div_lt_one (norm_pos_iff.2 (hV0 k))]
    have := hVJ k
    unfold alJForm38 at this
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul hc hc (norm_nonneg _) (norm_nonneg _)]
  set Q : ℕ → ℂ := fun k => V k 1 / V k 0 with hQ
  have hVQ : ∀ k, V k = V k 0 • ![1, Q k] := by
    intro k
    ext i
    fin_cases i
    · simp
    · show V k 1 = V k 0 * (V k 1 / V k 0)
      rw [mul_div_assoc', mul_div_cancel_left₀ _ (hV0 k)]
  have hstep : ∀ k : ℕ, Q (k + 1) =
      (ζ * star (α (k : ZMod L)) + ζ ^ 2 * Q k) / (1 + ζ * α (k : ZMod L) * Q k) := by
    intro k
    obtain ⟨-, hstep, -⟩ := al013s_step (hα (k : ZMod L)) hn h0 (hVn k)
    have hs : V (k + 1) = (V k 0 * ((((Real.sqrt (1 - ‖α (k : ZMod L)‖ ^ 2) : ℝ) : ℂ))⁻¹ *
        (ζ⁻¹ + α (k : ZMod L) * Q k))) •
        ![1, (ζ * star (α (k : ZMod L)) + ζ ^ 2 * Q k) / (1 + ζ * α (k : ZMod L) * Q k)] := by
      have e1 : V (k + 1) = (alTransfer38 (α (k : ZMod L)) ζ⁻¹).mulVec (V k) :=
        alPartial38_mulVec_succ α ζ⁻¹ k v
      rw [e1, congrArg (fun x => (alTransfer38 (α (k : ZMod L)) ζ⁻¹).mulVec x) (hVQ k),
        Matrix.mulVec_smul, hstep, smul_smul]
    have hne := hV0 (k + 1)
    generalize V k 0 * ((((Real.sqrt (1 - ‖α (k : ZMod L)‖ ^ 2) : ℝ) : ℂ))⁻¹ *
        (ζ⁻¹ + α (k : ZMod L) * Q k)) = c at hs
    generalize (ζ * star (α (k : ZMod L)) + ζ ^ 2 * Q k) / (1 + ζ * α (k : ZMod L) * Q k) = q'
      at hs ⊢
    rw [hs] at hne
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at hne
    show V (k + 1) 1 / V (k + 1) 0 = q'
    rw [hs]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, mul_one]
    field_simp
  have hper : ∀ k, Q (k + L) = Q k := by
    intro k
    have hVk : V (k + L) = alExtW38 α ζ • V k := by
      simp only [hV]
      rw [al013s_partial_add, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul]
    show V (k + L) 1 / V (k + L) 0 = V k 1 / V k 0
    rw [hVk]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_div_mul_left _ _ hw0
  have hmod : ∀ n k : ℕ, Q (k + L * n) = Q k := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih => intro k; rw [Nat.mul_succ, ← add_assoc, hper, ih]
  have hmod' : ∀ k : ℕ, Q (k % L) = Q k := by
    intro k
    have := hmod (k / L) (k % L)
    rw [Nat.mod_add_div] at this
    exact this.symm
  have hv0 : V 0 = v := by
    show (alPartial38 α ζ⁻¹ 0).mulVec v = v
    rw [show alPartial38 α ζ⁻¹ 0 = 1 from rfl, Matrix.one_mulVec]
  refine ⟨fun j => Q j.val, fun j => hVn _, ?_, ?_⟩
  · intro j
    have hj : ((j.val + 1 : ℕ) : ZMod L) = j + 1 := by
      push_cast; rw [ZMod.natCast_zmod_val]
    have hv1 : (j + 1).val = (j.val + 1) % L := by rw [← hj, ZMod.val_natCast]
    show Q (j + 1).val = _
    rw [hv1, hmod', hstep j.val, ZMod.natCast_zmod_val]
  · show (alMonodromy38 α ζ⁻¹).mulVec ![1, Q (0 : ZMod L).val] =
      alExtW38 α ζ • ![1, Q (0 : ZMod L).val]
    rw [ZMod.val_zero]
    have e := hVQ 0
    rw [hv0] at e
    have hv00 : v 0 ≠ 0 := by have := hV0 0; rwa [hv0] at this
    have e2 : alExtW38 α ζ • v = v 0 • (alExtW38 α ζ • ![1, Q 0]) := by
      rw [smul_comm]; exact congrArg (fun x => alExtW38 α ζ • x) e
    have h3 : v 0 • (alMonodromy38 α ζ⁻¹).mulVec ![1, Q 0] =
        v 0 • (alExtW38 α ζ • ![1, Q 0]) := by
      rw [← Matrix.mulVec_smul, ← e, hev, e2]
    exact smul_right_injective _ hv00 h3

theorem al013s_exists_all {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) :
    ∃ q : ZMod L → ℂ, (∀ j, ‖q j‖ < 1) ∧
      (∀ j, q (j + 1) = (ζ * star (α j) + ζ ^ 2 * q j) / (1 + ζ * α j * q j)) := by
  by_cases h0 : ζ = 0
  · subst h0
    exact ⟨0, fun j => by simp, fun j => by simp⟩
  · obtain ⟨q, h1, h2, -⟩ := al013s_exists hα hζ h0
    exact ⟨q, h1, h2⟩

theorem al013s_riccatiRatio_eq {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) :
    (∀ j, ‖riccatiRatio α ζ j‖ < 1) ∧
    (∀ j, riccatiRatio α ζ (j + 1) =
      (ζ * star (α j) + ζ ^ 2 * riccatiRatio α ζ j) / (1 + ζ * α j * riccatiRatio α ζ j)) ∧
    (ζ ≠ 0 → (alMonodromy38 α ζ⁻¹).mulVec ![1, riccatiRatio α ζ 0] =
      alExtW38 α ζ • ![1, riccatiRatio α ζ 0]) := by
  have h := al013s_exists_all hα hζ
  have hs : (∀ j, ‖riccatiRatio α ζ j‖ < 1) ∧
      (∀ j, riccatiRatio α ζ (j + 1) =
        (ζ * star (α j) + ζ ^ 2 * riccatiRatio α ζ j) / (1 + ζ * α j * riccatiRatio α ζ j)) := by
    unfold riccatiRatio
    rw [dif_pos h]
    exact h.choose_spec
  refine ⟨hs.1, hs.2, fun h0 => ?_⟩
  obtain ⟨q, hq, hr, he⟩ := al013s_exists hα hζ h0
  rw [al013s_unique hα hζ hs.1 hs.2 hq hr]
  exact he

theorem al013s_prod_range {L : ℕ} [NeZero L] (f : ZMod L → ℂ) :
    ∏ i ∈ Finset.range L, f (i : ZMod L) = ∏ j : ZMod L, f j := by
  refine Finset.prod_nbij (fun i : ℕ => (i : ZMod L)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro a ha b hb hab
    have ha' := Finset.mem_range.1 (Finset.mem_coe.1 ha)
    have hb' := Finset.mem_range.1 (Finset.mem_coe.1 hb)
    have := (ZMod.natCast_eq_natCast_iff' a b L).1 hab
    rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
  · intro j _
    exact ⟨j.val, Finset.mem_coe.2 (Finset.mem_range.2 (ZMod.val_lt j)),
      ZMod.natCast_zmod_val j⟩

theorem al013s_exp_mass {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (hα : IsALField38 α) :
    ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) =
      ∏ j : ZMod L, (((Real.sqrt (1 - ‖α j‖ ^ 2) : ℝ) : ℂ))⁻¹ := by
  have hx : ∀ j, 0 < 1 - ‖α j‖ ^ 2 := fun j => by nlinarith [norm_nonneg (α j), hα j]
  have h : Real.exp (alMass38 L α / 2) = ∏ j : ZMod L, (Real.sqrt (1 - ‖α j‖ ^ 2))⁻¹ := by
    have e : alMass38 L α / 2 = ∑ j : ZMod L, (-(Real.log (1 - ‖α j‖ ^ 2) / 2)) := by
      unfold alMass38
      rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    rw [e, Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (hx j), ← Real.exp_neg]
    congr 1; ring
  rw [h]
  simp [Complex.ofReal_prod, Complex.ofReal_inv]

theorem al013s_mass_product {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) {q : ZMod L → ℂ} (hq : ∀ j, ‖q j‖ < 1)
    (hrec : ∀ j, q (j + 1) = (ζ * star (α j) + ζ ^ 2 * q j) / (1 + ζ * α j * q j)) :
    alExteriorG38 α ζ = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) *
      ∏ j : ZMod L, (1 + ζ * α j * q j) := by
  by_cases h0 : ζ = 0
  · subst h0
    rw [alExteriorG38_zero hα, al013s_zero_sol hrec]
    simp
  have hn : ‖ζ‖ < 1 := by simpa using hζ
  have horb := al013s_orbit hα hn h0 hq hrec L
  rw [ZMod.natCast_self] at horb
  have hu : (![1, q 0] : Fin 2 → ℂ) ≠ 0 := fun h => by have := congrFun h 0; simp at this
  have hJ : 0 < alJForm38 ![1, q 0] := by
    simp [alJForm38]; nlinarith [norm_nonneg (q 0), hq 0]
  have hceq := al013s_eigenvalue_eq hα hζ h0 hu hJ horb
  set F : ZMod L → ℂ := fun j => ((((Real.sqrt (1 - ‖α j‖ ^ 2) : ℝ) : ℂ))⁻¹ *
    (ζ⁻¹ + α j * q j)) with hF
  have hceq' : ∏ j : ZMod L, F j = alExtW38 α ζ := (al013s_prod_range F).symm.trans hceq
  have hr : ∀ j : ZMod L, (Real.sqrt (1 - ‖α j‖ ^ 2) : ℝ) ≠ 0 := fun j =>
    (Real.sqrt_pos.2 (by nlinarith [norm_nonneg (α j), hα j])).ne'
  have hfj : ∀ j : ZMod L, F j = (((Real.sqrt (1 - ‖α j‖ ^ 2) : ℝ) : ℂ))⁻¹ * ζ⁻¹ *
      (1 + ζ * α j * q j) := by
    intro j
    have := hr j
    simp only [hF]
    field_simp
  rw [Finset.prod_congr rfl (fun j _ => hfj j), Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ZMod.card,
    ← al013s_exp_mass α hα] at hceq'
  have hζL : ζ ^ L ≠ 0 := pow_ne_zero _ h0
  unfold alExtW38 at hceq'
  calc alExteriorG38 α ζ = ζ ^ L * ((ζ ^ L)⁻¹ * alExteriorG38 α ζ) := by field_simp
    _ = ζ ^ L * (((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) * ζ⁻¹ ^ L *
          ∏ j : ZMod L, (1 + ζ * α j * q j)) := by rw [← hceq']
    _ = _ := by rw [inv_pow]; field_simp

theorem al013s_exterior_recurrence {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {z : ℂ} (hz : 1 < ‖z‖) (j : ZMod L) :
    riccatiRatio α z⁻¹ (j + 1) =
      (star (α j) + z⁻¹ * riccatiRatio α z⁻¹ j) / (z + α j * riccatiRatio α z⁻¹ j) := by
  have hζ : z⁻¹ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
  obtain ⟨h1, h2, -⟩ := al013s_riccatiRatio_eq hα hζ
  have hq := h1 j
  have hn : ‖z⁻¹‖ < 1 := by simpa using hζ
  have hden := (al013s_step (hα j) hn (inv_ne_zero hz0) hq).1
  rw [h2 j]
  set q := riccatiRatio α z⁻¹ j
  have h1' : 1 + z⁻¹ * α j * q = z⁻¹ * (z + α j * q) := by field_simp
  have hzq : z + α j * q ≠ 0 := by
    intro h; apply hden; rw [h1', h, mul_zero]
  rw [div_eq_div_iff hden hzq]
  field_simp

end
end NlsGge.ThirdConsultation.AL
