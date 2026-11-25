import Mathlib
import NlsGge.Hierarchy.ALQuadraticPart38
import NlsGge.ThirdConsultation.AL.RiccatiSupport1

                                                                                                                                      
set_option autoImplicit false
open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory Metric
open NlsGge.AblowitzLadik
namespace NlsGge.ThirdConsultation.AL
noncomputable section

theorem al037_den {a ζ q : ℂ} (ha : ‖a‖ < 1) (hζ : ‖ζ‖ < 1) (hq : ‖q‖ < 1) :
    1 + ζ * a * q ≠ 0 := by
  intro h
  have h1 : ζ * a * q = -1 := by linear_combination h
  have h2 : ‖ζ‖ * ‖a‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg ζ) hζ ha.le
  have h3 : ‖ζ‖ * ‖a‖ * ‖q‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_left
    (mul_nonneg (norm_nonneg ζ) (norm_nonneg a)) h2 hq.le
  have h4 : ‖ζ * a * q‖ < 1 := by rw [norm_mul, norm_mul]; exact h3
  rw [h1] at h4; simp at h4

theorem al037_series {L : ℕ} [NeZero L] (α : ZMod L → ℂ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (j : ZMod L) :
    Summable (fun k : ℕ => ‖ζ ^ (2 * k + 1) * star (α (j - ((k + 1 : ℕ) : ZMod L)))‖) ∧
    (∑' k : ℕ, ‖ζ ^ (2 * k + 1) * star (α (j - ((k + 1 : ℕ) : ZMod L)))‖) ≤
      ‖α‖ * ‖ζ‖ / (1 - ‖ζ‖ ^ 2) := by
  have hr2 : ‖ζ‖ ^ 2 < 1 := by nlinarith [norm_nonneg ζ]
  have hg : Summable (fun k : ℕ => ‖α‖ * ‖ζ‖ * (‖ζ‖ ^ 2) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) hr2).mul_left _
  have hb : ∀ k : ℕ, ‖ζ ^ (2 * k + 1) * star (α (j - ((k + 1 : ℕ) : ZMod L)))‖ ≤
      ‖α‖ * ‖ζ‖ * (‖ζ‖ ^ 2) ^ k := by
    intro k
    rw [norm_mul, norm_pow, norm_star]
    have h1 : ‖α (j - ((k + 1 : ℕ) : ZMod L))‖ ≤ ‖α‖ := norm_le_pi_norm α _
    have h2 : ‖ζ‖ ^ (2 * k + 1) = ‖ζ‖ * (‖ζ‖ ^ 2) ^ k := by rw [pow_succ, pow_mul]; ring
    rw [h2]
    nlinarith [mul_nonneg (norm_nonneg ζ) (pow_nonneg (sq_nonneg ‖ζ‖) k)]
  have hs := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb hg
  refine ⟨hs, ?_⟩
  calc (∑' k : ℕ, ‖ζ ^ (2 * k + 1) * star (α (j - ((k + 1 : ℕ) : ZMod L)))‖)
      ≤ ∑' k : ℕ, ‖α‖ * ‖ζ‖ * (‖ζ‖ ^ 2) ^ k := Summable.tsum_le_tsum hb hs hg
    _ = ‖α‖ * ‖ζ‖ / (1 - ‖ζ‖ ^ 2) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr2]; ring

theorem al037_summable {L : ℕ} [NeZero L] (α : ZMod L → ℂ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (j : ZMod L) :
    Summable (fun k : ℕ => ζ ^ (2 * k + 1) * star (α (j - ((k + 1 : ℕ) : ZMod L)))) :=
  Summable.of_norm (al037_series α hζ j).1

theorem al037_qstar_succ {L : ℕ} [NeZero L] (α : ZMod L → ℂ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) (k : ℕ) :
    alQStar38 α ζ (k + 1) = ζ * star (α (k : ZMod L)) + ζ ^ 2 * alQStar38 α ζ k := by
  have hs : ∀ x : ℂ, star x = starRingEnd ℂ x := fun x => rfl
  have hsum := al037_summable α hζ ((k + 1 : ℕ) : ZMod L)
  simp only [hs] at hsum
  unfold alQStar38
  simp only [hs]
  rw [hsum.tsum_eq_zero_add]
  congr 1
  · simp
  · rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    have e : ((k + 1 : ℕ) : ZMod L) - ((m + 1 + 1 : ℕ) : ZMod L) =
        (k : ZMod L) - ((m + 1 : ℕ) : ZMod L) := by push_cast; ring
    rw [e]; ring

theorem al037_qstar_succ' {L : ℕ} [NeZero L] (α : ZMod L → ℂ) {ζ : ℂ} (hζ : ‖ζ‖ < 1)
    (j : ZMod L) :
    alQStar38 α ζ (j + 1).val = ζ * star (α j) + ζ ^ 2 * alQStar38 α ζ j.val := by
  have h1 : (((j + 1).val : ℕ) : ZMod L) = ((j.val + 1 : ℕ) : ZMod L) := by
    rw [ZMod.natCast_zmod_val]; push_cast; rw [ZMod.natCast_zmod_val]
  have h2 : alQStar38 α ζ (j + 1).val = alQStar38 α ζ (j.val + 1) := by
    unfold alQStar38; rw [h1]
  rw [h2, al037_qstar_succ α hζ, ZMod.natCast_zmod_val]

theorem al037_unique {L : ℕ} [NeZero L] (α : ZMod L → ℂ) {ζ : ℂ} (hζ : ‖ζ‖ < 1)
    (q : ZMod L → ℂ) (hq : ∀ j, q (j + 1) = ζ * star (α j) + ζ ^ 2 * q j) :
    q = fun j => alQStar38 α ζ j.val := by
  set d : ZMod L → ℂ := fun j => q j - alQStar38 α ζ j.val with hd
  have hd1 : ∀ j, d (j + 1) = ζ ^ 2 * d j := by
    intro j
    simp only [hd]
    rw [hq j, al037_qstar_succ' α hζ j]; ring
  have hk : ∀ (k : ℕ) (j : ZMod L), d (j + (k : ZMod L)) = (ζ ^ 2) ^ k * d j := by
    intro k
    induction k with
    | zero => intro j; simp
    | succ k ih =>
      intro j
      have : j + ((k + 1 : ℕ) : ZMod L) = (j + (k : ZMod L)) + 1 := by push_cast; ring
      rw [this, hd1, ih]; ring
  funext j
  have h := hk L j
  rw [ZMod.natCast_self, add_zero] at h
  have hL : 0 < L := NeZero.pos L
  have hlt : ‖(ζ ^ 2) ^ L‖ < 1 := by
    rw [norm_pow, norm_pow]
    exact pow_lt_one₀ (by positivity) (by nlinarith [norm_nonneg ζ]) hL.ne'
  have h1 : (1 - (ζ ^ 2) ^ L) * d j = 0 := by linear_combination h
  have h2 : (1 - (ζ ^ 2) ^ L) ≠ 0 := by
    intro h0
    have : (ζ ^ 2) ^ L = 1 := by linear_combination -h0
    rw [this, norm_one] at hlt; exact lt_irrefl _ hlt
  have h3 : d j = 0 := (mul_eq_zero.1 h1).resolve_left h2
  exact sub_eq_zero.1 h3

theorem al037_bounds {L : ℕ} [NeZero L] {β q p : ZMod L → ℂ} {ζ : ℂ} {s : ℝ}
    (hζ : ‖ζ‖ < 1) (hs0 : 0 ≤ s) (hs : ‖ζ‖ * s ≤ (1 - ‖ζ‖ ^ 2) / 2)
    (hβ : ∀ j, ‖β j‖ ≤ s) (hq : ∀ j, ‖q j‖ < 1)
    (hprod : ∀ j, q (j + 1) * (1 + ζ * β j * q j) = ζ * star (β j) + ζ ^ 2 * q j)
    (hp : ∀ j, p (j + 1) = ζ * star (β j) + ζ ^ 2 * p j) :
    (∀ j, ‖q j‖ ≤ 2 * (‖ζ‖ * s) / (1 - ‖ζ‖ ^ 2)) ∧
    (∀ j, ‖q j - p j‖ ≤
      ‖ζ‖ * s * (2 * (‖ζ‖ * s) / (1 - ‖ζ‖ ^ 2)) ^ 2 / (1 - ‖ζ‖ ^ 2)) := by
  haveI : Nonempty (ZMod L) := ⟨0⟩
  set r : ℝ := ‖ζ‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg ζ
  have hκ : 0 < 1 - r ^ 2 := by nlinarith
  have hrs0 : 0 ≤ r * s := mul_nonneg hr0 hs0
  have hc : ∀ j, ‖ζ * star (β j) + ζ ^ 2 * q j‖ ≤ r * s + r ^ 2 * ‖q j‖ := by
    intro j
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, norm_star]
    exact add_le_add (mul_le_mul_of_nonneg_left (hβ j) hr0) le_rfl
  have hx : ∀ j, ‖q (j + 1) * (ζ * β j * q j)‖ ≤ ‖q (j + 1)‖ * (r * s) := by
    intro j
    rw [norm_mul, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖ζ‖ * ‖β j‖ * ‖q j‖ ≤ r * s * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hβ j) hr0) (hq j).le (norm_nonneg _) hrs0
      _ = r * s := by ring
  have step1 : ∀ j, ‖q (j + 1)‖ ≤ r * s + r ^ 2 * ‖q j‖ + ‖q (j + 1)‖ * (r * s) := by
    intro j
    have e : q (j + 1) = (ζ * star (β j) + ζ ^ 2 * q j) - q (j + 1) * (ζ * β j * q j) := by
      linear_combination hprod j
    calc ‖q (j + 1)‖ = ‖(ζ * star (β j) + ζ ^ 2 * q j) - q (j + 1) * (ζ * β j * q j)‖ := by
          rw [← e]
      _ ≤ ‖ζ * star (β j) + ζ ^ 2 * q j‖ + ‖q (j + 1) * (ζ * β j * q j)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hc j, hx j]
  obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j : ZMod L => ‖q j‖)
  have hM : ‖q j0‖ ≤ 2 * (r * s) / (1 - r ^ 2) := by
    have h := step1 (j0 - 1)
    rw [sub_add_cancel] at h
    have h' : ‖q (j0 - 1)‖ ≤ ‖q j0‖ := hj0 _
    rw [le_div_iff₀ hκ]
    nlinarith [norm_nonneg (q j0), mul_nonneg hrs0 (norm_nonneg (q j0))]
  have hA : ∀ j, ‖q j‖ ≤ 2 * (r * s) / (1 - r ^ 2) := fun j => (hj0 j).trans hM
  refine ⟨hA, ?_⟩
  set A : ℝ := 2 * (r * s) / (1 - r ^ 2) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hstep : ∀ j, ‖q (j + 1) - p (j + 1)‖ ≤ r ^ 2 * ‖q j - p j‖ + r * s * A ^ 2 := by
    intro j
    have e : q (j + 1) - p (j + 1) =
        ζ ^ 2 * (q j - p j) - q (j + 1) * (ζ * β j * q j) := by
      linear_combination hprod j - hp j
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_pow]
    · rw [norm_mul, norm_mul, norm_mul]
      have h1 : ‖ζ‖ * ‖β j‖ * ‖q j‖ ≤ r * s * A :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hβ j) hr0) (hA j) (norm_nonneg _) hrs0
      calc ‖q (j + 1)‖ * (‖ζ‖ * ‖β j‖ * ‖q j‖) ≤ A * (r * s * A) :=
            mul_le_mul (hA _) h1 (by positivity) hA0
        _ = r * s * A ^ 2 := by ring
  obtain ⟨j1, hj1⟩ := Finite.exists_max (fun j : ZMod L => ‖q j - p j‖)
  have hE : ‖q j1 - p j1‖ ≤ r * s * A ^ 2 / (1 - r ^ 2) := by
    have h := hstep (j1 - 1)
    rw [sub_add_cancel] at h
    have h' : ‖q (j1 - 1) - p (j1 - 1)‖ ≤ ‖q j1 - p j1‖ := hj1 _
    rw [le_div_iff₀ hκ]
    nlinarith [norm_nonneg (q j1 - p j1), sq_nonneg r]
  exact fun j => (hj1 j).trans hE

theorem al037 {L : ℕ} [NeZero L]
    (α : ZMod L → ℂ) (z : ℂ) (hz : 1 < ‖z‖) :
  (∀ j : ZMod L,
    Summable (fun k : ℕ => ‖z⁻¹^(2*k+1)*star (α (j-((k+1 : ℕ) : ZMod L)))‖) ∧
    HasSum (fun k : ℕ => z⁻¹^(2*k+1)*star (α (j-((k+1 : ℕ) : ZMod L))))
      (alQStar38 α z⁻¹ j.val) ∧
    (∑' k : ℕ, ‖z⁻¹^(2*k+1)*star (α (j-((k+1 : ℕ) : ZMod L)))‖) ≤
      ‖α‖*‖z⁻¹‖/(1-‖z⁻¹‖^2) ∧
    HasDerivAt (fun t : ℝ => riccatiRatio (t • α) z⁻¹ j)
      (alQStar38 α z⁻¹ j.val) 0) ∧
  (∀ j : ZMod L,
    alQStar38 α z⁻¹ (j+1).val =
      z⁻¹*star (α j)+z⁻¹^2*alQStar38 α z⁻¹ j.val) ∧
  ∀ q : ZMod L → ℂ,
    (∀ j, q (j+1) = z⁻¹*star (α j)+z⁻¹^2*q j) →
      q = fun j => alQStar38 α z⁻¹ j.val := by
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hζ : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have hr0 : 0 < ‖z⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hz0)
  refine ⟨fun j => ⟨(al037_series α hζ j).1, ?_, (al037_series α hζ j).2, ?_⟩,
    fun j => al037_qstar_succ' α hζ j, fun q hq => al037_unique α hζ q hq⟩
  · have h := (al037_summable α hζ j).hasSum
    unfold alQStar38
    rw [ZMod.natCast_zmod_val]
    exact h
  · -- derivative
    set ζ : ℂ := z⁻¹ with hζdef
    set r : ℝ := ‖ζ‖ with hr
    set a : ℝ := ‖α‖ with ha
    have hκ : 0 < 1 - r ^ 2 := by nlinarith
    set Cc : ℝ := r * a * (2 * (r * a) / (1 - r ^ 2)) ^ 2 / (1 - r ^ 2) with hCc
    have hev : ∀ᶠ t : ℝ in 𝓝 0, |t| * a < 1 ∧ r * (|t| * a) ≤ (1 - r ^ 2) / 2 := by
      have hc : ContinuousAt (fun t : ℝ => |t| * a) 0 := (by fun_prop : Continuous _).continuousAt
      have hc2 : ContinuousAt (fun t : ℝ => r * (|t| * a)) 0 :=
        (by fun_prop : Continuous _).continuousAt
      refine (hc.eventually (gt_mem_nhds (by simp))).and
        (hc2.eventually (ge_mem_nhds (by
          have : (0 : ℝ) < (1 - r ^ 2) / 2 := by nlinarith
          simpa using this)))
    have hbd : ∀ᶠ t : ℝ in 𝓝 0, ‖riccatiRatio (t • α) ζ j - (t : ℂ) * alQStar38 α ζ j.val‖ ≤
        Cc * |t| ^ 3 := by
      filter_upwards [hev] with t ht
      have hAL : IsALField38 (t • α) := by
        intro i
        rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
        have := norm_le_pi_norm α i
        have h0 := abs_nonneg t
        nlinarith [mul_le_mul_of_nonneg_left this h0]
      have hball : ζ ∈ ball (0 : ℂ) 1 := by simpa using hζ
      obtain ⟨h1, h2, -⟩ := al013s_riccatiRatio_eq hAL hball
      have hprod : ∀ i, riccatiRatio (t • α) ζ (i + 1) *
          (1 + ζ * (t • α) i * riccatiRatio (t • α) ζ i) =
          ζ * star ((t • α) i) + ζ ^ 2 * riccatiRatio (t • α) ζ i := by
        intro i
        rw [h2 i]
        exact div_mul_cancel₀ _ (al037_den (hAL i) hζ (h1 i))
      have hp : ∀ i, (fun i : ZMod L => (t : ℂ) * alQStar38 α ζ i.val) (i + 1) =
          ζ * star ((t • α) i) + ζ ^ 2 * (fun i : ZMod L => (t : ℂ) * alQStar38 α ζ i.val) i := by
        intro i
        simp only
        rw [al037_qstar_succ' α hζ i]
        simp only [Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
          Complex.conj_ofReal]
        ring
      have hb := (al037_bounds (β := t • α) (q := riccatiRatio (t • α) ζ)
        (p := fun i : ZMod L => (t : ℂ) * alQStar38 α ζ i.val) (s := |t| * a) hζ
        (mul_nonneg (abs_nonneg t) (norm_nonneg α)) ht.2
        (fun i => by
          rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm α i) (abs_nonneg t))
        h1 hprod hp).2 j
      refine hb.trans (le_of_eq ?_)
      simp only [hCc, hr, ha]
      have : |t| ^ 3 = |t| * |t| * |t| := by ring
      rw [this]
      field_simp
    have h0 : riccatiRatio ((0 : ℝ) • α) ζ j = 0 := by
      have := hbd.self_of_nhds
      simpa using this
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hbig : (fun t : ℝ => riccatiRatio ((0 + t) • α) ζ j - riccatiRatio ((0 : ℝ) • α) ζ j -
        t • alQStar38 α ζ j.val) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
      refine Asymptotics.IsBigO.of_bound Cc ?_
      filter_upwards [hbd] with t ht
      rw [zero_add, h0, sub_zero, Complex.real_smul, norm_pow, Real.norm_eq_abs]
      exact ht
    exact hbig.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))

end
end NlsGge.ThirdConsultation.AL
