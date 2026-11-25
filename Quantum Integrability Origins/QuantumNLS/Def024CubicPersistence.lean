import QuantumNLS.F04Global

/-!
# DEF-024 cubic persistence: global `H^s` mild solutions and the `H^s` a priori bound, all `s ≥ 1`

Source: `F04:lem-regular` (R-3F6AA186, `F04Regularity.h3_bound_Imax`, proved at order `3` only) and
`F04:thm-global` (R-169AABCC). The order-`3` argument is generalized here to every `s ≥ 1`.

Inputs used (all accepted, read-only):
* `Fourier.f04_tame`: the tame product bound `‖F(a)‖_{h^s} ≤ C_s ‖a‖²_{h^1} ‖a‖_{h^s}` for every
  `s ≥ 1`, with `C_s = Cs L s` (`LocalWellPosedness.norm_Fh_le` is its consequence);
* `LocalWellPosedness.IsMild`, `duhamel`, `Sgrp` (isometric), `continuous_Fh`, `gronwall_fwd/bwd`,
  `mild_unique`, `umax_mild`, `IsMild.mono`, `integrable_duhamel`;
* `LocalWellPosednessFull.Imax`, `umax`, `zero_mem_Imax`, `Imax_ordConnected`, `blowup_right/left`;
* `F04Global.thm_global` (the `H¹` flow, its energy bound `‖u(t)‖²_{H¹} ≤ M(u₀)+E(u₀)`), and
  `F04Global.umax1_mild`.

Realized here (no hypothesis beyond the accepted modules):
* `proj1`: the `H^s → H¹` projection `h04_mono`, which commutes with `Sgrp` and `Fh`
  (`proj1_Sgrp`, `proj1_Fh`: the values depend only on the coefficient sequence);
* `mild_proj`: the projection of an `H^s` mild solution is an `H¹` mild solution;
* `h1_bound_s`: `‖u(t)‖_{H¹} ≤ K` along every `H^s` solution, with `K = max(M+E, 0)` of the
  projected datum (by `mild_unique` and `thm_global`);
* `tame_s`: `‖F(a)‖_{H^s} ≤ C_s ‖a‖²_{H¹} ‖a‖_{H^s}`;
* `persist_bound`: `‖u(t)‖_{H^s} ≤ ‖u₀‖_{H^s} exp(2κ C_s K |t|)` on the maximal interval;
* `Imax_eq_univ_s`: the maximal `H^s` interval is `ℝ` (global existence for every `s ≥ 1`);
* `persist_global`: the global `H^s` mild solution with the bound on every `t ∈ ℝ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped BigOperators Topology ComplexConjugate InnerProductSpace
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
  QuantumNLS.F04Global

namespace QuantumNLS.Def024CubicPersistence

variable {L : ℝ} [Fact (0 < L)]

/-- The `H^s → H¹` projection (the Sobolev inclusion, as in `m31` at order `3`). -/
abbrev proj1 {s : ℝ} (hs : 1 ≤ s) : h04 L s →L[ℂ] h04 L 1 := h04_mono L hs

@[simp] lemma proj1_val_apply {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) (n : ℤ) :
    (proj1 (L := L) hs a).val n = a.val n := rfl

lemma proj1_Sgrp {s : ℝ} (hs : 1 ≤ s) (t : ℝ) (a : h04 L s) :
    proj1 (L := L) hs (Sgrp s t a) = Sgrp 1 t (proj1 (L := L) hs a) :=
  WSeq.ext (funext fun n => by simp only [proj1_val_apply, Sgrp_val])

lemma proj1_Fh {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) :
    proj1 (L := L) hs (Fh hs a) = Fh (le_refl (1 : ℝ)) (proj1 (L := L) hs a) :=
  WSeq.ext rfl

/-- The projection of an `H^s` mild solution is an `H¹` mild solution. -/
lemma mild_proj {s : ℝ} (hs : 1 ≤ s) {κ : ℝ} {I : Set ℝ} {u0 : h04 L s} {u : ℝ → h04 L s}
    (hu : IsMild hs κ I u0 u) :
    IsMild (le_refl (1 : ℝ)) κ I (proj1 (L := L) hs u0) (fun t => proj1 (L := L) hs (u t)) := by
  refine ⟨hu.zero_mem, hu.ordConnected, (proj1 (L := L) hs).continuous.comp_continuousOn hu.cont,
    fun t ht => ?_⟩
  rw [hu.duhamel_eq t ht]
  unfold duhamel
  have hi := integrable_duhamel hs hu.ordConnected hu.cont t 0 t hu.zero_mem ht
  have e : ∫ r in (0 : ℝ)..t, proj1 (L := L) hs (Sgrp s (t - r) (Fh hs (u r))) =
      ∫ r in (0 : ℝ)..t, Sgrp 1 (t - r) (Fh (le_refl (1 : ℝ)) (proj1 (L := L) hs (u r))) :=
    intervalIntegral.integral_congr fun r _ => by simp only [proj1_Sgrp, proj1_Fh]
  rw [map_sub, map_smul, proj1_Sgrp, ← (proj1 (L := L) hs).intervalIntegral_comp_comm hi, e]

/-- The constant `K = max(M(P u₀) + E(P u₀), 0)` of the projected datum (`H¹` energy bound). -/
def Kp {s : ℝ} (hs : 1 ≤ s) (κ : ℝ) (u0 : h04 L s) : ℝ :=
  max ((∫ x, ‖S1 (proj1 (L := L) hs u0) x‖ ^ 2) +
    QuantumNLS.ChargeEnergy.energyH1 κ (S1 (proj1 (L := L) hs u0))) 0

/-- **`H¹` bound along an `H^s` solution.** -/
lemma h1_bound_s {s : ℝ} (hs : 1 ≤ s) {κ : ℝ} (hκ : 0 ≤ κ) (u0 : h04 L s) {t : ℝ}
    (ht : t ∈ Imax hs κ u0) : ‖proj1 (L := L) hs (umax hs κ u0 t)‖ ^ 2 ≤ Kp hs κ u0 := by
  have hu := umax_mild (hs := hs) hκ u0
  have hp := mild_proj (L := L) hs hu
  have hv : IsMild (le_refl (1 : ℝ)) κ (Imax hs κ u0) (proj1 (L := L) hs u0)
      (umax (le_refl (1 : ℝ)) κ (proj1 (L := L) hs u0)) :=
    (umax1_mild hκ (proj1 (L := L) hs u0)).mono (Set.subset_univ _) (zero_mem_Imax hκ u0)
      (Imax_ordConnected u0)
  have heq := mild_unique (le_refl (1 : ℝ)) hκ hp hv t ht
  have hb := (thm_global hκ (proj1 (L := L) hs u0)).2.2.2.2.2.2.2.2.2.1 t
  have hn : ‖proj1 (L := L) hs (umax hs κ u0 t)‖ =
      ‖umax (le_refl (1 : ℝ)) κ (proj1 (L := L) hs u0) t‖ := congrArg norm heq
  rw [hn]
  exact le_trans hb (le_max_left _ _)

/-- **Tame estimate at every order `s ≥ 1`**: `‖F(a)‖_{H^s} ≤ C_s ‖a‖²_{H¹} ‖a‖_{H^s}`. -/
lemma tame_s {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) :
    ‖Fh hs a‖ ≤ Cs L s * ‖proj1 (L := L) hs a‖ ^ 2 * ‖a‖ := by
  have h := (f04_tame hs (h04_mem L s a)).2
  rw [norm_eq_sqrt s (Fh hs a), norm_eq_sqrt 1 (proj1 (L := L) hs a), norm_eq_sqrt s a]
  exact h

/-- **`H^s` a priori bound on the maximal interval**, all `s ≥ 1`:
`‖u(t)‖_{H^s} ≤ ‖u₀‖_{H^s} exp(2κ C_s K |t|)`. Duhamel, the tame estimate, the `H¹` bound of
`h1_bound_s`, and Gronwall (as `h3_bound_Imax`, at order `s`). -/
lemma persist_bound {s : ℝ} (hs : 1 ≤ s) {κ : ℝ} (hκ : 0 ≤ κ) (u0 : h04 L s) {t : ℝ}
    (ht : t ∈ Imax hs κ u0) :
    ‖umax hs κ u0 t‖ ≤ ‖u0‖ * Real.exp (2 * κ * Cs L s * Kp hs κ u0 * |t|) := by
  have hu := umax_mild (hs := hs) hκ u0
  set u := umax hs κ u0
  set I := Imax hs κ u0
  set c := Cs L s
  have hc : 0 ≤ c := le_trans zero_le_one (one_le_Cs L s)
  have hK : 0 ≤ Kp hs κ u0 := le_max_right _ _
  set K := Kp hs κ u0
  set b := 2 * κ * c * K
  have hb : 0 ≤ b := by positivity
  set a := ‖u0‖
  have h0 : (0 : ℝ) ∈ I := zero_mem_Imax hκ u0
  have hsub : Set.uIcc 0 t ⊆ I := hu.ordConnected.uIcc_subset h0 ht
  set lo := min 0 t
  set hi := max 0 t
  have hlohi : lo ≤ hi := min_le_max
  set φ0 : ℝ → ℝ := fun r => ‖u r‖
  have hφ0 : ContinuousOn φ0 (Set.Icc lo hi) := (hu.cont.mono hsub).norm
  set φ : ℝ → ℝ := fun r => φ0 (Set.projIcc lo hi hlohi r)
  have hφ : Continuous φ := hφ0.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun r => (Set.projIcc lo hi hlohi r).2)
  have hφeq : ∀ r ∈ Set.Icc lo hi, φ r = φ0 r := fun r hr => by
    simp only [φ, Set.projIcc_of_mem hlohi hr]
  have key : ∀ r ∈ Set.uIcc 0 t, φ0 r ≤ a + b * |∫ x in (0 : ℝ)..r, φ x| := by
    intro r hr
    have hrI := hsub hr
    have hsubr : Set.uIcc 0 r ⊆ Set.uIcc 0 t := Set.uIcc_subset_uIcc_left hr
    have hpt : ∀ x ∈ Set.uIcc 0 r,
        ‖Sgrp s (r - x) (Fh hs (u x))‖ ≤ (c * K) * φ x := by
      intro x hx
      have hxI := hsub (hsubr hx)
      rw [norm_Sgrp, hφeq x (hsubr hx)]
      have h1 := h1_bound_s hs hκ u0 hxI
      calc ‖Fh hs (u x)‖ ≤ c * ‖proj1 (L := L) hs (u x)‖ ^ 2 * ‖u x‖ := tame_s hs _
        _ ≤ c * K * ‖u x‖ := by gcongr
    have hgc : ContinuousOn (fun x => ‖Sgrp s (r - x) (Fh hs (u x))‖) (Set.uIcc 0 r) :=
      (continuousOn_Sgrp (continuous_const.sub continuous_id)
        ((continuous_Fh hs).comp_continuousOn (hu.cont.mono (hsubr.trans hsub)))).norm
    have hint := abs_integral_le_of_le (fun x _ => norm_nonneg _) hpt hgc.intervalIntegrable
      ((hφ.const_mul _).intervalIntegrable _ _)
    have hn : ‖u r‖ ≤ a + 2 * κ * |∫ x in (0 : ℝ)..r, ‖Sgrp s (r - x) (Fh hs (u x))‖| := by
      rw [hu.duhamel_eq r hrI]
      unfold duhamel
      refine (norm_sub_le _ _).trans ?_
      rw [norm_Sgrp, norm_smul, norm_coef κ hκ]
      have := intervalIntegral.norm_integral_le_abs_integral_norm (μ := volume) (a := 0) (b := r)
        (f := fun x => Sgrp s (r - x) (Fh hs (u x)))
      nlinarith
    have hlin : |∫ x in (0 : ℝ)..r, (c * K) * φ x| =
        (c * K) * |∫ x in (0 : ℝ)..r, φ x| := by
      rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity)]
    show ‖u r‖ ≤ a + b * |∫ x in (0 : ℝ)..r, φ x|
    rw [hlin] at hint
    have hb' : b = 2 * κ * (c * K) := by simp only [b]; ring
    rw [hb']
    nlinarith
  rcases le_total 0 t with h | h
  · have hfwd : ∀ r ∈ Set.Icc 0 t, φ r ≤ a + b * ∫ x in (0 : ℝ)..r, φ x := by
      intro r hr
      have hrI : r ∈ Set.uIcc 0 t := Set.Icc_subset_uIcc hr
      have hmem : r ∈ Set.Icc lo hi := hrI
      rw [hφeq r hmem]
      have := key r hrI
      rwa [abs_of_nonneg (intervalIntegral.integral_nonneg hr.1 fun x _ => norm_nonneg _)] at this
    have := gronwall_fwd hφ hb hfwd t ⟨h, le_rfl⟩
    rw [hφeq t Set.right_mem_uIcc, sub_zero] at this
    rw [abs_of_nonneg h]
    exact this
  · have hbwd : ∀ r ∈ Set.Icc t 0, φ r ≤ a + b * ∫ x in r..(0 : ℝ), φ x := by
      intro r hr
      have hrI : r ∈ Set.uIcc 0 t := Set.Icc_subset_uIcc' hr
      have hmem : r ∈ Set.Icc lo hi := hrI
      rw [hφeq r hmem]
      have := key r hrI
      rwa [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (intervalIntegral.integral_nonneg hr.2 fun x _ => norm_nonneg _)] at this
    have := gronwall_bwd hφ hb hbwd t ⟨le_rfl, h⟩
    rw [hφeq t Set.right_mem_uIcc, zero_sub] at this
    rw [abs_of_nonpos h]
    exact this

/-- **Globality at every order `s ≥ 1`**: the maximal `H^s` interval is all of `ℝ`. -/
lemma Imax_eq_univ_s {s : ℝ} (hs : 1 ≤ s) {κ : ℝ} (hκ : 0 ≤ κ) (u0 : h04 L s) :
    Imax hs κ u0 = Set.univ := by
  set I := Imax hs κ u0
  set B := 2 * κ * Cs L s * Kp hs κ u0
  have hB : 0 ≤ B := by
    have := le_trans zero_le_one (one_le_Cs L s)
    have := le_max_right ((∫ x, ‖S1 (proj1 (L := L) hs u0) x‖ ^ 2) +
      QuantumNLS.ChargeEnergy.energyH1 κ (S1 (proj1 (L := L) hs u0))) 0
    unfold B Kp
    positivity
  have hcap : ∀ t ∈ I, ∀ S : ℝ, |t| ≤ |S| + 1 →
      ‖umax hs κ u0 t‖ ≤ ‖u0‖ * Real.exp (B * (|S| + 1)) := by
    intro t ht S hS
    refine (persist_bound hs hκ u0 ht).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hS hB))
      (norm_nonneg _)
  have hA : ¬ BddAbove I := by
    intro hb
    obtain ⟨t, htI, ht1, ht2⟩ := blowup_right (hs := hs) hκ u0 hb
      (‖u0‖ * Real.exp (B * (|sSup I| + 1))) 1 one_pos
    have htS : t ≤ sSup I := le_csSup hb htI
    have habs : |t| ≤ |sSup I| + 1 :=
      abs_le.mpr ⟨by linarith [neg_abs_le (sSup I)], by linarith [le_abs_self (sSup I)]⟩
    linarith [hcap t htI _ habs]
  have hA' : ¬ BddBelow I := by
    intro hb
    obtain ⟨t, htI, ht1, ht2⟩ := blowup_left (hs := hs) hκ u0 hb
      (‖u0‖ * Real.exp (B * (|sInf I| + 1))) 1 one_pos
    have htS : sInf I ≤ t := csInf_le hb htI
    have habs : |t| ≤ |sInf I| + 1 :=
      abs_le.mpr ⟨by linarith [neg_abs_le (sInf I)], by linarith [le_abs_self (sInf I)]⟩
    linarith [hcap t htI _ habs]
  ext x
  simp only [Set.mem_univ, iff_true]
  obtain ⟨y, hyI, hxy⟩ := not_bddAbove_iff.mp hA x
  obtain ⟨z, hzI, hzx⟩ := not_bddBelow_iff.mp hA' x
  exact (Imax_ordConnected u0).out hzI hyI ⟨hzx.le, hxy.le⟩

/-- **Global `H^s` solutions with the a priori bound, every `s ≥ 1`.** -/
theorem persist_global {s : ℝ} (hs : 1 ≤ s) {κ : ℝ} (hκ : 0 ≤ κ) (u0 : h04 L s) :
    IsMild hs κ Set.univ u0 (umax hs κ u0) ∧
    ∀ t : ℝ, ‖umax hs κ u0 t‖ ≤ ‖u0‖ * Real.exp (2 * κ * Cs L s * Kp hs κ u0 * |t|) := by
  have hU := Imax_eq_univ_s hs hκ u0
  have hu := umax_mild (hs := hs) hκ u0
  rw [hU] at hu
  exact ⟨hu, fun t => persist_bound hs hκ u0 (by rw [hU]; exact Set.mem_univ t)⟩

#print axioms proj1_Sgrp
#print axioms mild_proj
#print axioms h1_bound_s
#print axioms tame_s
#print axioms persist_bound
#print axioms Imax_eq_univ_s
#print axioms persist_global

end QuantumNLS.Def024CubicPersistence
