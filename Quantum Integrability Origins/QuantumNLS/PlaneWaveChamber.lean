import Mathlib
import QuantumNLS.VolterraSeries
import QuantumNLS.BetheTransferOperators
import QuantumNLS.BetheWeakGradient

/-!
# Nested alternating-chamber integrals of exponentials equal the Volterra iterates

Source use: `ROOT_spectral_measure.tex`, `prop:root-free`, plane-wave clause: the printed computation of `⟨u^{⊗r}, K_{r,z}u^{⊗r}⟩` for the plane wave reduces to the integral over the alternating
chamber `{L > x₁ > y₁ > ⋯ > x_r > y_r > 0}` of `e^{iw Σ(x_j − y_j)}`.  With `Jc L r ℓ w = ∫_x ∫_y rawPlus ℓ w x y` (iterated integral over the cubes `[0,L]^r`; `rawPlus` is the frozen
literal chamber kernel of `BetheTransferKernelAdjoint`) we prove, for `0 ≤ ℓ ≤ L`,

  `Jc L r ℓ w = R_r(ℓ)`  (`VolterraSeries.Rr (I*w) r ℓ`, the iterates of `(Tf)(ℓ) = ∫₀^ℓ f(y)(e^{iw(ℓ−y)} − 1)/(iw) dy`),

by peeling off the first pair of coordinates with `plusOrder_cons` (a single change of variables for each cube and two Fubini swaps).  No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set

noncomputable section

namespace QuantumNLS.PlaneWaveChamber

open QuantumNLS.BetheTransferKernelAdjoint (PlusOrder displacement rawPlus plusOrder_cons)
open QuantumNLS.BetheWeakGradient (cubeMeasure cubeMeasure_eq_pi)
open QuantumNLS.BetheTransferOperators (measurable_rawPlus norm_rawPlus_le)
open QuantumNLS.VolterraSeries (kk kk_eq_integral Rr Tk continuous_Rr)

/-! ### Generic measurability and integrability -/

section Generic

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem measurable_param {ν : Measure β} [SFinite ν] {f : α × β → ℂ} (hf : Measurable f) :
    Measurable fun a => ∫ b, f (a, b) ∂ν :=
  (hf.stronglyMeasurable.integral_prod_right').measurable

theorem norm_param_le {ν : Measure β} [IsFiniteMeasure ν] {f : α × β → ℂ} {B : ℝ} (hb : ∀ p, ‖f p‖ ≤ B) (a : α) :
    ‖∫ b, f (a, b) ∂ν‖ ≤ B * ν.real univ := by
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun b => f (a, b)) (C := B)
    (Eventually.of_forall fun b => hb (a, b))
  simpa [mul_comm] using this

theorem integrable_bdd {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℂ} (hf : Measurable f) {B : ℝ}
    (hb : ∀ a, ‖f a‖ ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall hb)

theorem integrable_param {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure β} [IsFiniteMeasure ν]
    {f : α × β → ℂ} (hf : Measurable f) {B : ℝ} (hb : ∀ p, ‖f p‖ ≤ B) :
    Integrable (fun a => ∫ b, f (a, b) ∂ν) μ :=
  integrable_bdd (measurable_param hf) (norm_param_le hb)

end Generic

section Reorder

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]

/-- Swapping the two middle integrals of a bounded measurable four-fold iterated integral. -/
theorem reorder4 {μA : Measure A} {μB : Measure B} {μC : Measure C} {μD : Measure D}
    [IsFiniteMeasure μB] [IsFiniteMeasure μC] [IsFiniteMeasure μD]
    {G : A → B → C → D → ℂ} (hG : Measurable (fun p : ((A × B) × C) × D => G p.1.1.1 p.1.1.2 p.1.2 p.2))
    {K : ℝ} (hK : ∀ a b c d, ‖G a b c d‖ ≤ K) :
    ∫ a, ∫ b, ∫ c, ∫ d, G a b c d ∂μD ∂μC ∂μB ∂μA = ∫ a, ∫ c, ∫ b, ∫ d, G a b c d ∂μD ∂μB ∂μC ∂μA := by
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  have h1 : Measurable (fun p : (B × C) × D => G a p.1.1 p.1.2 p.2) :=
    hG.comp (by fun_prop : Measurable (fun p : (B × C) × D => (((a, p.1.1), p.1.2), p.2)))
  have hH : Measurable (fun q : B × C => ∫ d, G a q.1 q.2 d ∂μD) := measurable_param h1
  have hHb : ∀ q : B × C, ‖∫ d, G a q.1 q.2 d ∂μD‖ ≤ K * μD.real univ := fun q =>
    norm_param_le (f := fun p : (B × C) × D => G a p.1.1 p.1.2 p.2) (fun p => hK _ _ _ _) q
  have hI : Integrable (Function.uncurry fun (b : B) (c : C) => ∫ d, G a b c d ∂μD) (μB.prod μC) :=
    integrable_bdd hH hHb
  exact integral_integral_swap hI

end Reorder

/-! ### The cube slice, first coordinate outermost -/

def mu (L : ℝ) : Measure ℝ := volume.restrict (Icc 0 L)

instance (L : ℝ) : IsFiniteMeasure (mu L) := by unfold mu; infer_instance

theorem measurable_cons (r : ℕ) : Measurable (fun p : ℝ × (Fin r → ℝ) => (Fin.cons p.1 p.2 : Fin (r + 1) → ℝ)) := by
  refine measurable_pi_iff.2 (fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

theorem cube_slice0 {r : ℕ} {L : ℝ} (hL : 0 ≤ L) (f : (Fin (r + 1) → ℝ) → ℂ)
    (hf : Integrable f (cubeMeasure (r + 1) L)) :
    ∫ x, f x ∂cubeMeasure (r + 1) L = ∫ t, ∫ y, f (Fin.cons t y) ∂cubeMeasure r L ∂mu L := by
  let μ : Measure ℝ := mu L
  haveI : IsFiniteMeasure μ := inferInstance
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) 0).symm
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) 0).symm
  have hi : Integrable (fun p => f (e p)) (μ.prod (Measure.pi (fun _ : Fin r => μ))) := by
    apply (hp.integrable_comp_emb e.measurableEmbedding).mpr
    simpa only [cubeMeasure_eq_pi, μ, mu] using hf
  calc
    _ = ∫ p, f (e p) ∂μ.prod (Measure.pi (fun _ : Fin r => μ)) := by
      simpa only [cubeMeasure_eq_pi, μ, mu] using (hp.integral_comp' f).symm
    _ = ∫ t, ∫ y, f (e (t, y)) ∂Measure.pi (fun _ : Fin r => μ) ∂μ := integral_prod _ hi
    _ = _ := by
      rw [cubeMeasure_eq_pi]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      have he : ∀ y : Fin r → ℝ, e (t, y) = (Fin.cons t y : Fin (r + 1) → ℝ) := fun y =>
        (show e (t, y) = Fin.insertNth 0 t y from rfl).trans (Fin.insertNth_zero' t y)
      simp_rw [he]
      rfl

/-! ### The chamber integral -/

/-- `Jc L r ℓ w = ∫_{x ∈ [0,L]^r} ∫_{y ∈ [0,L]^r} rawPlus ℓ w x y`. -/
def Jc (L : ℝ) (r : ℕ) (ℓ : ℝ) (w : ℂ) : ℂ :=
  ∫ x, ∫ y, rawPlus ℓ w x y ∂cubeMeasure r L ∂cubeMeasure r L

theorem Jc_zero {L : ℝ} (hL : 0 ≤ L) (ℓ : ℝ) (w : ℂ) : Jc L 0 ℓ w = 1 := by
  have hU : Icc (fun _ : Fin 0 => (0 : ℝ)) (fun _ => L) = univ :=
    eq_univ_of_forall (fun x => ⟨fun j => j.elim0, fun j => j.elim0⟩)
  have hc : cubeMeasure 0 L = Measure.dirac (fun j : Fin 0 => (0 : ℝ)) := by
    unfold cubeMeasure
    rw [hU, Measure.restrict_univ]
    have : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac (fun j : Fin 0 => (0 : ℝ)) := by
      rw [volume_pi, Measure.pi_of_empty]
      congr 1; funext j; exact j.elim0
    rw [this]
  unfold Jc
  rw [hc, integral_dirac, integral_dirac]
  unfold rawPlus PlusOrder displacement
  simp

theorem rawPlus_cons (ℓ : ℝ) (w : ℂ) {r : ℕ} (x0 y0 : ℝ) (xt yt : Fin r → ℝ) :
    rawPlus ℓ w (Fin.cons x0 xt : Fin (r + 1) → ℝ) (Fin.cons y0 yt : Fin (r + 1) → ℝ) =
      (if 0 < y0 ∧ y0 < x0 ∧ x0 < ℓ then Complex.exp (Complex.I * w * ((x0 - y0 : ℝ) : ℂ)) else 0) *
        rawPlus y0 w xt yt := by
  classical
  unfold rawPlus
  have hd : displacement (Fin.cons x0 xt : Fin (r + 1) → ℝ) (Fin.cons y0 yt : Fin (r + 1) → ℝ) =
      (x0 - y0) + displacement xt yt := by
    unfold displacement
    rw [Fin.sum_univ_succ]
    simp
  have ho := plusOrder_cons ℓ (Fin.cons x0 xt : Fin (r + 1) → ℝ) (Fin.cons y0 yt : Fin (r + 1) → ℝ)
  simp only [Fin.cons_zero, Fin.tail_cons] at ho
  by_cases h : PlusOrder ℓ (Fin.cons x0 xt : Fin (r + 1) → ℝ) (Fin.cons y0 yt : Fin (r + 1) → ℝ)
  · obtain ⟨h1, h2, h3, h4⟩ := ho.1 h
    rw [if_pos h, if_pos ⟨h1, h2, h3⟩, if_pos h4, hd]
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  · rw [if_neg h]
    by_cases h' : 0 < y0 ∧ y0 < x0 ∧ x0 < ℓ
    · have h4 : ¬ PlusOrder y0 xt yt := fun h4 => h (ho.2 ⟨h'.1, h'.2.1, h'.2.2, h4⟩)
      rw [if_pos h', if_neg h4]; simp
    · rw [if_neg h']; simp

/-! ### The recursion -/

/-- The first-pair weight `A(x₀,y₀) = 1[0<y₀<x₀<ℓ] e^{iw(x₀−y₀)}`. -/
def Aw (ℓ : ℝ) (w : ℂ) (x0 y0 : ℝ) : ℂ :=
  if 0 < y0 ∧ y0 < x0 ∧ x0 < ℓ then Complex.exp (Complex.I * w * ((x0 - y0 : ℝ) : ℂ)) else 0

theorem measurable_Aw (ℓ : ℝ) (w : ℂ) : Measurable (fun p : ℝ × ℝ => Aw ℓ w p.1 p.2) := by
  unfold Aw
  refine Measurable.ite ?_ ?_ measurable_const
  · have h1 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := measurableSet_lt measurable_const measurable_snd
    have h2 : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} := measurableSet_lt measurable_snd measurable_fst
    have h3 : MeasurableSet {p : ℝ × ℝ | p.1 < ℓ} := measurableSet_lt measurable_fst measurable_const
    exact h1.inter (h2.inter h3)
  · exact Complex.continuous_exp.measurable.comp
      ((measurable_const.mul measurable_const).mul (Complex.continuous_ofReal.measurable.comp (measurable_fst.sub measurable_snd)))

theorem norm_Aw_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (w : ℂ) (x0 y0 : ℝ) : ‖Aw ℓ w x0 y0‖ ≤ Real.exp (ℓ * |w.im|) := by
  unfold Aw
  split_ifs with h
  · rw [Complex.norm_exp]
    have : (Complex.I * w * ((x0 - y0 : ℝ) : ℂ)).re = -(w.im * (x0 - y0)) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this]
    refine Real.exp_le_exp.2 ?_
    have h1 : 0 ≤ x0 - y0 := by linarith [h.2.1]
    have h2 : x0 - y0 ≤ ℓ := by linarith [h.1, h.2.2]
    nlinarith [abs_nonneg w.im, neg_abs_le w.im, mul_le_mul_of_nonneg_left h2 (abs_nonneg w.im),
      mul_nonneg (abs_nonneg w.im) h1, le_abs_self w.im, abs_nonneg w.im, mul_nonneg h1 (abs_nonneg w.im)]
  · simp only [norm_zero]; positivity

theorem inner_x0 {L : ℝ} (hL : 0 ≤ L) {ℓ y0 : ℝ} (hy : 0 < y0) (hyℓ : y0 < ℓ) (hℓL : ℓ ≤ L) {w : ℂ} (hw : w ≠ 0) :
    ∫ x0, Aw ℓ w x0 y0 ∂mu L = kk (Complex.I * w) (ℓ - y0) := by
  have hf : (fun x0 => Aw ℓ w x0 y0) = (Ioo y0 ℓ).indicator (fun x0 : ℝ => Complex.exp ((Complex.I * w) * ((x0 - y0 : ℝ) : ℂ))) := by
    funext x0
    unfold Aw
    simp only [Set.indicator_apply, Set.mem_Ioo]
    by_cases h : y0 < x0 ∧ x0 < ℓ
    · rw [if_pos ⟨hy, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  rw [hf, mu, integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hs : Ioo y0 ℓ ∩ Icc 0 L = Ioo y0 ℓ :=
    inter_eq_left.2 (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hyℓ.le]
  have h := intervalIntegral.integral_comp_sub_right (a := y0) (b := ℓ)
    (fun s : ℝ => Complex.exp ((Complex.I * w) * (s : ℂ))) y0
  have hc : Complex.I * w ≠ 0 := mul_ne_zero Complex.I_ne_zero hw
  refine h.trans ?_
  rw [sub_self]
  exact (kk_eq_integral hc _).symm

theorem inner_x0_zero {ℓ y0 : ℝ} (hy : ¬ (0 < y0 ∧ y0 < ℓ)) (w : ℂ) (μ : Measure ℝ) :
    ∫ x0, Aw ℓ w x0 y0 ∂μ = 0 := by
  have : (fun x0 => Aw ℓ w x0 y0) = fun _ => 0 := by
    funext x0
    unfold Aw
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact hy ⟨h1, h2.trans h3⟩
  rw [this]; simp


theorem Jc_succ {L : ℝ} (hL : 0 ≤ L) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L) {w : ℂ} (hw : w ≠ 0) (r : ℕ)
    (ih : ∀ y, 0 ≤ y → y ≤ L → Jc L r y w = Rr (Complex.I * w) r y) :
    Jc L (r + 1) ℓ w = Rr (Complex.I * w) (r + 1) ℓ := by
  set C : Measure (Fin r → ℝ) := cubeMeasure r L with hC
  haveI : IsFiniteMeasure C := by rw [hC]; infer_instance
  set K : ℝ := Real.exp (ℓ * |w.im|) with hK
  have hbd : ∀ (m : ℕ) (x y : Fin m → ℝ), ‖rawPlus ℓ w x y‖ ≤ K := fun m x y => norm_rawPlus_le ℓ hℓ0 w x y
  -- Step A: slices
  have hstepA : Jc L (r + 1) ℓ w = ∫ x0, ∫ xt, ∫ y0, ∫ yt, rawPlus ℓ w (Fin.cons x0 xt : Fin (r + 1) → ℝ)
      (Fin.cons y0 yt : Fin (r + 1) → ℝ) ∂C ∂mu L ∂C ∂mu L := by
    have hint1 : Integrable (fun x : Fin (r + 1) → ℝ => ∫ y, rawPlus ℓ w x y ∂cubeMeasure (r + 1) L)
        (cubeMeasure (r + 1) L) :=
      integrable_param (f := fun p : (Fin (r + 1) → ℝ) × (Fin (r + 1) → ℝ) => rawPlus ℓ w p.1 p.2)
        (measurable_rawPlus (r + 1) ℓ w) (fun p => hbd _ _ _)
    unfold Jc
    refine (cube_slice0 hL _ hint1).trans ?_
    refine integral_congr_ae (Eventually.of_forall fun x0 => integral_congr_ae (Eventually.of_forall fun xt => ?_))
    exact cube_slice0 hL (fun y => rawPlus ℓ w (Fin.cons x0 xt : Fin (r + 1) → ℝ) y)
      (integrable_bdd ((measurable_rawPlus (r + 1) ℓ w).comp (measurable_const.prodMk measurable_id))
        (fun y => hbd _ _ _))
  -- Step B: swap the middle integrals
  have hG : Measurable (fun p : ((ℝ × (Fin r → ℝ)) × ℝ) × (Fin r → ℝ) =>
      rawPlus ℓ w (Fin.cons p.1.1.1 p.1.1.2 : Fin (r + 1) → ℝ) (Fin.cons p.1.2 p.2 : Fin (r + 1) → ℝ)) := by
    have m1 : Measurable (fun p : ((ℝ × (Fin r → ℝ)) × ℝ) × (Fin r → ℝ) => (p.1.1.1, p.1.1.2)) := by fun_prop
    have m2 : Measurable (fun p : ((ℝ × (Fin r → ℝ)) × ℝ) × (Fin r → ℝ) => (p.1.2, p.2)) := by fun_prop
    exact (measurable_rawPlus (r + 1) ℓ w).comp (((measurable_cons r).comp m1).prodMk ((measurable_cons r).comp m2))
  have hstepB := reorder4 (μA := mu L) (μB := C) (μC := mu L) (μD := C)
    (G := fun x0 xt y0 yt => rawPlus ℓ w (Fin.cons x0 xt : Fin (r + 1) → ℝ) (Fin.cons y0 yt : Fin (r + 1) → ℝ)) hG
    (K := K) (fun _ _ _ _ => hbd _ _ _)
  -- Step C: evaluate the tail integral
  have hC' : ∀ x0 y0 : ℝ, ∫ xt, ∫ yt, rawPlus ℓ w (Fin.cons x0 xt : Fin (r + 1) → ℝ)
      (Fin.cons y0 yt : Fin (r + 1) → ℝ) ∂C ∂C = Aw ℓ w x0 y0 * Jc L r y0 w := by
    intro x0 y0
    simp_rw [rawPlus_cons, integral_const_mul]
    rfl
  rw [hstepA, hstepB]
  simp_rw [hC']
  -- replace `Jc` by `Rr` on the support
  have hR : ∀ x0 y0 : ℝ, Aw ℓ w x0 y0 * Jc L r y0 w = Aw ℓ w x0 y0 * Rr (Complex.I * w) r y0 := by
    intro x0 y0
    by_cases h : 0 < y0 ∧ y0 < x0 ∧ x0 < ℓ
    · rw [ih y0 h.1.le (by linarith [h.2.1, h.2.2])]
    · have : Aw ℓ w x0 y0 = 0 := by unfold Aw; rw [if_neg h]
      rw [this]; simp
  simp_rw [hR]
  -- Step D: swap x0 and y0
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := ℓ)).exists_bound_of_continuousOn
    (continuous_Rr (Complex.I * w) r).continuousOn
  have hΦm : Measurable (fun p : ℝ × ℝ => Aw ℓ w p.1 p.2 * Rr (Complex.I * w) r p.2) :=
    (measurable_Aw ℓ w).mul (((continuous_Rr (Complex.I * w) r).measurable).comp measurable_snd)
  have hΦb : ∀ p : ℝ × ℝ, ‖Aw ℓ w p.1 p.2 * Rr (Complex.I * w) r p.2‖ ≤ K * M := by
    intro p
    rw [norm_mul]
    by_cases h : 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < ℓ
    · have hy : p.2 ∈ Icc 0 ℓ := ⟨h.1.le, by linarith [h.2.1, h.2.2]⟩
      exact mul_le_mul (norm_Aw_le hℓ0 w _ _) (hM p.2 hy) (norm_nonneg _) (Real.exp_pos _).le
    · have : Aw ℓ w p.1 p.2 = 0 := by unfold Aw; rw [if_neg h]
      rw [this, norm_zero, zero_mul]
      have h0 : 0 ≤ K * M := by
        have := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hℓ0⟩)
        exact mul_nonneg (Real.exp_pos _).le this
      exact h0
  have hint : Integrable (Function.uncurry fun x0 y0 : ℝ => Aw ℓ w x0 y0 * Rr (Complex.I * w) r y0) ((mu L).prod (mu L)) :=
    integrable_bdd hΦm hΦb
  rw [integral_integral_swap hint]
  -- Step E: integrate out x0
  have hE : ∀ y0 : ℝ, ∫ x0, Aw ℓ w x0 y0 * Rr (Complex.I * w) r y0 ∂mu L =
      (Ioo 0 ℓ).indicator (fun y => Rr (Complex.I * w) r y * kk (Complex.I * w) (ℓ - y)) y0 := by
    intro y0
    rw [integral_mul_const]
    by_cases h : y0 ∈ Ioo 0 ℓ
    · rw [Set.indicator_of_mem h, inner_x0 hL h.1 h.2 hℓL hw]; ring
    · rw [Set.indicator_of_notMem h, inner_x0_zero (fun h' => h h') w]; simp
  simp_rw [hE]
  rw [integral_indicator measurableSet_Ioo, mu, Measure.restrict_restrict measurableSet_Ioo]
  have hs : Ioo 0 ℓ ∩ Icc 0 L = Ioo 0 ℓ :=
    inter_eq_left.2 (fun x hx => ⟨hx.1.le, by linarith [hx.2]⟩)
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hℓ0]
  rfl

theorem Jc_eq_Rr {L : ℝ} (hL : 0 ≤ L) {w : ℂ} (hw : w ≠ 0) (r : ℕ) :
    ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ L → Jc L r ℓ w = Rr (Complex.I * w) r ℓ := by
  induction r with
  | zero => intro ℓ _ _; rw [Jc_zero hL]; rfl
  | succ r ih => intro ℓ h0 h1; exact Jc_succ hL h0 h1 hw r ih

end QuantumNLS.PlaneWaveChamber

#print axioms QuantumNLS.PlaneWaveChamber.cube_slice0
#print axioms QuantumNLS.PlaneWaveChamber.Jc_zero
#print axioms QuantumNLS.PlaneWaveChamber.rawPlus_cons
#print axioms QuantumNLS.PlaneWaveChamber.inner_x0
#print axioms QuantumNLS.PlaneWaveChamber.Jc_eq_Rr
