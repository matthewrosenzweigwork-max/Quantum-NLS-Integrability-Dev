import Mathlib
import QuantumNLS.BetheTransferOperators

/-!
# Alternating-chamber integrals as iterated interval integrals

New module (R-7E0532E7 `eq:root-trace-symbol`, ordered-kernel / Dyson identification).  Pure measure theory, no quantum input.

For measurable `f g : ℝ → ℂ`, interval integrable on `[0,L]`, and `c : ℂ`, put (pairs `p_j = (x_j,y_j)`)

* `Phi f g c r ℓ p = 1_{PlusOrder ℓ x y} · ∏_j f(x_j) g(y_j) e^{ic(x_j - y_j)}`   (the integrand of the printed kernel `K̃⁺_{r,c}`
  after `Fin r → ℝ × ℝ ≃ (Fin r → ℝ)²`, with `PlusOrder` the frozen strict alternating chamber `ℓ > x₁ > y₁ > ⋯ > x_r > y_r > 0`),
* `Wr f g c r ℓ` the iterated integral `Wr 0 ℓ = 1`,
  `Wr (r+1) ℓ = ∫₀^ℓ f(x) e^{icx} ∫₀^x g(y) e^{-icy} Wr r y dy dx`.

**`Theta_eq_Wr`**: for `0 ≤ ℓ ≤ L`, the Lebesgue integral of `Phi f g c r ℓ` over `Fin r → ℝ × ℝ` equals `Wr f g c r ℓ`.
Proof: `plusOrder_cons` (peeling the first pair), the measure-preserving equivalence `piFinSuccAbove`, Fubini once per level;
integrability from the single domination `‖Phi‖ ≤ e^{|Im c| L} ∏_j |f|1_{(0,L)}(x_j) |g|1_{(0,L)}(y_j)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter
open scoped Interval

namespace QuantumNLS.RootChamberIntegral

open QuantumNLS.BetheTransferKernelAdjoint (PlusOrder plusOrder_cons displacement)

section Defs

variable (f g : ℝ → ℂ) (c : ℂ)

/-- Iterated interval integral of the alternating chamber. -/
def Wr : ℕ → ℝ → ℂ
  | 0, _ => 1
  | r + 1, ℓ => ∫ x in (0 : ℝ)..ℓ, f x * Complex.exp (Complex.I * c * x) *
      ∫ y in (0 : ℝ)..x, g y * Complex.exp (-(Complex.I * c * y)) * Wr r y

open Classical in
/-- The chamber integrand on pairs. -/
def Phi (r : ℕ) (ℓ : ℝ) (p : Fin r → ℝ × ℝ) : ℂ :=
  (if PlusOrder ℓ (fun j => (p j).1) (fun j => (p j).2) then (1 : ℂ) else 0) *
    ∏ j, (f (p j).1 * g (p j).2 * Complex.exp (Complex.I * c * (((p j).1 - (p j).2 : ℝ) : ℂ)))

/-- The integral of the chamber integrand over `Fin r → ℝ × ℝ`. -/
def Theta (r : ℕ) (ℓ : ℝ) : ℂ := ∫ p : Fin r → ℝ × ℝ, Phi f g c r ℓ p

theorem exp_sub_split (c : ℂ) (a b : ℝ) :
    Complex.exp (Complex.I * c * ((a - b : ℝ) : ℂ)) =
      Complex.exp (Complex.I * c * a) * Complex.exp (-(Complex.I * c * b)) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

open Classical in
theorem Phi_cons (r : ℕ) (ℓ a b : ℝ) (q : Fin r → ℝ × ℝ) :
    Phi f g c (r + 1) ℓ (Fin.cons (a, b) q) =
      (if 0 < b ∧ b < a ∧ a < ℓ then f a * g b * Complex.exp (Complex.I * c * ((a - b : ℝ) : ℂ)) else 0) *
        Phi f g c r b q := by
  unfold Phi
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have h : PlusOrder ℓ (fun j : Fin (r + 1) => ((Fin.cons (a, b) q : Fin (r + 1) → ℝ × ℝ) j).1)
      (fun j => ((Fin.cons (a, b) q : Fin (r + 1) → ℝ × ℝ) j).2) ↔
      (0 < b ∧ b < a ∧ a < ℓ) ∧ PlusOrder b (fun j => (q j).1) (fun j => (q j).2) := by
    have e1 : (Fin.tail fun j : Fin (r + 1) => ((Fin.cons (a, b) q : Fin (r + 1) → ℝ × ℝ) j).1) =
        fun j => (q j).1 := by funext j; simp [Fin.tail]
    have e2 : (Fin.tail fun j : Fin (r + 1) => ((Fin.cons (a, b) q : Fin (r + 1) → ℝ × ℝ) j).2) =
        fun j => (q j).2 := by funext j; simp [Fin.tail]
    rw [plusOrder_cons, e1, e2]
    simp only [Fin.cons_zero, and_assoc]
  by_cases h1 : 0 < b ∧ b < a ∧ a < ℓ <;> by_cases h2 : PlusOrder b (fun j => (q j).1) (fun j => (q j).2) <;>
    simp [h, h1, h2, mul_assoc]

end Defs

section Integrability

variable {f g : ℝ → ℂ} {c : ℂ}

theorem measurable_Phi (hf : Measurable f) (hg : Measurable g) (r : ℕ) (ℓ : ℝ) :
    Measurable (Phi f g c r ℓ) := by
  classical
  unfold Phi
  refine Measurable.mul ?_ ?_
  · have hm : Measurable (fun p : Fin r → ℝ × ℝ => ((fun j => (p j).1), (fun j => (p j).2))) :=
      Measurable.prodMk (measurable_pi_iff.2 (fun j => (measurable_pi_apply j).fst))
        (measurable_pi_iff.2 (fun j => (measurable_pi_apply j).snd))
    have hs := (QuantumNLS.BetheTransferOperators.measurableSet_plusOrder r ℓ).preimage hm
    exact Measurable.ite hs measurable_const measurable_const
  · refine Finset.measurable_prod _ (fun j _ => ?_)
    have h1 : Measurable (fun p : Fin r → ℝ × ℝ => (p j).1) := (measurable_pi_apply j).fst
    have h2 : Measurable (fun p : Fin r → ℝ × ℝ => (p j).2) := (measurable_pi_apply j).snd
    refine ((hf.comp h1).mul (hg.comp h2)).mul ?_
    exact Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp (h1.sub h2)))

/-- Single domination of the chamber integrand. -/
theorem integrable_Phi (hf : Measurable f) (hg : Measurable g) {L : ℝ} (hfi : IntervalIntegrable f volume 0 L)
    (hgi : IntervalIntegrable g volume 0 L) (hL : 0 ≤ L) (r : ℕ) {ℓ : ℝ} (h0 : 0 ≤ ℓ) (hℓ : ℓ ≤ L) :
    Integrable (Phi f g c r ℓ) (volume : Measure (Fin r → ℝ × ℝ)) := by
  classical
  set ft : ℝ → ℝ := (Ioo (0 : ℝ) L).indicator (fun x => ‖f x‖) with hft
  set gt : ℝ → ℝ := (Ioo (0 : ℝ) L).indicator (fun x => ‖g x‖) with hgt
  have hfti : Integrable ft volume := by
    have h1 : IntegrableOn (fun x => ‖f x‖) (Ioc (0 : ℝ) L) volume :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL).1 hfi).norm
    exact (integrable_indicator_iff measurableSet_Ioo).2 (h1.mono_set Ioo_subset_Ioc_self)
  have hgti : Integrable gt volume := by
    have h1 : IntegrableOn (fun x => ‖g x‖) (Ioc (0 : ℝ) L) volume :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL).1 hgi).norm
    exact (integrable_indicator_iff measurableSet_Ioo).2 (h1.mono_set Ioo_subset_Ioc_self)
  have hk : Integrable (fun z : ℝ × ℝ => ft z.1 * gt z.2) (volume : Measure (ℝ × ℝ)) :=
    hfti.mul_prod hgti
  have hprod : Integrable (fun p : Fin r → ℝ × ℝ => ∏ j, (ft (p j).1 * gt (p j).2))
      (volume : Measure (Fin r → ℝ × ℝ)) :=
    Integrable.fintype_prod (f := fun (_ : Fin r) (z : ℝ × ℝ) => ft z.1 * gt z.2) (fun _ => hk)
  have hdom := hprod.const_mul (Real.exp (|c.im| * L))
  refine hdom.mono' (measurable_Phi hf hg r ℓ).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  by_cases hP : PlusOrder ℓ (fun j => (p j).1) (fun j => (p j).2)
  · have hmem : ∀ j, (p j).1 ∈ Ioo (0 : ℝ) L ∧ (p j).2 ∈ Ioo (0 : ℝ) L := by
      intro j
      obtain ⟨h1, h2, h3⟩ := hP.1 j
      exact ⟨⟨h1.trans h2, h3.trans_le hℓ⟩, ⟨h1, (h2.trans h3).trans_le hℓ⟩⟩
    have hdisp := QuantumNLS.BetheTransferOperators.displacement_range h0 hP
    have hphase : ‖∏ j, Complex.exp (Complex.I * c * (((p j).1 - (p j).2 : ℝ) : ℂ))‖ ≤
        Real.exp (|c.im| * L) := by
      have hs : ∏ j, Complex.exp (Complex.I * c * (((p j).1 - (p j).2 : ℝ) : ℂ)) =
          Complex.exp (Complex.I * c * ((displacement (fun j => (p j).1) (fun j => (p j).2) : ℝ) : ℂ)) := by
        rw [← Complex.exp_sum]
        congr 1
        simp only [displacement, Complex.ofReal_sum, Finset.mul_sum]
      rw [hs]
      have := QuantumNLS.BetheTransferOperators.norm_phase_le L c hdisp.1 (hdisp.2.trans hℓ)
      rwa [mul_comm L] at this
    simp only [Phi, hP, ↓reduceIte, one_mul]
    rw [norm_prod]
    have hsplit : ∏ j, ‖f (p j).1 * g (p j).2 * Complex.exp (Complex.I * c * (((p j).1 - (p j).2 : ℝ) : ℂ))‖ =
        (∏ j, (ft (p j).1 * gt (p j).2)) *
          ‖∏ j, Complex.exp (Complex.I * c * (((p j).1 - (p j).2 : ℝ) : ℂ))‖ := by
      rw [norm_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [norm_mul, norm_mul]
      simp only [hft, hgt, Set.indicator_of_mem (hmem j).1, Set.indicator_of_mem (hmem j).2]
    have hp0 : 0 ≤ ∏ j, (ft (p j).1 * gt (p j).2) := Finset.prod_nonneg (fun j _ => by
      refine mul_nonneg ?_ ?_ <;> exact Set.indicator_nonneg (fun x _ => norm_nonneg _) _)
    calc _ = (∏ j, (ft (p j).1 * gt (p j).2)) *
          ‖∏ j, Complex.exp (Complex.I * c * (((p j).1 - (p j).2 : ℝ) : ℂ))‖ := hsplit
      _ ≤ (∏ j, (ft (p j).1 * gt (p j).2)) * Real.exp (|c.im| * L) :=
          mul_le_mul_of_nonneg_left hphase hp0
      _ = _ := mul_comm _ _
  · simp only [Phi, hP, ↓reduceIte, zero_mul, norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun j _ => by
      refine mul_nonneg ?_ ?_ <;> exact Set.indicator_nonneg (fun x _ => norm_nonneg _) _))

end Integrability

section Recursion

variable {f g : ℝ → ℂ} {c : ℂ}

theorem Theta_zero (ℓ : ℝ) : Theta f g c 0 ℓ = 1 := by
  classical
  have hP : PlusOrder ℓ (fun j : Fin 0 => ((fun j : Fin 0 => ((0 : ℝ), (0 : ℝ))) j).1)
      (fun j : Fin 0 => ((fun j : Fin 0 => ((0 : ℝ), (0 : ℝ))) j).2) := ⟨fun j => j.elim0, fun i => i.elim0⟩
  unfold Theta
  have : ∀ p : Fin 0 → ℝ × ℝ, Phi f g c 0 ℓ p = 1 := by
    intro p
    have hP' : PlusOrder ℓ (fun j : Fin 0 => (p j).1) (fun j : Fin 0 => (p j).2) :=
      ⟨fun j => j.elim0, fun i => i.elim0⟩
    simp [Phi, hP']
  simp_rw [this]
  have hv : (volume : Measure (Fin 0 → ℝ × ℝ)) = Measure.dirac (fun j => j.elim0) := Measure.pi_of_empty _ _
  rw [hv]
  simp

theorem Theta_eq_Wr (hf : Measurable f) (hg : Measurable g) {L : ℝ} (hfi : IntervalIntegrable f volume 0 L)
    (hgi : IntervalIntegrable g volume 0 L) (hL : 0 ≤ L) :
    ∀ r : ℕ, ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ L → Theta f g c r ℓ = Wr f g c r ℓ := by
  classical
  intro r
  induction r with
  | zero => intro ℓ _ _; rw [Theta_zero]; rfl
  | succ r ih =>
    intro ℓ h0 hℓ
    have hΦ := integrable_Phi (c := c) hf hg hfi hgi hL (r + 1) h0 hℓ
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ × ℝ) 0).symm
    have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => ℝ × ℝ) 0).symm
    have he : ∀ w : (ℝ × ℝ) × (Fin r → ℝ × ℝ), e w = Fin.cons w.1 w.2 := by
      intro w
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    have hint : Integrable (fun w : (ℝ × ℝ) × (Fin r → ℝ × ℝ) => Phi f g c (r + 1) ℓ (e w)) volume :=
      (hmp.integrable_comp_emb e.measurableEmbedding).2 hΦ
    have h1 : Theta f g c (r + 1) ℓ = ∫ w : (ℝ × ℝ) × (Fin r → ℝ × ℝ), Phi f g c (r + 1) ℓ (e w) :=
      (hmp.integral_comp' (Phi f g c (r + 1) ℓ)).symm
    set K : ℝ × ℝ → ℂ := fun ab => if 0 < ab.2 ∧ ab.2 < ab.1 ∧ ab.1 < ℓ then
      f ab.1 * g ab.2 * Complex.exp (Complex.I * c * ((ab.1 - ab.2 : ℝ) : ℂ)) else 0 with hKdef
    have hcons : ∀ w : (ℝ × ℝ) × (Fin r → ℝ × ℝ),
        Phi f g c (r + 1) ℓ (e w) = K w.1 * Phi f g c r w.1.2 w.2 := by
      intro w
      rw [he]
      exact Phi_cons f g c r ℓ w.1.1 w.1.2 w.2
    have hint' : Integrable (fun w : (ℝ × ℝ) × (Fin r → ℝ × ℝ) => K w.1 * Phi f g c r w.1.2 w.2) volume :=
      hint.congr (Eventually.of_forall hcons)
    have h2 : Theta f g c (r + 1) ℓ = ∫ ab : ℝ × ℝ, K ab * Theta f g c r ab.2 := by
      rw [h1]
      simp_rw [hcons]
      rw [Measure.volume_eq_prod, integral_prod _ (by simpa [Measure.volume_eq_prod] using hint')]
      refine integral_congr_ae (Eventually.of_forall fun ab => ?_)
      simp only [Theta]
      rw [integral_const_mul]
    have hint2 : Integrable (fun ab : ℝ × ℝ => K ab * Theta f g c r ab.2) volume := by
      have := (by simpa [Measure.volume_eq_prod] using hint' :
        Integrable (fun w : (ℝ × ℝ) × (Fin r → ℝ × ℝ) => K w.1 * Phi f g c r w.1.2 w.2)
          ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (Fin r → ℝ × ℝ)))).integral_prod_left
      refine this.congr (Eventually.of_forall fun ab => ?_)
      simp only [Theta]
      rw [integral_const_mul]
    have hK : ∀ ab : ℝ × ℝ, K ab * Theta f g c r ab.2 = K ab * Wr f g c r ab.2 := by
      intro ab
      by_cases hc : 0 < ab.2 ∧ ab.2 < ab.1 ∧ ab.1 < ℓ
      · rw [ih ab.2 hc.1.le (by linarith [hc.2.1, hc.2.2])]
      · simp [hKdef, hc]
    simp_rw [hK] at h2 hint2
    -- iterated integral
    have hinner : ∀ a : ℝ, ∫ b : ℝ, K (a, b) * Wr f g c r b =
        (Ioo (0 : ℝ) ℓ).indicator (fun a => f a * Complex.exp (Complex.I * c * a) *
          ∫ y in (0 : ℝ)..a, g y * Complex.exp (-(Complex.I * c * y)) * Wr f g c r y) a := by
      intro a
      by_cases ha : a ∈ Ioo (0 : ℝ) ℓ
      · rw [Set.indicator_of_mem ha]
        have hpt : ∀ b : ℝ, K (a, b) * Wr f g c r b = (Ioo (0 : ℝ) a).indicator
            (fun b => (f a * Complex.exp (Complex.I * c * a)) *
              (g b * Complex.exp (-(Complex.I * c * b)) * Wr f g c r b)) b := by
          intro b
          by_cases hb : b ∈ Ioo (0 : ℝ) a
          · rw [Set.indicator_of_mem hb]
            have : 0 < b ∧ b < a ∧ a < ℓ := ⟨hb.1, hb.2, ha.2⟩
            simp only [hKdef, this, and_self, ↓reduceIte]
            rw [exp_sub_split]; ring
          · rw [Set.indicator_of_notMem hb]
            have : ¬ (0 < b ∧ b < a ∧ a < ℓ) := fun h => hb ⟨h.1, h.2.1⟩
            simp [hKdef, this]
        simp_rw [hpt]
        rw [integral_indicator measurableSet_Ioo, integral_const_mul,
          intervalIntegral.integral_of_le ha.1.le, integral_Ioc_eq_integral_Ioo]
      · rw [Set.indicator_of_notMem ha]
        have : ∀ b : ℝ, K (a, b) * Wr f g c r b = 0 := by
          intro b
          have : ¬ (0 < b ∧ b < a ∧ a < ℓ) := fun h => ha ⟨h.1.trans h.2.1, h.2.2⟩
          simp [hKdef, this]
        simp_rw [this]
        simp
    rw [h2, Measure.volume_eq_prod, integral_prod _ (by simpa [Measure.volume_eq_prod] using hint2)]
    simp_rw [hinner]
    rw [integral_indicator measurableSet_Ioo]
    show _ = ∫ x in (0 : ℝ)..ℓ, f x * Complex.exp (Complex.I * c * x) *
      ∫ y in (0 : ℝ)..x, g y * Complex.exp (-(Complex.I * c * y)) * Wr f g c r y
    rw [intervalIntegral.integral_of_le h0, integral_Ioc_eq_integral_Ioo]

end Recursion

end QuantumNLS.RootChamberIntegral

#print axioms QuantumNLS.RootChamberIntegral.integrable_Phi
#print axioms QuantumNLS.RootChamberIntegral.Theta_zero
#print axioms QuantumNLS.RootChamberIntegral.Theta_eq_Wr
