import Mathlib
import QuantumNLS.Loss
import QuantumNLS.SobolevSpaces

/-!
# R-8C922B25 `lem:loss`, the "in particular" clause: the Sobolev scales `h^s`, `H^s` (DEF-002) and `f : ℓ² → L²` real analytic

Printed: "In particular, if `f : ℓ² → L²` is real analytic and its restriction `h^S → H^S` is continuous, then `f : h^S → H^q` is `C^k` for `S > (k+1)q`.  The analogous
statement holds with physical and sequence spaces interchanged.  All bounds can be chosen uniformly near a fixed compact subset of `h^S`."

* `holder_weighted` (ROOT-01: "Hölder applied to the coefficient square sum proves interpolation, with precisely the source exponents"):
  `Σ w^θ a ≤ (Σ a)^{1−θ} (Σ w a)^θ`;
* `h02_interp`: `‖y‖_{h^q} ≤ ‖y‖_{h^0}^{1−q/S} ‖y‖_{h^S}^{q/S}` for the DEF-002 weights `(1+|2πn/L|)^{2s}` (`Sobolev.h02`, realized in `SobolevSpaces`);
* `seqScale L`: the scale `Y s = h^s(ℤ)` (real Banach by restriction of scalars; the inclusions `h02_mono` are injective);
* `loss_seq` / `loss_seq_uniform`: the lemma for `f : h^0 → h^0` real analytic (`AnalyticOnNhd ℝ`) whose restriction `g : h^S → h^S` is continuous;
* `fieldScale L`: the physical scale `H^s(𝕋_L)` through the Fourier unitary of `SobolevSpaces` (`WField`, `toSeq`, `fieldIncl`), and `loss_field`
  (sequence and physical spaces interchanged).
ROOT-01 is the instance FIN-EXT025-ROOT-01 (Parseval, Sobolev interpolation); it is used here only through the weighted sequence form proved below, no owner-held contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
open scoped NNReal ContDiff
open Filter Topology Set Metric
noncomputable section
namespace QuantumNLS.LossSobolev

open QuantumNLS.Sobolev QuantumNLS.Loss

theorem holder_weighted {ι : Type*} (a w : ι → ℝ) (ha : ∀ n, 0 ≤ a n) (hw : ∀ n, 0 < w n) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hs : Summable a) (hsw : Summable (fun n => w n * a n)) :
    Summable (fun n => w n ^ θ * a n) ∧
      ∑' n, w n ^ θ * a n ≤ (∑' n, a n) ^ (1 - θ) * (∑' n, w n * a n) ^ θ := by
  have hpq : Real.HolderConjugate (1 - θ)⁻¹ θ⁻¹ := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [one_lt_inv₀ (by linarith)]; linarith
    · rw [inv_inv, inv_inv]; ring
  have hf : ∀ n, 0 ≤ a n ^ (1 - θ) := fun n => Real.rpow_nonneg (ha n) _
  have hg : ∀ n, 0 ≤ (w n * a n) ^ θ := fun n => Real.rpow_nonneg (mul_nonneg (hw n).le (ha n)) _
  have hfp : ∀ n, (a n ^ (1 - θ)) ^ (1 - θ)⁻¹ = a n := fun n => by
    rw [← Real.rpow_mul (ha n), mul_inv_cancel₀ (by linarith), Real.rpow_one]
  have hgq : ∀ n, ((w n * a n) ^ θ) ^ θ⁻¹ = w n * a n := fun n => by
    rw [← Real.rpow_mul (mul_nonneg (hw n).le (ha n)), mul_inv_cancel₀ hθ0.ne', Real.rpow_one]
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg (by simpa [hfp] using hs)
    (by simpa [hgq] using hsw)
  have e : ∀ n, a n ^ (1 - θ) * (w n * a n) ^ θ = w n ^ θ * a n := fun n => by
    rw [Real.mul_rpow (hw n).le (ha n)]
    have : a n ^ (1 - θ) * a n ^ θ = a n := by
      rw [← Real.rpow_add' (ha n) (by linarith)]; simp
    calc a n ^ (1 - θ) * (w n ^ θ * a n ^ θ) = w n ^ θ * (a n ^ (1 - θ) * a n ^ θ) := by ring
      _ = _ := by rw [this]
  simp only [e, hfp, hgq] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  rw [one_div, inv_inv, one_div, inv_inv]

/-- The weight identity `w_q = w_S^{q/S}` for the DEF-002 weights. -/
theorem sobolevWeight_rpow (L : ℝ) {q S : ℝ} (hS : 0 < S) (n : ℤ) :
    QuantumNLS.Fourier.sobolevWeight L q n = QuantumNLS.Fourier.sobolevWeight L S n ^ (q / S) := by
  unfold QuantumNLS.Fourier.sobolevWeight
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  field_simp

theorem h02_val (L : ℝ) {s t : ℝ} (hst : s ≤ t) (x : h02 L t) : (h02_mono L hst x).val = x.val := rfl

theorem sq_rpow' (x c : ℝ) (hx : 0 ≤ x) : (x ^ 2) ^ c = (x ^ c) ^ 2 := by
  calc (x ^ 2) ^ c = (x ^ (2 : ℝ)) ^ c := by rw [Real.rpow_two]
    _ = x ^ (2 * c) := (Real.rpow_mul hx 2 c).symm
    _ = x ^ (c * 2) := by rw [mul_comm]
    _ = (x ^ c) ^ (2 : ℝ) := Real.rpow_mul hx c 2
    _ = (x ^ c) ^ 2 := Real.rpow_two _

/-- **Interpolation for the DEF-002 scale** (the printed inequality with exponent `q/S`). -/
theorem h02_interp (L : ℝ) {q S : ℝ} (hq : 0 < q) (hqS : q < S) (y : h02 L S) :
    ‖h02_mono L hqS.le y‖ ≤ ‖h02_mono L (by linarith : (0 : ℝ) ≤ S) y‖ ^ (1 - q / S) * ‖y‖ ^ (q / S) := by
  have hS : 0 < S := hq.trans hqS
  set θ : ℝ := q / S with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one hS]; exact hqS
  set a : ℤ → ℝ := fun n => ‖y.val n‖ ^ 2 with ha
  set w : ℤ → ℝ := fun n => QuantumNLS.Fourier.sobolevWeight L S n with hw
  have ha0 : ∀ n, 0 ≤ a n := fun n => sq_nonneg _
  have hwpos : ∀ n, 0 < w n := fun n => QuantumNLS.Fourier.sobolevWeight_pos L S n
  have hnS : ‖y‖ ^ 2 = ∑' n, w n * a n := by rw [h02_norm_sq]; rfl
  have hsw : Summable (fun n => w n * a n) := y.summable
  have h0 : ∀ n, QuantumNLS.Fourier.sobolevWeight L 0 n = 1 := fun n => by
    simp [QuantumNLS.Fourier.sobolevWeight]
  have hn0 : ‖h02_mono L (by linarith : (0 : ℝ) ≤ S) y‖ ^ 2 = ∑' n, a n := by
    rw [h02_norm_sq]
    unfold QuantumNLS.Fourier.hsNormSq
    simp only [h02_val, one_mul, h0]
    rfl
  have hsa : Summable a := by
    have h1 := (h02_mono L (by linarith : (0 : ℝ) ≤ S) y).summable
    refine h1.congr (fun n => ?_)
    show (def002 L 0).w n * ‖(h02_mono L (by linarith : (0 : ℝ) ≤ S) y).val n‖ ^ 2 = ‖y.val n‖ ^ 2
    rw [show (def002 L 0).w n = 1 from h0 n, one_mul]
    rfl
  have hnq : ‖h02_mono L hqS.le y‖ ^ 2 = ∑' n, w n ^ θ * a n := by
    rw [h02_norm_sq]
    unfold QuantumNLS.Fourier.hsNormSq
    simp only [h02_val]
    refine tsum_congr (fun n => ?_)
    rw [sobolevWeight_rpow L hS n]
  have hH := holder_weighted a w ha0 hwpos hθ0 hθ1 hsa hsw
  have hE : ‖h02_mono L hqS.le y‖ ^ 2 ≤
      (‖h02_mono L (by linarith : (0 : ℝ) ≤ S) y‖ ^ 2) ^ (1 - θ) * (‖y‖ ^ 2) ^ θ := by
    rw [hnq, hn0, hnS]; exact hH.2
  have h2 : ‖h02_mono L hqS.le y‖ ^ 2 ≤
      (‖h02_mono L (by linarith : (0 : ℝ) ≤ S) y‖ ^ (1 - θ) * ‖y‖ ^ θ) ^ 2 := by
    rw [mul_pow, ← sq_rpow' _ _ (norm_nonneg _), ← sq_rpow' _ _ (norm_nonneg _)]; exact hE
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- The DEF-002 sequence scale `Y s = h^s(ℤ)` (real Banach spaces by restriction of scalars; inclusions `h02_mono`). -/
def seqScale (L : ℝ) : InterpScale where
  Y s := h02 L (s : ℝ)
  instN := fun _ => inferInstance
  instS := fun _ => inferInstance
  instC := fun _ => inferInstance
  emb s t h := (h02_mono L (by exact_mod_cast h : ((t : ℝ≥0) : ℝ) ≤ (s : ℝ))).restrictScalars ℝ
  emb_inj s t h := by
    intro a b hab
    apply PosWeight.WSeq.ext
    have := congrArg (fun z => (z : h02 L (t : ℝ)).val) hab
    simpa [h02_val] using this
  emb_comp s t r h1 h2 y := PosWeight.WSeq.ext rfl
  interp q S hq hqS y := by
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hqS' : (q : ℝ) < S := by exact_mod_cast hqS
    exact h02_interp L hq' hqS' y

/-- **`lem:loss`, "in particular", general form.**  `f : X₀ → Y⁰` real analytic, `ι : X' → X₀` bounded linear, and `g : X' → Y^S` continuous with `emb S 0 ∘ g = f ∘ ι`
(the restriction of `f` is continuous into the stronger space): then `emb S q ∘ g : X' → Y^q` is `C^k` for `S > (k+1)q`, its derivatives are those of `f ∘ ι` in `Y⁰`,
and the bounds are uniform near every compact subset of `X'`. -/
theorem loss_analytic (𝒴 : InterpScale) {X' X0 : Type*} [NormedAddCommGroup X'] [NormedSpace ℝ X'] [CompleteSpace X']
    [NormedAddCommGroup X0] [NormedSpace ℝ X0] (ι : X' →L[ℝ] X0) {k : ℕ} (hk : 1 ≤ k) {q S : ℝ≥0} (hq : 0 < q)
    (hS : ((k : ℝ) + 1) * q < S) (hqS : q ≤ S) (f : X0 → 𝒴.Y 0) (hf : AnalyticOnNhd ℝ f univ)
    (g : X' → 𝒴.Y S) (hg : Continuous g) (hres : ∀ x, 𝒴.emb S 0 (nn_zero_le S) (g x) = f (ι x)) :
    ContDiff ℝ ((k : ℕ) : ℕ∞ω) (fun x => 𝒴.emb S q hqS (g x)) ∧
      (∀ j ≤ k, ∀ x v, 𝒴.emb q 0 (nn_zero_le q) (iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x v) =
        iteratedFDeriv ℝ j (fun x => f (ι x)) x v) ∧
      ∀ K : Set X', IsCompact K → ∃ V : Set X', IsOpen V ∧ K ⊆ V ∧ ∃ B : ℝ,
        ∀ x ∈ V, ∀ j ≤ k, ‖iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x‖ ≤ B := by
  have hfC : ContDiff ℝ ((k + 1 : ℕ) : ℕ∞ω) f := contDiffOn_univ.1 (hf.contDiffOn uniqueDiffOn_univ)
  have hf' : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) (fun x => f (ι x)) univ := (hfC.comp ι.contDiff).contDiffOn
  have hloc : ∀ x ∈ (univ : Set X'), ∃ r > 0, ∃ M : ℝ, ∀ y ∈ (univ : Set X'), dist y x < r → ‖g y‖ ≤ M := by
    intro x _
    obtain ⟨r, hr, h⟩ := Metric.continuous_iff.1 hg x 1 one_pos
    refine ⟨r, hr, ‖g x‖ + 1, fun y _ hy => ?_⟩
    have := h y hy
    rw [dist_eq_norm] at this
    calc ‖g y‖ = ‖(g y - g x) + g x‖ := by rw [sub_add_cancel]
      _ ≤ ‖g y - g x‖ + ‖g x‖ := norm_add_le _ _
      _ ≤ ‖g x‖ + 1 := by linarith
  have hmain := loss 𝒴 isOpen_univ hk hq hS hqS (fun x => f (ι x)) hf' g (fun x _ => (hres x).symm) hloc
  refine ⟨contDiffOn_univ.1 hmain.1, fun j hj x v => hmain.2.1 j hj x (mem_univ x) v, fun K hK => ?_⟩
  exact loss_uniform 𝒴 isOpen_univ hk hq hS hqS _ hf' g (fun x _ => (hres x).symm) hloc hK (subset_univ K)

section Field

variable (L : ℝ) [Fact (0 < L)]

theorem toSeq_fieldIncl {s t : ℝ} (hst : s ≤ t) (u : H02 L t) :
    toSeq L (def002 L s) (fieldIncl (def002 L s) (def002 L t) zero_le_one (def002_le_of_le L hst) u) =
      h02_mono L hst (toSeq L (def002 L t) u) := PosWeight.WSeq.ext rfl

/-- The physical DEF-002 scale `Y s = H^s(𝕋_L)` (Fourier unitary `toSeq`, identity inclusions). -/
def fieldScale : InterpScale where
  Y s := H02 L (s : ℝ)
  instN := fun _ => inferInstance
  instS := fun _ => inferInstance
  instC := fun s => WField.completeSpace (one_le_def002 L (NNReal.coe_nonneg s))
  emb s t h := (fieldIncl (def002 L (t : ℝ)) (def002 L (s : ℝ)) zero_le_one
    (def002_le_of_le L (by exact_mod_cast h : ((t : ℝ≥0) : ℝ) ≤ (s : ℝ)))).restrictScalars ℝ
  emb_inj s t h := by
    intro a b hab
    apply WField.ext
    have := congrArg (fun z => (z : H02 L (t : ℝ)).val) hab
    simpa using this
  emb_comp s t r h1 h2 y := WField.ext rfl
  interp q S hq hqS y := by
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hqS' : (q : ℝ) < S := by exact_mod_cast hqS
    have h := h02_interp L hq' hqS' (toSeq L (def002 L (S : ℝ)) y)
    have e1 : ∀ (t : ℝ) (ht : t ≤ S), ‖fieldIncl (def002 L t) (def002 L (S : ℝ)) zero_le_one
        (def002_le_of_le L ht) y‖ = ‖h02_mono L ht (toSeq L (def002 L (S : ℝ)) y)‖ := fun t ht => by
      rw [WField.norm_def, toSeq_fieldIncl]
    have e3 : ‖y‖ = ‖toSeq L (def002 L (S : ℝ)) y‖ := WField.norm_def L y
    show ‖fieldIncl (def002 L (q : ℝ)) (def002 L (S : ℝ)) zero_le_one (def002_le_of_le L hqS'.le) y‖ ≤
      ‖fieldIncl (def002 L ((0 : ℝ≥0) : ℝ)) (def002 L (S : ℝ)) zero_le_one
        (def002_le_of_le L (by exact_mod_cast nn_zero_le S)) y‖ ^ (1 - (q : ℝ) / S) * ‖y‖ ^ ((q : ℝ) / S)
    rw [e1 (q : ℝ) hqS'.le, e1 ((0 : ℝ≥0) : ℝ) (by exact_mod_cast nn_zero_le S), e3]
    exact h

end Field

/-- **`lem:loss`, "in particular" (printed: `f : ℓ² → L²` real analytic, restriction `h^S → H^S` continuous ⇒ `f : h^S → H^q` is `C^k`).** -/
theorem loss_h_to_H (L : ℝ) [Fact (0 < L)] {k : ℕ} (hk : 1 ≤ k) {q S : ℝ≥0} (hq : 0 < q)
    (hS : ((k : ℝ) + 1) * q < S) (hqS : q ≤ S)
    (f : (seqScale L).Y 0 → (fieldScale L).Y 0) (hf : AnalyticOnNhd ℝ f univ)
    (g : (seqScale L).Y S → (fieldScale L).Y S) (hg : Continuous g)
    (hres : ∀ x, (fieldScale L).emb S 0 (nn_zero_le S) (g x) = f ((seqScale L).emb S 0 (nn_zero_le S) x)) :
    ContDiff ℝ ((k : ℕ) : ℕ∞ω) (fun x => (fieldScale L).emb S q hqS (g x)) ∧
      (∀ j ≤ k, ∀ x v, (fieldScale L).emb q 0 (nn_zero_le q)
          (iteratedFDeriv ℝ j (fun x => (fieldScale L).emb S q hqS (g x)) x v) =
        iteratedFDeriv ℝ j (fun x => f ((seqScale L).emb S 0 (nn_zero_le S) x)) x v) ∧
      ∀ K : Set ((seqScale L).Y S), IsCompact K → ∃ V : Set ((seqScale L).Y S), IsOpen V ∧ K ⊆ V ∧ ∃ B : ℝ,
        ∀ x ∈ V, ∀ j ≤ k, ‖iteratedFDeriv ℝ j (fun x => (fieldScale L).emb S q hqS (g x)) x‖ ≤ B :=
  loss_analytic (fieldScale L) ((seqScale L).emb S 0 (nn_zero_le S)) hk hq hS hqS f hf g hg hres

/-- **The same with physical and sequence spaces interchanged** (`f : L² → ℓ²`, restriction `H^S → h^S` continuous ⇒ `f : H^S → h^q` is `C^k`). -/
theorem loss_H_to_h (L : ℝ) [Fact (0 < L)] {k : ℕ} (hk : 1 ≤ k) {q S : ℝ≥0} (hq : 0 < q)
    (hS : ((k : ℝ) + 1) * q < S) (hqS : q ≤ S)
    (f : (fieldScale L).Y 0 → (seqScale L).Y 0) (hf : AnalyticOnNhd ℝ f univ)
    (g : (fieldScale L).Y S → (seqScale L).Y S) (hg : Continuous g)
    (hres : ∀ x, (seqScale L).emb S 0 (nn_zero_le S) (g x) = f ((fieldScale L).emb S 0 (nn_zero_le S) x)) :
    ContDiff ℝ ((k : ℕ) : ℕ∞ω) (fun x => (seqScale L).emb S q hqS (g x)) ∧
      (∀ j ≤ k, ∀ x v, (seqScale L).emb q 0 (nn_zero_le q)
          (iteratedFDeriv ℝ j (fun x => (seqScale L).emb S q hqS (g x)) x v) =
        iteratedFDeriv ℝ j (fun x => f ((fieldScale L).emb S 0 (nn_zero_le S) x)) x v) ∧
      ∀ K : Set ((fieldScale L).Y S), IsCompact K → ∃ V : Set ((fieldScale L).Y S), IsOpen V ∧ K ⊆ V ∧ ∃ B : ℝ,
        ∀ x ∈ V, ∀ j ≤ k, ‖iteratedFDeriv ℝ j (fun x => (seqScale L).emb S q hqS (g x)) x‖ ≤ B :=
  loss_analytic (seqScale L) ((fieldScale L).emb S 0 (nn_zero_le S)) hk hq hS hqS f hf g hg hres

end QuantumNLS.LossSobolev

#print axioms QuantumNLS.LossSobolev.holder_weighted
#print axioms QuantumNLS.LossSobolev.h02_interp
#print axioms QuantumNLS.LossSobolev.seqScale
#print axioms QuantumNLS.LossSobolev.fieldScale
#print axioms QuantumNLS.LossSobolev.loss_analytic
#print axioms QuantumNLS.LossSobolev.loss_h_to_H
#print axioms QuantumNLS.LossSobolev.loss_H_to_h
