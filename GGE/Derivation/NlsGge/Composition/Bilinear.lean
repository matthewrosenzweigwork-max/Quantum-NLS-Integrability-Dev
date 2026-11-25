import NlsGge.Composition.Model

/-!
# W03.03: pointwise continuous bilinear maps act on `A_w`

Source: `paper/v2.tex`, lines 1442 ("Pointwise continuous bilinear maps induce continuous maps
between the corresponding spaces") and 1447-1452 (proof).

`X, Y, Z` are complex Banach spaces and `B : X →L[ℝ] Y →L[ℝ] Z` is only *real* bilinear.
Writing `z • x = re z • x + im z • (I • x)` shows
`B (z • x) (ζ • y) = zζ V₁ + z ζ̄ V₂ + z̄ ζ V₃ + z̄ ζ̄ V₄` with `‖Vᵢ‖ ≤ ‖B‖ ‖x‖ ‖y‖`, so the
`(k,l)` term of the product of two Fourier series has frequencies `±k ± l`.  Since the weight is
even, each of the four resulting convolutions obeys the weighted estimate of
`Convolution.lean`.  This is the honest version of "the same proof applies to Banach-valued
bilinear maps" for real-bilinear maps on complex spaces.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NlsGge.Composition

open MeasureTheory AddCircle Complex ComplexConjugate
open scoped ENNReal

section Algebra

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
  [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem smul_decomp (z : ℂ) (x : X) : z • x = z.re • x + z.im • (I • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- The four sesquilinear components of a real-bilinear map. -/
def bcomb (B : X →L[ℝ] Y →L[ℝ] Z) (x : X) (y : Y) (α β γ : ℂ) : Z :=
  (1 / 4 : ℂ) • (B x y + α • B x (I • y) + β • B (I • x) y + γ • B (I • x) (I • y))

theorem bilin_expand (B : X →L[ℝ] Y →L[ℝ] Z) (x : X) (y : Y) (z ζ : ℂ) :
    B (z • x) (ζ • y) =
      (z * ζ) • bcomb B x y (-I) (-I) (-1) + (z * conj ζ) • bcomb B x y I (-I) 1 +
      (conj z * ζ) • bcomb B x y (-I) I 1 + (conj z * conj ζ) • bcomb B x y I I (-1) := by
  unfold bcomb
  rw [smul_decomp z x, smul_decomp ζ y]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply]
  simp only [← Complex.coe_smul]
  have hre : ∀ w : ℂ, (w.re : ℂ) = (w + conj w) / 2 := fun w => by rw [Complex.re_eq_add_conj]
  have him : ∀ w : ℂ, (w.im : ℂ) = -I * (w - conj w) / 2 := fun w => by
    rw [Complex.im_eq_sub_conj]; field_simp; ring_nf; rw [I_sq]; ring
  simp only [hre, him]
  match_scalars <;> ring_nf <;> simp only [I_sq] <;> ring

theorem norm_bcomb_le (B : X →L[ℝ] Y →L[ℝ] Z) (x : X) (y : Y) {α β γ : ℂ} (hα : ‖α‖ = 1)
    (hβ : ‖β‖ = 1) (hγ : ‖γ‖ = 1) : ‖bcomb B x y α β γ‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
  unfold bcomb
  have hIx : ‖I • x‖ = ‖x‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have hIy : ‖I • y‖ = ‖y‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have hb : ∀ (u : X) (v : Y), ‖B u v‖ ≤ ‖B‖ * ‖u‖ * ‖v‖ := fun u v => B.le_opNorm₂ u v
  have h1 := hb x y
  have h2 := hb x (I • y)
  have h3 := hb (I • x) y
  have h4 := hb (I • x) (I • y)
  rw [hIx, hIy] at *
  rw [norm_smul]
  have : ‖B x y + α • B x (I • y) + β • B (I • x) y + γ • B (I • x) (I • y)‖ ≤
      ‖B x y‖ + ‖B x (I • y)‖ + ‖B (I • x) y‖ + ‖B (I • x) (I • y)‖ := by
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)) ?_
    · rw [norm_smul, hα, one_mul]
    · rw [norm_smul, hβ, one_mul]
    · rw [norm_smul, hγ, one_mul]
  have hq : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [hq]
  linarith

end Algebra

section Product

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
variable {w : ℤ → ℝ}

theorem expSum_single (m : ℤ) (v : X) : expSum (Pi.single m v) = fun θ => fourier m θ • v := by
  funext θ
  unfold expSum
  rw [tsum_eq_single m]
  · simp
  · intro n hn; simp [hn]

theorem summable_norm_single (m : ℤ) (v : X) : Summable fun n => ‖(Pi.single m v : ℤ → X) n‖ := by
  apply summable_of_ne_finset_zero (s := {m})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [hn]

theorem summable_norm_add {c d : ℤ → X} (hc : Summable fun n => ‖c n‖)
    (hd : Summable fun n => ‖d n‖) : Summable fun n => ‖(c + d) n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_add_le _ _) (hc.add hd)

/-- The four frequencies of the `(k,l)` product term. -/
def termCoeffs (B : X →L[ℝ] Y →L[ℝ] Z) (k l : ℤ) (x : X) (y : Y) : ℤ → Z :=
  Pi.single (k + l) (bcomb B x y (-I) (-I) (-1)) + Pi.single (k + -l) (bcomb B x y I (-I) 1) +
  Pi.single (-k + l) (bcomb B x y (-I) I 1) + Pi.single (-k + -l) (bcomb B x y I I (-1))

theorem summable_termCoeffs (B : X →L[ℝ] Y →L[ℝ] Z) (k l : ℤ) (x : X) (y : Y) :
    Summable fun n => ‖termCoeffs B k l x y n‖ := by
  apply summable_of_ne_finset_zero (s := {k + l, k + -l, -k + l, -k + -l})
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [termCoeffs, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]

theorem term_eq_expSum (B : X →L[ℝ] Y →L[ℝ] Z) (k l : ℤ) (x : X) (y : Y) :
    (fun θ : AddCircle (1 : ℝ) => B (fourier k θ • x) (fourier l θ • y)) =
      expSum (termCoeffs B k l x y) := by
  funext θ
  have hs := fun (m : ℤ) (v : Z) => summable_norm_single m v
  unfold termCoeffs
  rw [expSum_add (summable_norm_add (summable_norm_add (hs _ _) (hs _ _)) (hs _ _)) (hs _ _),
    expSum_add (summable_norm_add (hs _ _) (hs _ _)) (hs _ _), expSum_add (hs _ _) (hs _ _)]
  simp only [expSum_single]
  rw [bilin_expand]
  simp only [fourier_add, fourier_neg]

/-- Indicator of `n` being one of the four frequencies `±k ± l`. -/
def freqInd (k l n : ℤ) : ℝ :=
  (if k + l = n then 1 else 0) + (if k + -l = n then 1 else 0) +
  (if -k + l = n then 1 else 0) + (if -k + -l = n then 1 else 0)

theorem norm_termCoeffs_le (B : X →L[ℝ] Y →L[ℝ] Z) (k l : ℤ) (x : X) (y : Y) (n : ℤ) :
    ‖termCoeffs B k l x y n‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ * freqInd k l n := by
  have hI : ‖(I : ℂ)‖ = 1 := Complex.norm_I
  have hmI : ‖(-I : ℂ)‖ = 1 := by rw [norm_neg, Complex.norm_I]
  have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
  have hm1 : ‖(-1 : ℂ)‖ = 1 := by rw [norm_neg, norm_one]
  have hK : 0 ≤ ‖B‖ * ‖x‖ * ‖y‖ := by positivity
  have hsingle : ∀ (m : ℤ) (v : Z), ‖v‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ →
      ‖(Pi.single m v : ℤ → Z) n‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ * (if m = n then 1 else 0) := by
    intro m v hv
    by_cases hmn : m = n
    · subst hmn; simp [hv]
    · rw [Pi.single_eq_of_ne (Ne.symm hmn), if_neg hmn]; simp
  unfold termCoeffs freqInd
  simp only [Pi.add_apply]
  refine norm_add₄_le.trans ?_
  have e1 := hsingle (k + l) _ (norm_bcomb_le B x y hmI hmI hm1)
  have e2 := hsingle (k + -l) _ (norm_bcomb_le B x y hI hmI h1)
  have e3 := hsingle (-k + l) _ (norm_bcomb_le B x y hmI hI h1)
  have e4 := hsingle (-k + -l) _ (norm_bcomb_le B x y hI hI hm1)
  nlinarith

theorem freqInd_nonneg (k l n : ℤ) : 0 ≤ freqInd k l n := by
  unfold freqInd; positivity

theorem freqInd_le (k l n : ℤ) : freqInd k l n ≤ 4 := by
  unfold freqInd
  have : ∀ p : Prop, [Decidable p] → (if p then (1 : ℝ) else 0) ≤ 1 := fun p _ => by
    split_ifs <;> norm_num
  linarith [this (k + l = n), this (k + -l = n), this (-k + l = n), this (-k + -l = n)]

/-- The pointwise product of two synthesized functions. -/
def pointwiseProd (w : ℤ → ℝ) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X) (h : Model Y) :
    AddCircle (1 : ℝ) → Z := fun θ => B (synth w g θ) (synth w h θ)

/-- The `(k,l)` product term. -/
def prodTerm (w : ℤ → ℝ) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X) (h : Model Y) (p : ℤ × ℤ)
    (θ : AddCircle (1 : ℝ)) : Z :=
  B (fourier p.1 θ • coeff w g p.1) (fourier p.2 θ • coeff w h p.2)

theorem norm_prodTerm_le (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X) (h : Model Y) (p : ℤ × ℤ)
    (θ : AddCircle (1 : ℝ)) :
    ‖prodTerm w B g h p θ‖ ≤ ‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ := by
  unfold prodTerm
  refine (B.le_opNorm₂ _ _).trans_eq ?_
  rw [norm_fourier_smul, norm_fourier_smul]

theorem summable_prod_bound (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) :
    Summable fun p : ℤ × ℤ => ‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ := by
  have := summable_mul_of_summable_norm (R := ℝ) (f := fun n => ‖coeff w g n‖)
    (g := fun n => ‖coeff w h n‖)
    ((summable_norm_coeff hw g).1.congr fun n => (norm_norm _).symm)
    ((summable_norm_coeff hw h).1.congr fun n => (norm_norm _).symm)
  simpa [mul_assoc] using this.mul_left ‖B‖

theorem pointwiseProd_eq_tsum (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) (θ : AddCircle (1 : ℝ)) :
    pointwiseProd w B g h θ = ∑' p : ℤ × ℤ, prodTerm w B g h p θ := by
  have hsp : Summable fun p : ℤ × ℤ => prodTerm w B g h p θ :=
    Summable.of_norm_bounded (summable_prod_bound hw B g h) (fun p => norm_prodTerm_le B g h p θ)
  rw [hsp.tsum_prod]
  unfold pointwiseProd synth expSum
  have hg := summable_expSum_terms (summable_norm_coeff hw g).1 θ
  have hh := summable_expSum_terms (summable_norm_coeff hw h).1 θ
  have e1 : B (∑' k, fourier k θ • coeff w g k) (∑' l, fourier l θ • coeff w h l) =
      ∑' k, B (fourier k θ • coeff w g k) (∑' l, fourier l θ • coeff w h l) := by
    have := (B.flip (∑' l, fourier l θ • coeff w h l)).map_tsum hg
    simpa using this
  rw [e1]
  congr 1; ext k
  rw [(B (fourier k θ • coeff w g k)).map_tsum hh]
  rfl

theorem continuous_pointwiseProd (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) : Continuous (pointwiseProd w B g h) :=
  B.continuous₂.comp ((continuous_synth hw g).prodMk (continuous_synth hw h))

theorem continuous_prodTerm (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X) (h : Model Y) (p : ℤ × ℤ) :
    Continuous (prodTerm w B g h p) :=
  B.continuous₂.comp (((map_continuous (fourier p.1)).smul continuous_const).prodMk
    ((map_continuous (fourier p.2)).smul continuous_const))

theorem fourierCoeff_pointwiseProd (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z)
    (g : Model X) (h : Model Y) (n : ℤ) :
    fourierCoeff (pointwiseProd w B g h) n =
      ∑' p : ℤ × ℤ, fourierCoeff (prodTerm w B g h p) n := by
  unfold fourierCoeff
  have hint : ∀ p : ℤ × ℤ, Integrable (fun θ : AddCircle (1 : ℝ) =>
      fourier (-n) θ • prodTerm w B g h p θ) haarAddCircle := fun p =>
    integrable_of_continuous ((map_continuous (fourier (T := 1) (-n))).smul
      (continuous_prodTerm B g h p))
  have hsum : Summable fun p : ℤ × ℤ => ∫ θ : AddCircle (1 : ℝ),
      ‖fourier (-n) θ • prodTerm w B g h p θ‖ ∂haarAddCircle := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun θ => norm_nonneg _)
      (fun p => ?_) (summable_prod_bound hw B g h)
    have hb : ∀ θ : AddCircle (1 : ℝ), ‖‖fourier (-n) θ • prodTerm w B g h p θ‖‖ ≤
        ‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ := fun θ => by
      rw [norm_norm, norm_fourier_smul]; exact norm_prodTerm_le B g h p θ
    have := norm_integral_le_of_norm_le_const (μ := (haarAddCircle : Measure (AddCircle (1 : ℝ))))
      (Filter.Eventually.of_forall hb)
    simp only [probReal_univ, mul_one] at this
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  congr 1; ext θ
  rw [pointwiseProd_eq_tsum hw B g h θ]
  have hsp : Summable fun p : ℤ × ℤ => prodTerm w B g h p θ :=
    Summable.of_norm_bounded (summable_prod_bound hw B g h) (fun p => norm_prodTerm_le B g h p θ)
  exact (hsp.tsum_const_smul _).symm

theorem fourierCoeff_prodTerm (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) (p : ℤ × ℤ) (n : ℤ) :
    fourierCoeff (prodTerm w B g h p) n = termCoeffs B p.1 p.2 (coeff w g p.1) (coeff w h p.2) n := by
  have : prodTerm w B g h p = expSum (termCoeffs B p.1 p.2 (coeff w g p.1) (coeff w h p.2)) :=
    term_eq_expSum B p.1 p.2 _ _
  rw [this, fourierCoeff_expSum (summable_termCoeffs B _ _ _ _)]

/-- Real bound for a Fourier coefficient of the product. -/
theorem norm_fourierCoeff_pointwiseProd_le (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z)
    (g : Model X) (h : Model Y) (n : ℤ) :
    ‖fourierCoeff (pointwiseProd w B g h) n‖ ≤
      ∑' p : ℤ × ℤ, ‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ * freqInd p.1 p.2 n := by
  rw [fourierCoeff_pointwiseProd hw B g h n]
  have hle : ∀ p : ℤ × ℤ, ‖fourierCoeff (prodTerm w B g h p) n‖ ≤
      ‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ * freqInd p.1 p.2 n := fun p => by
    rw [fourierCoeff_prodTerm hw]; exact norm_termCoeffs_le B _ _ _ _ n
  have hS : Summable fun p : ℤ × ℤ => ‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ * freqInd p.1 p.2 n :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (by positivity) (freqInd_nonneg _ _ _))
      (fun p => mul_le_of_le_one_right (by positivity) (le_refl _) |>.trans' (by
        have := freqInd_le p.1 p.2 n
        have h0 : 0 ≤ ‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ := by positivity
        nlinarith)) ((summable_prod_bound hw B g h).mul_left 4)
  refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hS)).trans ?_
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hS) hS


/-! ### `ℝ≥0∞` bookkeeping: four convolutions -/

theorem ennreal_tsum_ite_of_iff (f : ℤ → ℝ≥0∞) (P : ℤ → Prop) [DecidablePred P] (m : ℤ)
    (hP : ∀ l, P l ↔ l = m) : ∑' l, (if P l then f l else 0) = f m := by
  rw [tsum_eq_single m]
  · simp [(hP m).mpr rfl]
  · intro l hl; simp [show ¬ P l from fun h => hl ((hP l).mp h)]

/-- `ℝ≥0∞` version of `freqInd`. -/
def freqIndE (k l n : ℤ) : ℝ≥0∞ :=
  (if k + l = n then 1 else 0) + (if k + -l = n then 1 else 0) +
  (if -k + l = n then 1 else 0) + (if -k + -l = n then 1 else 0)

theorem ofReal_freqInd (k l n : ℤ) : ENNReal.ofReal (freqInd k l n) = freqIndE k l n := by
  unfold freqInd freqIndE
  have h : ∀ p : Prop, [Decidable p] →
      ENNReal.ofReal (if p then (1 : ℝ) else 0) = if p then 1 else 0 := fun p _ => by
    split_ifs <;> simp
  have hn : ∀ p : Prop, [Decidable p] → (0 : ℝ) ≤ if p then (1 : ℝ) else 0 := fun p _ => by
    split_ifs <;> norm_num
  rw [ENNReal.ofReal_add (by positivity) (hn _), ENNReal.ofReal_add (by positivity) (hn _),
    ENNReal.ofReal_add (hn _) (hn _), h, h, h, h]

theorem ennreal_freq_sum_le (A B : ℤ → ℝ≥0∞) (n : ℤ) :
    ∑' p : ℤ × ℤ, A p.1 * B p.2 * freqIndE p.1 p.2 n ≤
      4 * ∑' k, (A k + A (-k)) * (B (n - k) + B (-(n - k))) := by
  set C : ℤ → ℝ≥0∞ := fun k => (A k + A (-k)) * (B (n - k) + B (-(n - k))) with hC
  -- split into the four frequencies
  have hsplit : ∀ p : ℤ × ℤ, A p.1 * B p.2 * freqIndE p.1 p.2 n =
      (if p.2 = n - p.1 then A p.1 * B p.2 else 0) + (if p.2 = p.1 - n then A p.1 * B p.2 else 0) +
      (if p.2 = n + p.1 then A p.1 * B p.2 else 0) +
      (if p.2 = -n - p.1 then A p.1 * B p.2 else 0) := by
    intro p
    unfold freqIndE
    have e1 : (p.1 + p.2 = n) ↔ (p.2 = n - p.1) := by omega
    have e2 : (p.1 + -p.2 = n) ↔ (p.2 = p.1 - n) := by omega
    have e3 : (-p.1 + p.2 = n) ↔ (p.2 = n + p.1) := by omega
    have e4 : (-p.1 + -p.2 = n) ↔ (p.2 = -n - p.1) := by omega
    simp only [e1, e2, e3, e4, mul_add]
    simp only [mul_ite, mul_one, mul_zero]
  simp_rw [hsplit]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
  have t1 : ∑' p : ℤ × ℤ, (if p.2 = n - p.1 then A p.1 * B p.2 else 0) = ∑' k, A k * B (n - k) := by
    rw [ENNReal.tsum_prod (f := fun k l => if l = n - k then A k * B l else 0)]
    congr 1; ext k
    exact ennreal_tsum_ite_of_iff (fun l => A k * B l) _ _ (fun l => Iff.rfl)
  have t2 : ∑' p : ℤ × ℤ, (if p.2 = p.1 - n then A p.1 * B p.2 else 0) = ∑' k, A k * B (k - n) := by
    rw [ENNReal.tsum_prod (f := fun k l => if l = k - n then A k * B l else 0)]
    congr 1; ext k
    exact ennreal_tsum_ite_of_iff (fun l => A k * B l) _ _ (fun l => Iff.rfl)
  have t3 : ∑' p : ℤ × ℤ, (if p.2 = n + p.1 then A p.1 * B p.2 else 0) =
      ∑' k, A (-k) * B (n - k) := by
    rw [ENNReal.tsum_prod (f := fun k l => if l = n + k then A k * B l else 0)]
    rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1; ext k
    simp only [Equiv.neg_apply]
    rw [ennreal_tsum_ite_of_iff (fun l => A (-k) * B l) _ (n + -k) (fun l => Iff.rfl)]
    rw [sub_eq_add_neg]
  have t4 : ∑' p : ℤ × ℤ, (if p.2 = -n - p.1 then A p.1 * B p.2 else 0) =
      ∑' k, A (-k) * B (-(n - k)) := by
    rw [ENNReal.tsum_prod (f := fun k l => if l = -n - k then A k * B l else 0)]
    rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1; ext k
    simp only [Equiv.neg_apply]
    rw [ennreal_tsum_ite_of_iff (fun l => A (-k) * B l) _ (-n - -k) (fun l => Iff.rfl)]
    congr 2; ring
  rw [t1, t2, t3, t4]
  have b1 : ∑' k, A k * B (n - k) ≤ ∑' k, C k := ENNReal.tsum_le_tsum fun k => by
    simp only [hC]; gcongr
    · exact le_self_add
    · exact le_self_add
  have b2 : ∑' k, A k * B (k - n) ≤ ∑' k, C k := ENNReal.tsum_le_tsum fun k => by
    simp only [hC]; gcongr
    · exact le_self_add
    · rw [show k - n = -(n - k) by ring]; exact le_add_self
  have b3 : ∑' k, A (-k) * B (n - k) ≤ ∑' k, C k := ENNReal.tsum_le_tsum fun k => by
    simp only [hC]; gcongr
    · exact le_add_self
    · exact le_self_add
  have b4 : ∑' k, A (-k) * B (-(n - k)) ≤ ∑' k, C k := ENNReal.tsum_le_tsum fun k => by
    simp only [hC]; gcongr
    · exact le_add_self
    · exact le_add_self
  calc _ ≤ ∑' k, C k + ∑' k, C k + ∑' k, C k + ∑' k, C k := by gcongr
    _ = 4 * ∑' k, C k := by ring

/-- `∑_k (x_k + x_{-k})^2 ≤ 4 ∑_k x_k^2`. -/
theorem ennreal_tsum_sym_sq_le (x : ℤ → ℝ≥0∞) :
    ∑' k, (x k + x (-k)) ^ 2 ≤ 4 * ∑' k, x k ^ 2 := by
  have hpt : ∀ k, (x k + x (-k)) ^ 2 ≤ 2 * x k ^ 2 + 2 * x (-k) ^ 2 := by
    intro k
    have := ennreal_two_mul_le_add_sq (x k) (x (-k))
    calc (x k + x (-k)) ^ 2 = x k ^ 2 + x (-k) ^ 2 + 2 * x k * x (-k) := by ring
      _ ≤ x k ^ 2 + x (-k) ^ 2 + (x k ^ 2 + x (-k) ^ 2) := by gcongr
      _ = _ := by ring
  refine (ENNReal.tsum_le_tsum hpt).trans_eq ?_
  have e := (Equiv.neg ℤ).tsum_eq (fun k => x k ^ 2)
  simp only [Equiv.neg_apply] at e
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, e]
  ring

/-- Real summability and bound from an `ℝ≥0∞` bound. -/
theorem summable_of_ennreal_bound {f : ℤ → ℝ} (hf : ∀ n, 0 ≤ f n) {C : ℝ} (hC : 0 ≤ C)
    (h : ∑' n, ENNReal.ofReal (f n) ≤ ENNReal.ofReal C) : Summable f ∧ ∑' n, f n ≤ C := by
  have hfin : ∑' n, ENNReal.ofReal (f n) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hs : Summable f := by
    refine (ENNReal.summable_toReal hfin).congr fun n => ?_
    rw [ENNReal.toReal_ofReal (hf n)]
  refine ⟨hs, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hs] at h
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp h


theorem summable_freq_bound (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) (n : ℤ) :
    Summable fun p : ℤ × ℤ => ‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ * freqInd p.1 p.2 n :=
  Summable.of_nonneg_of_le (fun p => mul_nonneg (by positivity) (freqInd_nonneg _ _ _))
    (fun p => by
      have := freqInd_le p.1 p.2 n
      have h0 : 0 ≤ ‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ := by positivity
      show _ ≤ 4 * (‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖)
      nlinarith) ((summable_prod_bound hw B g h).mul_left 4)

/-- The product constant `C_w = 32 ‖r‖₂` for a chosen ratio majorant `r` (the factor `16`
relative to the source's `2‖r‖₂` comes from the four sesquilinear parts of a real-bilinear map
and from symmetrization `a_k + a_{-k}`; it is a fixed constant depending only on `w`). -/
def prodConst {w : ℤ → ℝ} (hw : AdmissibleWeight w) : ℝ :=
  32 * Real.sqrt (ratioNormSq (Classical.choose hw.ratio))

theorem prodConst_nonneg {w : ℤ → ℝ} (hw : AdmissibleWeight w) : 0 ≤ prodConst hw := by
  unfold prodConst; positivity

/-- W03.03, bilinear estimate: `∑ (w_n ‖(B(f,g))^(n)‖)^2 ≤ (C_w ‖B‖ ‖f‖ ‖g‖)^2`. -/
theorem pointwiseProd_weighted_bound (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z)
    (g : Model X) (h : Model Y) :
    Summable (fun n => (w n * ‖fourierCoeff (pointwiseProd w B g h) n‖) ^ 2) ∧
    ∑' n, (w n * ‖fourierCoeff (pointwiseProd w B g h) n‖) ^ 2 ≤
      (prodConst hw * ‖B‖ * ‖g‖ * ‖h‖) ^ 2 := by
  obtain hr := Classical.choose_spec hw.ratio
  set r := Classical.choose hw.ratio with hrdef
  set A : ℤ → ℝ≥0∞ := fun k => ENNReal.ofReal ‖coeff w g k‖ with hA
  set Bn : ℤ → ℝ≥0∞ := fun k => ENNReal.ofReal ‖coeff w h k‖ with hBn
  set At : ℤ → ℝ≥0∞ := fun k => A k + A (-k) with hAt
  set Bt : ℤ → ℝ≥0∞ := fun k => Bn k + Bn (-k) with hBt
  set W : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (w n) with hW
  set nB : ℝ≥0∞ := ENNReal.ofReal ‖B‖ with hnB
  set fh := fourierCoeff (pointwiseProd w B g h) with hfh
  -- coefficient bound
  have hcoef : ∀ n, ENNReal.ofReal ‖fh n‖ ≤ nB * (4 * ∑' k, At k * Bt (n - k)) := by
    intro n
    have h1 := norm_fourierCoeff_pointwiseProd_le hw B g h n
    have h2 := ENNReal.ofReal_le_ofReal h1
    rw [ENNReal.ofReal_tsum_of_nonneg (fun p => mul_nonneg (by positivity) (freqInd_nonneg _ _ _))
      (summable_freq_bound hw B g h n)] at h2
    refine h2.trans ?_
    have h3 : ∀ p : ℤ × ℤ, ENNReal.ofReal (‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ *
        freqInd p.1 p.2 n) = nB * (A p.1 * Bn p.2 * freqIndE p.1 p.2 n) := by
      intro p
      have e : ‖B‖ * ‖coeff w g p.1‖ * ‖coeff w h p.2‖ * freqInd p.1 p.2 n =
          ‖B‖ * ((‖coeff w g p.1‖ * ‖coeff w h p.2‖) * freqInd p.1 p.2 n) := by ring
      rw [e, ENNReal.ofReal_mul (norm_nonneg B),
        ENNReal.ofReal_mul (mul_nonneg (norm_nonneg (coeff w g p.1)) (norm_nonneg (coeff w h p.2))),
        ENNReal.ofReal_mul (norm_nonneg (coeff w g p.1)), ofReal_freqInd]
    simp_rw [h3]
    rw [ENNReal.tsum_mul_left]
    gcongr
    exact ennreal_freq_sum_le A Bn n
  -- weighted square sum
  have hW_even : ∀ k, W (-k) = W k := fun k => by simp [hW, hw.even k]
  have hWA : ∀ k, W k * A k = ENNReal.ofReal ‖g k‖ := by
    intro k
    simp only [hW, hA]
    rw [← ENNReal.ofReal_mul (hw.pos k).le, norm_coeff hw, ← mul_assoc,
      mul_inv_cancel₀ (hw.pos k).ne', one_mul]
  have hWB : ∀ k, W k * Bn k = ENNReal.ofReal ‖h k‖ := by
    intro k
    simp only [hW, hBn]
    rw [← ENNReal.ofReal_mul (hw.pos k).le, norm_coeff hw, ← mul_assoc,
      mul_inv_cancel₀ (hw.pos k).ne', one_mul]
  have hsqG : ∑' k, ENNReal.ofReal ‖g k‖ ^ 2 = ENNReal.ofReal (‖g‖ ^ 2) := by
    rw [Model.norm_sq_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) g.summable_sq]
    congr 1; ext k; rw [ENNReal.ofReal_pow (norm_nonneg _)]
  have hsqH : ∑' k, ENNReal.ofReal ‖h k‖ ^ 2 = ENNReal.ofReal (‖h‖ ^ 2) := by
    rw [Model.norm_sq_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) h.summable_sq]
    congr 1; ext k; rw [ENNReal.ofReal_pow (norm_nonneg _)]
  have hAt2 : ∑' k, (W k * At k) ^ 2 ≤ 4 * ENNReal.ofReal (‖g‖ ^ 2) := by
    have : ∀ k, W k * At k = ENNReal.ofReal ‖g k‖ + ENNReal.ofReal ‖g (-k)‖ := by
      intro k
      simp only [hAt, mul_add]
      rw [hWA, ← hW_even k, hWA]
    simp_rw [this]
    rw [← hsqG]
    exact ennreal_tsum_sym_sq_le (fun k => ENNReal.ofReal ‖g k‖)
  have hBt2 : ∑' k, (W k * Bt k) ^ 2 ≤ 4 * ENNReal.ofReal (‖h‖ ^ 2) := by
    have : ∀ k, W k * Bt k = ENNReal.ofReal ‖h k‖ + ENNReal.ofReal ‖h (-k)‖ := by
      intro k
      simp only [hBt, mul_add]
      rw [hWB, ← hW_even k, hWB]
    simp_rw [this]
    rw [← hsqH]
    exact ennreal_tsum_sym_sq_le (fun k => ENNReal.ofReal ‖h k‖)
  have hconv := ennreal_weighted_conv hr At Bt
  have hR : ∑' n, ENNReal.ofReal (r n) ^ 2 = ENNReal.ofReal (ratioNormSq r) := by
    rw [ratioNormSq, ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hr.r_sq]
    congr 1; ext n; rw [ENNReal.ofReal_pow (hr.r_nonneg n)]
  rw [hR] at hconv
  have hmain : ∑' n, ENNReal.ofReal ((w n * ‖fh n‖) ^ 2) ≤
      ENNReal.ofReal ((prodConst hw * ‖B‖ * ‖g‖ * ‖h‖) ^ 2) := by
    calc ∑' n, ENNReal.ofReal ((w n * ‖fh n‖) ^ 2)
        = ∑' n, (W n * ENNReal.ofReal ‖fh n‖) ^ 2 := by
          congr 1; ext n
          rw [ENNReal.ofReal_pow (mul_nonneg (hw.pos n).le (norm_nonneg _)),
            ENNReal.ofReal_mul (hw.pos n).le]
      _ ≤ ∑' n, (W n * (nB * (4 * ∑' k, At k * Bt (n - k)))) ^ 2 :=
          ENNReal.tsum_le_tsum fun n => by gcongr; exact hcoef n
      _ = (4 * nB) ^ 2 * ∑' n, (W n * ∑' k, At k * Bt (n - k)) ^ 2 := by
          rw [← ENNReal.tsum_mul_left]; congr 1; ext n; ring
      _ ≤ (4 * nB) ^ 2 * (4 * ENNReal.ofReal (ratioNormSq r) * (∑' n, (W n * At n) ^ 2) *
            ∑' n, (W n * Bt n) ^ 2) := by gcongr
      _ ≤ (4 * nB) ^ 2 * (4 * ENNReal.ofReal (ratioNormSq r) * (4 * ENNReal.ofReal (‖g‖ ^ 2)) *
            (4 * ENNReal.ofReal (‖h‖ ^ 2))) := by gcongr
      _ = ENNReal.ofReal ((prodConst hw * ‖B‖ * ‖g‖ * ‖h‖) ^ 2) := by
          have hRn : 0 ≤ ratioNormSq r := tsum_nonneg fun n => sq_nonneg _
          have : (prodConst hw * ‖B‖ * ‖g‖ * ‖h‖) ^ 2 =
              1024 * (‖B‖ ^ 2 * (ratioNormSq r * (‖g‖ ^ 2 * ‖h‖ ^ 2))) := by
            rw [prodConst, ← hrdef]
            have hs := Real.sq_sqrt hRn
            rw [mul_pow, mul_pow, mul_pow, mul_pow, hs]; ring
          rw [this, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (sq_nonneg _),
            ENNReal.ofReal_mul hRn, ENNReal.ofReal_mul (sq_nonneg _),
            ENNReal.ofReal_pow (norm_nonneg B) 2]
          simp only [hnB, ENNReal.ofReal_ofNat]
          ring
  exact summable_of_ennreal_bound (fun n => sq_nonneg _) (sq_nonneg _) hmain


theorem memAw_pointwiseProd (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) : MemAw w (pointwiseProd w B g h) :=
  ⟨continuous_pointwiseProd hw B g h, (pointwiseProd_weighted_bound hw B g h).1⟩

theorem awNorm_pointwiseProd_le (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) : awNorm w (pointwiseProd w B g h) ≤ prodConst hw * ‖B‖ * ‖g‖ * ‖h‖ := by
  unfold awNorm
  refine Real.sqrt_le_iff.mpr ⟨by have := prodConst_nonneg hw; positivity, ?_⟩
  exact (pointwiseProd_weighted_bound hw B g h).2

/-- The model element of the pointwise product. -/
def prodModel (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X) (h : Model Y) :
    Model Z := toModel hw (memAw_pointwiseProd hw B g h)

theorem synth_prodModel (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) (θ : AddCircle (1 : ℝ)) :
    synth w (prodModel hw B g h) θ = B (synth w g θ) (synth w h θ) := by
  unfold prodModel; rw [synth_toModel]; rfl

theorem norm_prodModel_le (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) : ‖prodModel hw B g h‖ ≤ prodConst hw * ‖B‖ * ‖g‖ * ‖h‖ := by
  unfold prodModel; rw [norm_toModel]; exact awNorm_pointwiseProd_le hw B g h

/-- W03.03 / `D:lem:composition` first assertion on the model: the continuous real-bilinear
map `Model X × Model Y → Model Z` induced by `B` pointwise, with norm `≤ C_w ‖B‖`. -/
def prodCLM (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) :
    Model X →L[ℝ] Model Y →L[ℝ] Model Z :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (prodModel hw B)
      (fun g g' h => synth_injective hw (funext fun θ => by
        rw [synth_add hw, synth_prodModel, synth_prodModel, synth_prodModel, synth_add hw,
          map_add, ContinuousLinearMap.add_apply]))
      (fun c g h => synth_injective hw (funext fun θ => by
        rw [synth_smul, synth_prodModel, synth_prodModel, synth_smul, map_smul,
          ContinuousLinearMap.smul_apply]))
      (fun g h h' => synth_injective hw (funext fun θ => by
        rw [synth_add hw, synth_prodModel, synth_prodModel, synth_prodModel, synth_add hw,
          map_add]))
      (fun c g h => synth_injective hw (funext fun θ => by
        rw [synth_smul, synth_prodModel, synth_prodModel, synth_smul, map_smul])))
    (prodConst hw * ‖B‖) (fun g h => norm_prodModel_le hw B g h)

@[simp] theorem prodCLM_apply (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) : prodCLM hw B g h = prodModel hw B g h := rfl

theorem synth_prodCLM (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) (g : Model X)
    (h : Model Y) (θ : AddCircle (1 : ℝ)) :
    synth w (prodCLM hw B g h) θ = B (synth w g θ) (synth w h θ) := synth_prodModel hw B g h θ

theorem norm_prodCLM_le (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z) :
    ‖prodCLM hw B‖ ≤ prodConst hw * ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (mul_nonneg (prodConst_nonneg hw) (norm_nonneg B)) _

/-- **`D:lem:composition`, first assertion (function form).**  A pointwise continuous
real-bilinear map sends `A_w(X) × A_w(Y)` into `A_w(Z)` with
`‖B(f,g)‖_{A_w} ≤ C_w ‖B‖ ‖f‖_{A_w} ‖g‖_{A_w}`. -/
theorem composition_bilinear (hw : AdmissibleWeight w) (B : X →L[ℝ] Y →L[ℝ] Z)
    {f : AddCircle (1 : ℝ) → X} {g : AddCircle (1 : ℝ) → Y} (hf : MemAw w f) (hg : MemAw w g) :
    MemAw w (fun θ => B (f θ) (g θ)) ∧
      awNorm w (fun θ => B (f θ) (g θ)) ≤ prodConst hw * ‖B‖ * awNorm w f * awNorm w g := by
  have e : (fun θ => B (f θ) (g θ)) = pointwiseProd w B (toModel hw hf) (toModel hw hg) := by
    funext θ; simp only [pointwiseProd, synth_toModel]
  rw [e, ← norm_toModel hw hf, ← norm_toModel hw hg]
  exact ⟨memAw_pointwiseProd hw B _ _, awNorm_pointwiseProd_le hw B _ _⟩

end Product

end NlsGge.Composition
