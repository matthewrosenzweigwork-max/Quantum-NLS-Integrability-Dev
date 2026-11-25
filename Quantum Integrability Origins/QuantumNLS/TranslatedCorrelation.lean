import Mathlib
import QuantumNLS.SobolevSpaces

/-!
# REG-006: translated scalar products (`CC:G04:correlation`), checkpoint

Source: `source/chapters/regularity/integer_moments.tex`, lines 159--206 (statement and printed proof).
Setup: integers `k ≥ 1`, `q ≥ 2`, factors `f_1,…,f_q ∈ H^k(𝕋_L)`, and
`C(h) = ∫_{𝕋_L} ∏_j f_j(x+h_j) dx` for `h ∈ ℝ^q`.

Realized spaces used read-only (no new H^k is introduced):
* DEF-002 `H^s(T_L)` = `QuantumNLS.Sobolev.H02 L s` (`SobolevSpaces.lean`, realized, a4e11c0c), with
  `H^k = H02 L k` and the torus `AddCircle L` with mathlib `volume` (total mass `L`, `Fourier.torus_mass`);
* the realized continuous embedding `H^1 ↪ C(𝕋_L)` (`sobolevEmbedding`, bound `c_L`, and
  `sobolevEmbedding_ae`: the continuous function is an a.e. representative of the `L²` class);
* the norm-`≤ 1` inclusions `H^k ↪ H^1` (`H02.mono`) and `H^1_{DEF-002} ↪ H^1_{F04}` (`H02.toH04`).

## What is formalized (checkpoint)

Proved, with no sorry and standard axioms only:
1. `Cfun_eq_cont`: `C(h)` may be computed with the continuous representatives (independence of the
   representative, by translation invariance of the null sets).
2. `norm_Cfun_le`: `‖C(h)‖ ≤ L · c_L^q · ∏_j ‖f_j‖_{H^k}` for every `h` (order-0 bound of the lemma with
   `C_{k,q,L} = L c_L^q`).
3. `Cfun_continuous`: `C : ℝ^q → ℂ` is continuous.
4. `correlation_checkpoint`: the conjunction of 1–3 and the `d = 0` Taylor clause (the Taylor polynomial of
   degree 0 is `C(0)`; its remainder is `o(1)` and bounded by `2 L c_L^q ∏‖f_j‖`).

NOT formalized (gaps, see the review record): `C ∈ C^{2k}(ℝ^q)`; the bounds on partial derivatives of total order
1..2k; the Taylor remainders for `d ≥ 1`. These need a realized derivative operator on H^k and the
integration-by-parts argument of the printed proof (lines 176--199), which are not in the realized modules.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory AddCircle Filter Topology
open scoped BigOperators ENNReal

namespace QuantumNLS.TranslatedCorrelation

open QuantumNLS.Sobolev QuantumNLS.Fourier

variable {L : ℝ} [Fact (0 < L)]

/-- The realized DEF-002 space `H^k(𝕋_L)` for an integer `k` (`H02 L k`). -/
abbrev Hk (L : ℝ) [Fact (0 < L)] (k : ℕ) : Type := H02 L (k : ℝ)

theorem one_le_cast {k : ℕ} (hk : 1 ≤ k) : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk

/-- The F04 `H^1` representative of `f ∈ H^k`: `H^k ↪ H^1_{DEF-002} ↪ H^1_{F04}` (both norm `≤ 1`). -/
def toF1 {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) : H04sp L 1 :=
  H02.toH04 zero_le_one (H02.mono (L := L) (s := 1) (t := (k : ℝ)) (one_le_cast hk) f)

theorem toF1_val {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) : (toF1 hk f).val = f.val := by
  unfold toF1 H02.toH04 H02.mono
  rw [fieldIncl_val, fieldIncl_val]

/-- The continuous representative of `f ∈ H^k`, `k ≥ 1`: `H^k ↪ H^1 ↪ C(𝕋_L)` (realized `sobolevEmbedding`). -/
def contRep {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) : C(AddCircle L, ℂ) :=
  sobolevEmbedding (toF1 hk f)

theorem norm_toF1_le {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) : ‖toF1 hk f‖ ≤ ‖f‖ :=
  (H02.norm_toH04_le zero_le_one (H02.mono (L := L) (s := 1) (t := (k : ℝ)) (one_le_cast hk) f)).trans
    (H02.norm_mono_le (L := L) (s := 1) (t := (k : ℝ)) (one_le_cast hk) f)

theorem norm_contRep_le {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) : ‖contRep hk f‖ ≤ cL L * ‖f‖ :=
  (norm_sobolevEmbedding_le (L := L) (toF1 hk f)).trans
    (mul_le_mul_of_nonneg_left (norm_toF1_le hk f) (cL_nonneg L))

theorem norm_contRep_apply_le {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) (x : AddCircle L) :
    ‖contRep hk f x‖ ≤ cL L * ‖f‖ :=
  (ContinuousMap.norm_coe_le_norm (contRep hk f) x).trans (norm_contRep_le hk f)

/-- The continuous representative is an a.e. representative of the `L²` class of `f`
(realized `sobolevEmbedding_ae`, transported along `toF1_val`). -/
theorem ae_eq_contRep {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) :
    ((f : Hk L k).val : AddCircle L → ℂ) =ᵐ[volume] ⇑(contRep hk f) := by
  have h := sobolevEmbedding_ae (L := L) (toF1 hk f)
  rw [toF1_val] at h
  exact h

/-- Translation preserves almost-everywhere equality on the torus (`volume` is translation invariant;
the group is named explicitly to avoid an instance-search timeout on `volume`). -/
theorem ae_translate {g g' : AddCircle L → ℂ} (h : g =ᵐ[volume] g') (a : AddCircle L) :
    ∀ᵐ x ∂(volume : Measure (AddCircle L)), g (x + a) = g' (x + a) := by
  have hq : Measure.QuasiMeasurePreserving (fun y : AddCircle L => a + y)
      (volume : Measure (AddCircle L)) (volume : Measure (AddCircle L)) :=
    quasiMeasurePreserving_add_left (G := AddCircle L) volume a
  have h' : ∀ᵐ y ∂(volume : Measure (AddCircle L)), g y = g' y := h
  have hT := hq.ae (p := fun y => g y = g' y) h'
  filter_upwards [hT] with x hx
  rw [add_comm x a]
  exact hx

/-- `C(h) = ∫_{𝕋_L} ∏_j f_j(x+h_j) dx` (source line 164), with `f_j` the `L²` classes of `H^k`. -/
def Cfun {q k : ℕ} (f : Fin q → Hk L k) (h : Fin q → ℝ) : ℂ :=
  ∫ x, ∏ j, (f j).val (x + ((h j : ℝ) : AddCircle L)) ∂(volume : Measure (AddCircle L))

/-- `C(h)` may be computed with the continuous representatives (source: the integral depends only on the
classes). -/
theorem Cfun_eq_cont {q k : ℕ} (hk : 1 ≤ k) (f : Fin q → Hk L k) (h : Fin q → ℝ) :
    Cfun f h = ∫ x, ∏ j, contRep hk (f j) (x + ((h j : ℝ) : AddCircle L))
      ∂(volume : Measure (AddCircle L)) := by
  unfold Cfun
  refine integral_congr_ae ?_
  have hs : ∀ j : Fin q, ∀ᵐ x ∂(volume : Measure (AddCircle L)),
      (f j).val (x + ((h j : ℝ) : AddCircle L)) = contRep hk (f j) (x + ((h j : ℝ) : AddCircle L)) :=
    fun j => ae_translate (ae_eq_contRep hk (f j)) _
  filter_upwards [ae_all_iff.2 hs] with x hx
  exact Finset.prod_congr rfl (fun j _ => hx j)

/-- **Order-0 bound** (source lines 167--169 for `d`-free order 0): `|C(h)| ≤ L c_L^q ∏_j ‖f_j‖_{H^k}`,
uniformly in `h`. -/
theorem norm_Cfun_le {q k : ℕ} (hk : 1 ≤ k) (f : Fin q → Hk L k) (h : Fin q → ℝ) :
    ‖Cfun f h‖ ≤ L * cL L ^ q * ∏ j, ‖f j‖ := by
  rw [Cfun_eq_cont hk f h]
  have hpt : ∀ x : AddCircle L, ‖∏ j, contRep hk (f j) (x + ((h j : ℝ) : AddCircle L))‖ ≤
      ∏ j, (cL L * ‖f j‖) := by
    intro x
    rw [norm_prod]
    gcongr with j _
    exact norm_contRep_apply_le hk (f j) _
  have hint := norm_integral_le_of_norm_le_const (μ := (volume : Measure (AddCircle L)))
    (C := ∏ j, (cL L * ‖f j‖)) (Filter.Eventually.of_forall hpt)
  have hmass : (volume : Measure (AddCircle L)).real Set.univ = L := by
    rw [Measure.real, torus_mass (L := L), ENNReal.toReal_ofReal (Fact.out : (0 : ℝ) < L).le]
  rw [hmass] at hint
  have hprod : ∏ j, (cL L * ‖f j‖) = cL L ^ q * ∏ j, ‖f j‖ := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod] at hint
  linarith [hint]

/-- Continuity of `C` on `ℝ^q` (the order-0 part of `C ∈ C^{2k}`). -/
theorem Cfun_continuous {q k : ℕ} (hk : 1 ≤ k) (f : Fin q → Hk L k) :
    Continuous fun h : Fin q → ℝ => Cfun f h := by
  have hcoe : Continuous fun r : ℝ => ((r : ℝ) : AddCircle L) := by
    fun_prop
  have hF : Continuous fun p : (Fin q → ℝ) × AddCircle L =>
      ∏ j, contRep hk (f j) (p.2 + ((p.1 j : ℝ) : AddCircle L)) := by
    refine continuous_finset_prod _ (fun j _ => ?_)
    exact (contRep hk (f j)).continuous.comp
      (continuous_snd.add (hcoe.comp ((continuous_apply j).comp continuous_fst)))
  have hc := continuous_parametric_integral_of_continuous (μ := (volume : Measure (AddCircle L)))
    (f := fun (h : Fin q → ℝ) (x : AddCircle L) =>
      ∏ j, contRep hk (f j) (x + ((h j : ℝ) : AddCircle L)))
    hF (isCompact_univ)
  have e : (fun h : Fin q → ℝ => Cfun f h) = fun h : Fin q → ℝ =>
      ∫ x in Set.univ, ∏ j, contRep hk (f j) (x + ((h j : ℝ) : AddCircle L))
        ∂(volume : Measure (AddCircle L)) := by
    funext h
    rw [Measure.restrict_univ, Cfun_eq_cont hk f h]
  rw [e]
  exact hc

/-- **Checkpoint of `CC:G04:correlation`** (source lines 159--173, the parts formalized here):
for `k ≥ 1`, `q ≥ 2` and `f_j ∈ H^k`:
(a) `C(h)` is independent of the representatives and continuous on `ℝ^q`;
(b) the order-0 bound `‖C(h)‖ ≤ C_{k,q,L} ∏_j ‖f_j‖_{H^k}` holds uniformly in `h`, with `C_{k,q,L} = L c_L^q`;
(c) the `d = 0` Taylor clause: the degree-0 Taylor polynomial is `C(0)`; its remainder `C(h) − C(0)` is
    `o(1)` as `h → 0` and bounded for all `h` by `C_{k,q,L,0} ∏_j ‖f_j‖_{H^k}` with `C_{k,q,L,0} = 2 L c_L^q`.
The `C^{2k}` regularity and the derivative/`d ≥ 1` clauses are not part of this checkpoint. -/
theorem correlation_checkpoint {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (f : Fin q → Hk L k) :
    (∀ h : Fin q → ℝ, Cfun f h = ∫ x, ∏ j, contRep hk (f j) (x + ((h j : ℝ) : AddCircle L))
        ∂(volume : Measure (AddCircle L))) ∧
    Continuous (fun h : Fin q → ℝ => Cfun f h) ∧
    (∀ h : Fin q → ℝ, ‖Cfun f h‖ ≤ L * cL L ^ q * ∏ j, ‖f j‖) ∧
    Tendsto (fun h : Fin q → ℝ => Cfun f h - Cfun f 0) (𝓝 0) (𝓝 0) ∧
    (∀ h : Fin q → ℝ, ‖Cfun f h - Cfun f 0‖ ≤ 2 * L * cL L ^ q * ∏ j, ‖f j‖) := by
  refine ⟨fun h => Cfun_eq_cont hk f h, Cfun_continuous hk f, fun h => norm_Cfun_le hk f h, ?_, ?_⟩
  · simpa using ((Cfun_continuous hk f).tendsto (0 : Fin q → ℝ)).sub_const (Cfun f 0)
  · intro h
    have h1 := norm_Cfun_le hk f h
    have h2 := norm_Cfun_le hk f 0
    have h3 := norm_sub_le (Cfun f h) (Cfun f 0)
    have hP : 0 ≤ L * cL L ^ q * ∏ j, ‖f j‖ :=
      mul_nonneg (mul_nonneg (le_of_lt (Fact.out : (0 : ℝ) < L)) (pow_nonneg (cL_nonneg L) q))
        (Finset.prod_nonneg fun j _ => norm_nonneg _)
    linarith

end QuantumNLS.TranslatedCorrelation

/-! Axiom audit (every declaration of the checkpoint). -/
#print axioms QuantumNLS.TranslatedCorrelation.correlation_checkpoint
#print axioms QuantumNLS.TranslatedCorrelation.Cfun_eq_cont
#print axioms QuantumNLS.TranslatedCorrelation.norm_Cfun_le
#print axioms QuantumNLS.TranslatedCorrelation.Cfun_continuous
#print axioms QuantumNLS.TranslatedCorrelation.norm_contRep_le
#print axioms QuantumNLS.TranslatedCorrelation.ae_eq_contRep
#print axioms QuantumNLS.TranslatedCorrelation.ae_translate
