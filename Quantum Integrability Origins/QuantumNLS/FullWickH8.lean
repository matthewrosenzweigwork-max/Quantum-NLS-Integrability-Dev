import QuantumNLS.FullWickH1
import QuantumNLS.FullWickH2
import QuantumNLS.FullWickH3
import QuantumNLS.FullWickH6
import QuantumNLS.FullWickH7
import QuantumNLS.FullWickO2
import QuantumNLS.FullWickS1
import QuantumNLS.FullWickS2

/-! FullWickH8 (haiku_inventory, R-140AE34B `thm:full-wick`, assembly stage A: algebra and STATIC clause).

Printed items (source-text/chapters/core/wick_calculus.tex:49-203):
  * every balanced `f` gives `W^q_N(f)` with uniform strong symbol `f(w(u))` on `𝒰_R`, and its adjoint
    with the conjugate symbol (static clause, parameter predicate `UniformStaticR49b.UniformStatic hκ j q`);
  * the same at the Q06 selected witnesses (separate corollary);
  * ordered products of Cartesian generators (`pair_list_prod`, constants C = K = 1);
  * the scaled Dirac commutator (eq:full-Dirac-bound) with symbol the bracket polynomial;
  * uniformly norm-close preparations preserve the static statements (FullWickH7).

Recipe (sonnet_fourier `HOW the auxiliary construction SHOULD CONSUME IT`, the review `How the auxiliary construction should consume this`):
  generators from `FullWickO2.wick_uniform_pair` (static gauge `FullWickO1.staticGauge q`),
  ordered products by `FullWickH6.pair_list_prod` (C = K = 1), the O(1/N) comparison
  `FullWickS1.balanced_ordered_word_comparison_uniform` and the sum transfer
  `FullWickS2.hasUniformPairT_of_sum_opClose`; the adjoint companion is the star of the same bound.

Operators are the DEF-032 `BalancedWickDefinition.quantization` on `HN L (n+1)` (basis
`Def044D1SpectralR51a.basis hκ n`, Lean gauge `staticGauge q`). The classical symbol is
`WickSpectralBridge.evalSym (chart.Φ u) f`, the Sym-level form of `f(w(u))`.

No sorry, admit or custom axiom. Standard axioms only (see the audit at the end of the file).
-/

noncomputable section
open Filter Topology
open scoped ComplexConjugate BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH8

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH6 (GoodFactor pair_list_prod)
open QuantumNLS.FullWickH7 (IsNormClosePrepT hasUniformPairT_of_normClose)
open QuantumNLS.FullWickO1 (bilinear bilinearPoly staticGauge)
open QuantumNLS.FullWickO2 (UR norm_product norm_wick_bilinear_le wick_uniform_pair)
open QuantumNLS.FullWickS1 (orderedWord monomialWord wordSym_monomialWord
  balanced_ordered_word_comparison_uniform)
open QuantumNLS.WickSymbols (Sym Balanced coeffNorm zm pb Mon)
open QuantumNLS.WickBounds (gensym wordSym labelsOf Cfg balanced_pb)
open QuantumNLS.WickSpectralBridge (evalSym evalMon evalSym_zm evalSym_gensym evalSym_wordSym)
open QuantumNLS.FullWickS2 (hasUniformPairT_of_sum_opClose hasUniformStrongT_of_opClose)
open QuantumNLS.UniformStaticR49b (UniformStatic)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (BetheBasis HN)
open QuantumNLS.BetheOccupationGauge (Gauge)

/-! ### Generic Hilbert-space algebra -/

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma adjoint_eq_star (A : E →L[ℂ] E) : A.adjoint = star A :=
  (ContinuousLinearMap.star_eq_adjoint A).symm

/-- Operator-norm symmetry, stated at the `E →L[ℂ] E` instances used in the statements below. -/
lemma norm_sub_comm_clm (A B : E →L[ℂ] E) : ‖A - B‖ = ‖B - A‖ :=
  norm_sub_rev A B

lemma norm_adjoint_eq (A : E →L[ℂ] E) : ‖A.adjoint‖ = ‖A‖ := by
  rw [adjoint_eq_star]
  exact norm_star A

/-- The star of an ordered product is the reversed product of the stars. -/
lemma star_list_prod' {ι : Type*} (T : ι → E →L[ℂ] E) (l : List ι) :
    star (l.map T).prod = ((l.map fun i => star (T i)).reverse).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, star_mul, ih, List.reverse_cons, List.prod_append,
      List.prod_nil, mul_one]

/-- The adjoint of an ordered product is the reversed product of the adjoints. -/
lemma adjoint_list_prod {ι : Type*} (T : ι → E →L[ℂ] E) (l : List ι) :
    (l.map T).prod.adjoint = ((l.map fun i => (T i).adjoint).reverse).prod := by
  simp only [adjoint_eq_star]
  exact star_list_prod' T l

/-- The adjoint of a finite linear combination (conjugate coefficients). -/
lemma adjoint_sub_sum {ι : Type*} (s : Finset ι) (A : E →L[ℂ] E) (c : ι → ℂ)
    (B : ι → E →L[ℂ] E) :
    (A - ∑ i ∈ s, c i • B i).adjoint
      = A.adjoint - ∑ i ∈ s, (starRingEnd ℂ) (c i) • (B i).adjoint := by
  simp only [adjoint_eq_star, star_sub, star_sum, star_smul, Complex.star_def]

end Algebra

/-! ### Classical symbol bounds -/

section Symbols

lemma norm_finsupp_prod_le (φ : ℤ → ℂ) (hφ : ∀ a, ‖φ a‖ ≤ 1) (α : ℤ →₀ ℕ) :
    ‖α.prod (fun a k => φ a ^ k)‖ ≤ 1 := by
  unfold Finsupp.prod
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun a _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hφ a))

lemma norm_evalMon_le (z : ℤ → ℂ) (hz : ∀ a, ‖z a‖ ≤ 1) (p : Mon) :
    ‖WickSpectralBridge.evalMon z p‖ ≤ 1 := by
  unfold WickSpectralBridge.evalMon
  rw [norm_mul]
  exact (mul_le_mul (norm_finsupp_prod_le z hz p.1)
    (norm_finsupp_prod_le (fun a => (starRingEnd ℂ) (z a))
      (fun a => by rw [Complex.norm_conj]; exact hz a) p.2)
    (norm_nonneg _) zero_le_one).trans (by norm_num)

/-- `‖f(z)‖ ≤ ‖f‖_coeff` whenever every coordinate has modulus at most one. -/
lemma norm_evalSym_le (z : ℤ → ℂ) (hz : ∀ a, ‖z a‖ ≤ 1) (f : Sym) :
    ‖evalSym z f‖ ≤ coeffNorm f := by
  rw [CoherentLowerBound.evalSym_expand, coeffNorm]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul]
  calc ‖f.coeff p‖ * ‖WickSpectralBridge.evalMon z p‖
      ≤ ‖f.coeff p‖ * 1 := mul_le_mul_of_nonneg_left (norm_evalMon_le z hz p) (norm_nonneg _)
    _ = ‖f.coeff p‖ := mul_one _

/-- The chart symbol of a unit-norm point is bounded by the coefficient norm. -/
lemma chart_evalSym_norm_le {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {u : L2T L} (hu : ‖u‖ = 1)
    (f : Sym) :
    ‖evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f‖ ≤ coeffNorm f :=
  norm_evalSym_le _ (fun a => RetargetStageR48b.coordinate_le_one hκ u hu a) f

/-- **Symbol bound from a strong symbol.** If `A_N` has norm at most one, the preparations are
normalized, and `a` is a uniform strong symbol of `A`, then `|a| ≤ 1` on `S × Tb`. -/
lemma symbol_le_one_of_strong {X Θ : Type*} {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)]
    [∀ N, NormedSpace ℂ (H N)] {A : ∀ N, H N →L[ℂ] H N} {S : Set X} {Tb : Set Θ}
    {ψ : X → Θ → ∀ N, H N} {a : X → Θ → ℂ}
    (hA : ∀ᶠ N in atTop, ‖A N‖ ≤ 1) (hψ : ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N‖ = 1)
    (h : HasUniformStrongT A S Tb ψ a) :
    ∀ u ∈ S, ∀ t ∈ Tb, ‖a u t‖ ≤ 1 := by
  intro u hu t ht
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hAN, hψN, hN⟩ := (hA.and (hψ.and (h ε hε))).exists
  have hp : ‖ψ u t N‖ = 1 := hψN u hu t ht
  have hd : ‖(A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ ≤ ε := hN u hu t ht
  have e1 : a u t • ψ u t N
      = A N (ψ u t N) - (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    abel
  have hAψ : ‖A N (ψ u t N)‖ ≤ 1 :=
    ((A N).le_opNorm _).trans (by rw [hp, mul_one]; exact hAN)
  calc ‖a u t‖ = ‖a u t • ψ u t N‖ := by rw [norm_smul, hp, mul_one]
    _ = ‖A N (ψ u t N) - (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ := by
        rw [e1]
    _ ≤ ‖A N (ψ u t N)‖ + ‖(A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ :=
        norm_sub_le _ _
    _ ≤ 1 + ε := add_le_add hAψ hd

end Symbols

/-! ### DEF-032 operators: norm and adjoint identities (any Bethe basis, gauge, N ≥ 1) -/

section Operators

variable {L : ℝ} [Fact (0 < L)]

lemma norm_gensym_quant_le {N : ℕ} (hN : 0 < N) (b : BetheBasis L N) (G : Gauge) (a c : ℤ) :
    ‖BalancedWickDefinition.quantization b G (gensym a c)‖ ≤ 1 :=
  (FullWickH1.quantization_coeff_bound hN b G (WickBounds.balanced_zm_ab a c)).trans
    (FullWickS1.coeffNorm_zm _ _).le

/-- The ordered word has adjoint the reversed word of the transposed generators. -/
lemma orderedWord_adjoint {N : ℕ} (hN : 0 < N) (b : BetheBasis L N) (G : Gauge)
    (w : List (ℤ × ℤ)) :
    (orderedWord b G w).adjoint
      = ((w.map fun p => BalancedWickDefinition.quantization b G (gensym p.2 p.1)).reverse).prod := by
  unfold orderedWord
  rw [adjoint_list_prod]
  congr 2
  apply List.map_congr_left
  intro p _
  exact FullWickO1.quantization_bilinear_adjoint hN b G p.1 p.2

/-- The `Sym`-level symbol of a balanced polynomial equals the sum over its monomial words. -/
lemma evalSym_eq_sum_words (z : ℤ → ℂ) {f : Sym} (hf : Balanced f) :
    evalSym z f = ∑ i ∈ f.coeff.support, f.coeff i * evalSym z (wordSym (monomialWord i)) := by
  rw [CoherentLowerBound.evalSym_expand]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [wordSym_monomialWord p (hf p hp), evalSym_zm]

end Operators

/-! ### STATIC clause (parameter predicate `UniformStatic hκ j q`) -/

section Static

variable {L κ : ℝ} [Fact (0 < L)]

lemma evaluate_bilinearPoly_eq (a c : ℤ) (z : ℤ → ℂ) :
    BalancedWickDefinition.evaluate (bilinearPoly a c) z = evalSym z (gensym a c) := by
  rw [FullWickO1.evaluate_bilinearPoly, evalSym_gensym]

/-- One Cartesian generator `W^q_N(c_ab)` with its adjoint, as a `GoodFactor` for `pair_list_prod`
(constants `C = K = 1`). -/
theorem static_gen_good (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (p : ℤ × ℤ) :
    GoodFactor (H := fun n => HN L (n + 1))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (bilinear p.1 p.2))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (bilinear p.2 p.1))
      (fun (p : ℤ × ℤ) (u : L2T L) (_ : Θ) =>
        evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (gensym p.1 p.2))
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) 1 1 p := by
  refine ⟨Filter.Eventually.of_forall fun n => ?_, Filter.Eventually.of_forall fun n => ?_,
    fun u hu t _ => ?_, ?_⟩
  · exact norm_wick_bilinear_le hκ q n p.1 p.2
  · exact norm_wick_bilinear_le hκ q n p.2 p.1
  · exact (chart_evalSym_norm_le hκ hu.1 (gensym p.1 p.2)).trans
      (FullWickS1.coeffNorm_zm _ _).le
  · have h := wick_uniform_pair hκ j q hU Tb R p.1 p.2
    simp only [evaluate_bilinearPoly_eq] at h
    exact h

/-- **Ordered products of generators (static).** The ordered product `E_{a_1b_1} ⋯ E_{a_kb_k}` has the
uniform strong symbol `∏ z_{a_j} conj z_{b_j}` = `evalSym (wordSym w)` on `𝒰_R`, its adjoint the
conjugate, and `‖·‖ ≤ 1` eventually. -/
theorem static_word_pair (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (w : List (ℤ × ℤ)) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => orderedWord (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) w)
      (fun n => ((w.map fun p => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (gensym p.2 p.1)).reverse).prod)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w)) := by
  have hgood : ∀ p ∈ w, GoodFactor (H := fun n => HN L (n + 1))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (bilinear p.1 p.2))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (bilinear p.2 p.1))
      (fun (p : ℤ × ℤ) (u : L2T L) (_ : Θ) =>
        evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (gensym p.1 p.2))
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) 1 1 p :=
    fun p _ => static_gen_good hκ hU Tb R p
  have hp := (pair_list_prod (H := fun n => HN L (n + 1)) _ _ _ (UR (L := L) R) Tb _ 1 1
    zero_le_one zero_le_one w hgood).1
  have e : (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w))
      = (fun (u : L2T L) (t : Θ) => (w.map fun p =>
          evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (gensym p.1 p.2)).prod) := by
    funext u t
    rw [evalSym_wordSym]
    congr 1
    apply List.map_congr_left
    intro p _
    exact (evalSym_gensym _ _ _).symm
  rw [e]
  exact hp

/-- **STATIC clause (parameter predicate `UniformStatic hκ j q`).** For every balanced `f`, the operator
`W^q_N(f)` has the uniform strong symbol `f(w(u))` on `𝒰_R`, and its adjoint `W^q_N(f)^*` has the
conjugate symbol. Proof: the O(1/N) comparison of `balanced_ordered_word_comparison_uniform` (constant
`K`), the ordered products of `static_word_pair`, and the sum transfer `hasUniformPairT_of_sum_opClose`;
the adjoint bound is the star of the same bound. -/
theorem static_poly_pair (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) {f : Sym}
    (hf : Balanced f) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f)
      (fun n => (BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f).adjoint)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f) := by
  obtain ⟨K, hK0, hK⟩ := balanced_ordered_word_comparison_uniform f hf
  have hAB : ∀ᶠ n : ℕ in atTop,
      ‖BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f
        - ∑ i ∈ f.coeff.support, f.coeff i •
            orderedWord (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (monomialWord i)‖
        ≤ K * (n : ℝ)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 := hK L (n + 1) (Nat.succ_pos n) (Def044D1SpectralR51a.basis (L := L) hκ n)
      (staticGauge q)
    unfold FullWickS1.polyWordOp at h1
    rw [norm_sub_comm_clm]
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK0
    apply inv_anti₀ (by exact_mod_cast (show 0 < n from hn))
    push_cast
    linarith
  have hAB' : ∀ᶠ n : ℕ in atTop,
      ‖(BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
          (staticGauge q) f).adjoint
        - ∑ i ∈ f.coeff.support, (starRingEnd ℂ) (f.coeff i) •
            ((monomialWord i).map fun p => BalancedWickDefinition.quantization
              (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (gensym p.2 p.1)).reverse.prod‖
        ≤ K * (n : ℝ)⁻¹ := by
    filter_upwards [hAB] with n hn
    have e : (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
          (staticGauge q) f).adjoint
        - ∑ i ∈ f.coeff.support, (starRingEnd ℂ) (f.coeff i) •
            ((monomialWord i).map fun p => BalancedWickDefinition.quantization
              (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (gensym p.2 p.1)).reverse.prod
        = (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
              (staticGauge q) f
            - ∑ i ∈ f.coeff.support, f.coeff i •
              orderedWord (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q)
                (monomialWord i)).adjoint := by
      rw [adjoint_sub_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [orderedWord_adjoint (Nat.succ_pos n)]
    rw [e, norm_adjoint_eq]
    exact hn
  have hψ : ∀ᶠ n : ℕ in atTop, ∀ u ∈ UR (L := L) R, ∀ t ∈ Tb,
      ‖UniformStaticR49b.product n u‖ ≤ 1 :=
    Filter.Eventually.of_forall fun n u hu t _ => (norm_product n u hu.1).le
  have key := hasUniformPairT_of_sum_opClose (H := fun n => HN L (n + 1)) f.coeff.support
    (fun i n => orderedWord (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q)
      (monomialWord i))
    (fun i n => ((monomialWord i).map fun p => BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (gensym p.2 p.1)).reverse.prod)
    f.coeff
    (fun i (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym (monomialWord i)))
    (A := fun n => BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f)
    (A' := fun n => (BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f).adjoint)
    (S := UR (L := L) R) (Tb := Tb)
    (ψ := fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
    hK0 hAB hAB' hψ (fun i _ => static_word_pair hκ hU Tb R (monomialWord i))
  have hfun : (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f)
      = (fun (u : L2T L) (t : Θ) => ∑ i ∈ f.coeff.support, f.coeff i *
          evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym (monomialWord i))) := by
    funext u t
    exact evalSym_eq_sum_words _ hf
  rw [hfun]
  exact key

/-- **Norm-close preparations (static).** Uniformly norm-close normalized preparations `ψ'` of the
static product state keep the static pair with the same symbol `f(w(u))` and its conjugate. -/
theorem static_poly_normClose (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) {f : Sym}
    (hf : Balanced f) {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (n + 1)}
    (hprep : IsNormClosePrepT (H := fun n => HN L (n + 1)) ψ'
      (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f)
      (fun n => (BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f).adjoint)
      (UR (L := L) R) Tb ψ'
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f) :=
  hasUniformPairT_of_normClose (C := coeffNorm f) (K := coeffNorm f)
    (Filter.Eventually.of_forall fun n => FullWickH1.quantization_coeff_bound (N := n + 1)
      (Nat.succ_pos n) (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) hf)
    (Filter.Eventually.of_forall fun n => (norm_adjoint_eq _).trans_le
      (FullWickH1.quantization_coeff_bound (N := n + 1) (Nat.succ_pos n)
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) hf))
    (fun u hu _ _ => chart_evalSym_norm_le hκ hu.1 f)
    (static_poly_pair hκ hU Tb R hf) hprep.2

/-- **Selected-witness corollary (static).** The static pair of `static_poly_pair` at the Q06 selected
witnesses (`UniformStaticR49b.selected_uniform_static`; gauge `RetargetSelectionR49b.sectorGauge`).
This is a separate statement; the theorems above use the static input only as a parameter predicate. -/
theorem static_poly_pair_selected (hκ : 0 < κ) {Θ : Type*} (Tb : Set Θ) (R : ℝ) {f : Sym}
    (hf : Balanced f) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n)
        (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) f)
      (fun n => (BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n)
        (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) f).adjoint)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f) :=
  static_poly_pair hκ (UniformStaticR49b.selected_uniform_static (L := L) hκ) Tb R hf

/-- **Scaled Dirac commutator (static).** `-iN[W^q_N(f), W^q_N(g)]` has the uniform strong symbol
`{f,g}(w(u))`, the symbol of the bracket polynomial `pb S f g`, on `𝒰_R` (eq:full-Dirac-bound). -/
theorem static_dirac (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) {f g : Sym}
    (hf : Balanced f) (hg : Balanced g) {S : Finset ℤ} (hSf : labelsOf f ⊆ S)
    (hSg : labelsOf g ⊆ S) :
    HasUniformStrongT (H := fun n => HN L (n + 1))
      (fun n => (-(Complex.I) * ((n + 1 : ℕ) : ℂ)) •
        (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f
          * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
              (staticGauge q) g
          - BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
              (staticGauge q) g
          * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
              (staticGauge q) f))
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (pb S f g)) := by
  have hB := (static_poly_pair hκ hU Tb R (balanced_pb S hf hg)).1
  refine hasUniformStrongT_of_opClose (K := |Cfg f g + Cfg g f|) (M := 1) (abs_nonneg _) ?_ ?_ hB
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h := FullWickH1.quantization_Dirac_bound (N := n + 1) (Nat.succ_pos n)
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) hf hg hSf hSg
    refine h.trans ?_
    refine mul_le_mul (le_abs_self _) ?_ (by positivity) (abs_nonneg _)
    apply inv_anti₀ (by exact_mod_cast (show 0 < n from hn))
    push_cast
    linarith
  · exact Filter.Eventually.of_forall fun n u hu t _ => (norm_product n u hu.1).le

end Static

end QuantumNLS.FullWickH8

#print axioms QuantumNLS.FullWickH8.norm_sub_comm_clm
#print axioms QuantumNLS.FullWickH8.norm_adjoint_eq
#print axioms QuantumNLS.FullWickH8.adjoint_list_prod
#print axioms QuantumNLS.FullWickH8.adjoint_sub_sum
#print axioms QuantumNLS.FullWickH8.norm_evalSym_le
#print axioms QuantumNLS.FullWickH8.symbol_le_one_of_strong
#print axioms QuantumNLS.FullWickH8.orderedWord_adjoint
#print axioms QuantumNLS.FullWickH8.evalSym_eq_sum_words
#print axioms QuantumNLS.FullWickH8.static_gen_good
#print axioms QuantumNLS.FullWickH8.static_word_pair
#print axioms QuantumNLS.FullWickH8.static_poly_pair
#print axioms QuantumNLS.FullWickH8.static_poly_normClose
#print axioms QuantumNLS.FullWickH8.static_poly_pair_selected
#print axioms QuantumNLS.FullWickH8.static_dirac

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.FullWickH8." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickH8." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          (name.toString.splitOn "RB7BindFinal").length > 1 ||
          (name.toString.splitOn "DEF033_package").length > 1 ||
          name.components.any (fun c => c.toString == "RegularCut") ||
          name == ``QuantumNLS.UniformStaticR31m.GaugeRetargetingRD51987CAInput ||
          name == ``QuantumNLS.UniformStaticR31m.uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.retarget_and_uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.uniform_static_intermediate then
        throwError "Excluded dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"FullWickH8 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no held identifiers."
