import QuantumNLS.Ext025LGP07
import QuantumNLS.Ext025LGP07Spec

/-!
# EXT-025 layer A (completion): FULL contract theorem for FIN-EXT025-GP-07

COMPLETES the frozen `Ext025LGP07` (sha256 f3738ed45f34a2657042cb00182618c33a8d2954c6d698dba993aee5e3f7d32c, not
edited) by the clause that module left open: identification of the form domain with the domain
of the spectral square root `(T+c)^{1/2}`.

Exact source text (FINAL_EXTERNAL_THEOREM_INSTANCES.json, sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782, instance
`FIN-EXT025-GP-07`, "Representation of a densely defined closed semibounded quadratic form"):

* Hypotheses: "The quadratic form is densely defined, Hermitian, closed in its shifted form
  norm and bounded below on a complex Hilbert space."
* Conclusion: "It has a unique associated selfadjoint operator with the same form domain;
  membership in the operator domain is characterized by representing the form against every
  form-domain test vector by an ambient Hilbert vector."
* Normalization: "Dense domain is explicit. Selfadjointness of a merely formal differential
  expression is not inferred."

Hypotheses = the raw structure `Ext025B7ClosedForm.FormData` (as in the frozen module).

`contract_GP07_full` has the following conjuncts (for `F : FormData E`):
1. (frozen) existence of a selfadjoint `T` with the printed domain characterization
   (`x ∈ D(T), T x = f` iff `x ∈ F.domain` and `q(v,x) = <v,f>` for all `v ∈ F.domain`);
2. (frozen) uniqueness of such `T`;
3. (frozen) the spectral-free form-domain clauses (`D(T) ⊆ F.domain`, `q(v,x) = <v,Tx>`, `D(T)` is
   a form core, form domain of `T` = `F.domain`);
4. (NEW) the SPECTRAL SQUARE ROOT clause: for every projection-valued measure `P` of `T` (that is,
   `T` is the frozen maximal Borel integral `operator P (t ↦ t)` of `Ext025B9Bridges`), the
   spectral square root `S = (T+c)^{1/2} := operator P (t ↦ sqrt(t+c))` with `c = 1 - F.bound`
   satisfies
   (a) `D(S) = F.domain` (the form domain IS the domain of the square root);
   (b) `S` is selfadjoint and nonnegative;
   (c) `q(v,u) + c <v,u> = <S v, S u>` for all `v,u ∈ F.domain` (the shifted form is the square of
       the root; this is the printed representation `q + c = ‖S ·‖²` on the exact form domain);
   (d) `S ∘ S = T + c` with exact domains (`x ∈ D(T), T x = f` iff `x ∈ D(S), S x ∈ D(S),
       S (S x) = f + c x`), i.e. `S` really is the square root of the constructed operator.

Hypothesis note (PRECISE, for the reviewer).  The square-root clause 4 quantifies over spectral
measures `P` of `T`.  This is the repository's formalization of the standing input "A selfadjoint
operator has a projection-valued spectral measure" (the printed hypothesis of FIN-EXT025-GP-08 and
the premise of the frozen modules `Ext025B8*`/`Ext025B9*`).  The spectral THEOREM (existence of `P`
for an arbitrary selfadjoint `T`) is neither in Mathlib nor in the frozen modules, and is NOT proved
here; clause 4 is vacuous for a `T` that is given no `P`.  Clauses 1-3 do not use `P`.

Proof of clause 4 (all steps use the frozen calculus; `Ext025LGP07Spec` for the inner products):
* `T`-side: `⟪x, T x⟫ = ∫ t dμ_x`, and the form lower bound gives `μ_x((-∞, b)) = 0`
  (`Spec.support_ge`);
* for `u ∈ D(T)`: `u ∈ D(S)` and `‖S u‖² = Re q(u,u) + c‖u‖² = ‖u‖_F²` (`hA`);
* `F.domain ⊆ D(S)`: form-core approximation + closedness of the selfadjoint `S` (graph limit);
* `D(S) ⊆ F.domain`: spectral windows `P([-n,n]) x ∈ D(T)` are form-Cauchy and `F.closed`;
* polarization: `S` restricted to the form space is a linear isometry, giving (c);
* (d) from (c), selfadjointness of `S` (frozen `real_selfAdjoint`) and the adjoint criterion.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Filter Topology MeasureTheory
open scoped InnerProductSpace LinearPMap ENNReal

namespace QuantumNLS.Ext025L

open QuantumNLS.Ext025B7ClosedForm
open BetheChargeResolution QuantumNLS.Ext025B6PVM
open QuantumNLS.Ext025B9MaximalIntegral QuantumNLS.Ext025B9IntegralDomain
open QuantumNLS.Ext025L.Spec

universe u

/-- The shifted square-root symbol `t ↦ sqrt(t + c)`. -/
def rootSym (c : ℝ) : ℝ → ℂ := fun t => ((Real.sqrt (t + c) : ℝ) : ℂ)

theorem rootSym_meas (c : ℝ) : Measurable (rootSym c) :=
  Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
    (measurable_id.add measurable_const))

/-- The spectral square root `(T+c)^{1/2}` of the operator with spectral measure `P`, as the
frozen maximal Borel integral of the symbol `t ↦ sqrt(t+c)`. -/
def sqrtOp {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : ProjectionMeasure E) (c : ℝ) : E →ₗ.[ℂ] E :=
  operator P (rootSym c) (rootSym_meas c)

theorem sqrtOp_selfAdjoint {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (P : ProjectionMeasure E) (c : ℝ) : IsSelfAdjoint (sqrtOp P c) :=
  QuantumNLS.Ext025B9SelfAdjoint.real_selfAdjoint P (fun t => Real.sqrt (t + c))
    (Real.continuous_sqrt.measurable.comp (measurable_id.add measurable_const))

section generic
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

/-- For a vector of the domain of `t`, with `t + c ≥ 0` almost everywhere for its scalar
spectral measure: it lies in the domain of the root and `‖S u‖² = Re⟪u, T u⟫ + c‖u‖²`. -/
theorem root_domain_norm (c : ℝ) (u : E) (hu : u ∈ domain P idSym)
    (hc : ∀ᵐ t ∂scalarMeasure P u, 0 ≤ t + c) :
    ∃ h : u ∈ domain P (rootSym c),
      ‖operator P (rootSym c) (rootSym_meas c) ⟨u, h⟩‖ ^ 2 =
        (⟪u, operator P idSym idSym_meas ⟨u, hu⟩⟫_ℂ).re + c * ‖u‖ ^ 2 := by
  have hmem : MemLp idSym 2 (scalarMeasure P u) := (mem_domain P idSym idSym_meas u).mp hu
  have hint : Integrable (fun t : ℝ => t) (scalarMeasure P u) := by
    have := (hmem.integrable (by norm_num)).re
    simpa [idSym] using this
  have hsq : ∀ᵐ t ∂scalarMeasure P u, ‖rootSym c t‖ ^ 2 = t + c := by
    filter_upwards [hc] with t ht
    simp [rootSym, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ht]
  have hintsq : Integrable (fun t => ‖rootSym c t‖ ^ 2) (scalarMeasure P u) :=
    (hint.add (integrable_const c)).congr (hsq.mono fun t ht => ht.symm)
  have hmemS : MemLp (rootSym c) 2 (scalarMeasure P u) :=
    (memLp_two_iff_integrable_sq_norm (rootSym_meas c).aestronglyMeasurable).mpr hintsq
  have hS : u ∈ domain P (rootSym c) := (mem_domain P _ (rootSym_meas c) u).mpr hmemS
  refine ⟨hS, ?_⟩
  have h2 := operator_square P (rootSym c) (rootSym_meas c) ⟨u, hS⟩
  dsimp only at h2
  rw [h2, integral_congr_ae hsq, integral_add hint (integrable_const c), integral_const,
    measureReal_def, scalarMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul,
    operator_inner P idSym idSym_meas u hu]
  have : (∫ t, idSym t ∂scalarMeasure P u).re = ∫ t, t ∂scalarMeasure P u := by
    have h : (∫ t, idSym t ∂scalarMeasure P u) = ((∫ t, t ∂scalarMeasure P u : ℝ) : ℂ) :=
      integral_ofReal
    rw [h, Complex.ofReal_re]
  rw [this]
  ring

end generic

/-- Squared norm in the shifted form space. -/
theorem normV_sq {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : FormData E) (z : F.domain) :
    ‖toV (F := F) z‖ ^ 2 = (F.q z z).re + (1 - F.bound) * ‖(z : E)‖ ^ 2 := by
  have h1 : ‖toV (F := F) z‖ ^ 2 = (⟪toV (F := F) z, toV (F := F) z⟫_ℂ).re :=
    norm_sq_eq_re_inner (𝕜 := ℂ) _
  rw [h1]
  exact formInner_re F (toV (F := F) z)

/-- `LinearPMap` equality gives pointwise equality on the (propositionally) equal vectors. -/
theorem pmap_congr {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {A B : E →ₗ.[ℂ] E} (h : A = B) (x : A.domain) (y : B.domain) (hxy : (x : E) = (y : E)) :
    A x = B y := by
  subst h
  have : x = y := Subtype.ext hxy
  rw [this]

/-- The square-root clauses for a given square root `S` of the operator `T + c`, `c = 1 - bound`. -/
def GP07_root_prop {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : FormData E) (T S : E →ₗ.[ℂ] E) : Prop :=
  (∀ x : E, x ∈ S.domain ↔ x ∈ F.domain) ∧
  IsSelfAdjoint S ∧
  (∀ x : S.domain, 0 ≤ (⟪(x : E), S x⟫_ℂ).re) ∧
  (∀ (v u : F.domain) (hv : (v : E) ∈ S.domain) (hu : (u : E) ∈ S.domain),
    F.q v u + ((1 - F.bound : ℝ) : ℂ) * ⟪(v : E), (u : E)⟫_ℂ = ⟪S ⟨v, hv⟩, S ⟨u, hu⟩⟫_ℂ) ∧
  (∀ x f : E, (∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = f) ↔
    ∃ (hx : x ∈ S.domain) (hy : S ⟨x, hx⟩ ∈ S.domain),
      S ⟨S ⟨x, hx⟩, hy⟩ = f + ((1 - F.bound : ℝ) : ℂ) • x)

theorem gp07_root {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : FormData E) (T : E →ₗ.[ℂ] E) (hT : GP07_prop F T) (P : ProjectionMeasure E)
    (hP : operator P (fun t : ℝ => (t : ℂ)) Complex.measurable_ofReal = T) :
    GP07_root_prop F T (sqrtOp P (1 - F.bound)) := by
  have hP' : operator P idSym idSym_meas = T := hP
  clear hP
  -- the frozen contract supplies the form-domain clauses for this `T`
  obtain ⟨T0, hp0, hun0, hfd0⟩ := gp07_main F
  have hTT0 : T = T0 := hun0 T hT
  subst hTT0
  subst hP'
  obtain ⟨hdomF, hq, hcore, -⟩ := hfd0
  obtain ⟨hsa, hrep⟩ := hT
  -- lower bound of the identity operator on its domain
  have hlb : ∀ (x : E) (hx : x ∈ domain P idSym),
      F.bound * ‖x‖ ^ 2 ≤ (⟪x, operator P idSym idSym_meas ⟨x, hx⟩⟫_ℂ).re := by
    intro x hx
    have hxF : x ∈ F.domain := hdomF ⟨x, hx⟩
    have h1 : F.q ⟨x, hxF⟩ ⟨x, hxF⟩ = ⟪x, operator P idSym idSym_meas ⟨x, hx⟩⟫_ℂ :=
      hq ⟨x, hx⟩ hxF ⟨x, hxF⟩
    have h2 : F.bound * ‖x‖ ^ 2 ≤ (F.q ⟨x, hxF⟩ ⟨x, hxF⟩).re := F.lower ⟨x, hxF⟩
    rw [h1] at h2
    exact h2
  have hsupp := support_ge P F.bound hlb
  have hfn : ∀ z : F.domain, Real.sqrt ((F.q z z).re + (1 - F.bound) * ‖(z : E)‖ ^ 2) =
      ‖toV (F := F) z‖ := fun z => (norm_eq F (toV (F := F) z)).symm
  -- (A') vectors of D(T) lie in D(S) with the form norm
  have hA : ∀ (y : E) (hy : y ∈ domain P idSym),
      ∃ hS : y ∈ domain P (rootSym (1 - F.bound)),
        ‖operator P (rootSym (1 - F.bound)) (rootSym_meas _) ⟨y, hS⟩‖ ^ 2 =
          ‖toV (F := F) ⟨y, hdomF ⟨y, hy⟩⟩‖ ^ 2 := by
    intro y hy
    have hae : ∀ᵐ t ∂scalarMeasure P y, 0 ≤ t + (1 - F.bound) := by
      have h0 : ∀ᵐ t ∂scalarMeasure P y, t ∉ Set.Iio F.bound :=
        measure_eq_zero_iff_ae_notMem.mp (hsupp y)
      filter_upwards [h0] with t ht
      have : F.bound ≤ t := not_lt.mp ht
      linarith
    obtain ⟨hS, hn⟩ := root_domain_norm P (1 - F.bound) y hy hae
    refine ⟨hS, ?_⟩
    rw [hn, normV_sq]
    have hF : y ∈ F.domain := hdomF ⟨y, hy⟩
    have h1 : F.q ⟨y, hF⟩ ⟨y, hF⟩ = ⟪y, operator P idSym idSym_meas ⟨y, hy⟩⟫_ℂ :=
      hq ⟨y, hy⟩ hF ⟨y, hF⟩
    change _ = (F.q ⟨y, hF⟩ ⟨y, hF⟩).re + (1 - F.bound) * ‖y‖ ^ 2
    rw [h1]
  -- distances in the root equal distances in the form space, on D(T)
  have hdistS : ∀ (y y' : E) (hy : y ∈ domain P idSym) (hy' : y' ∈ domain P idSym)
      (hSy : y ∈ domain P (rootSym (1 - F.bound))) (hSy' : y' ∈ domain P (rootSym (1 - F.bound))),
      ‖operator P (rootSym (1 - F.bound)) (rootSym_meas _) ⟨y, hSy⟩ -
        operator P (rootSym (1 - F.bound)) (rootSym_meas _) ⟨y', hSy'⟩‖ =
      ‖toV (F := F) ⟨y, hdomF ⟨y, hy⟩⟩ - toV (F := F) ⟨y', hdomF ⟨y', hy'⟩⟩‖ := by
    intro y y' hy hy' hSy hSy'
    have hyy : y - y' ∈ domain P idSym := Submodule.sub_mem _ hy hy'
    obtain ⟨hS'', hn''⟩ := hA (y - y') hyy
    have e1 : operator P (rootSym (1 - F.bound)) (rootSym_meas _) ⟨y - y', hS''⟩ =
        operator P (rootSym (1 - F.bound)) (rootSym_meas _) ⟨y, hSy⟩ -
        operator P (rootSym (1 - F.bound)) (rootSym_meas _) ⟨y', hSy'⟩ := by
      have := (operator P (rootSym (1 - F.bound)) (rootSym_meas _)).map_sub ⟨y, hSy⟩ ⟨y', hSy'⟩
      rw [← this]
      rfl
    have e2 : toV (F := F) ⟨y - y', hdomF ⟨y - y', hyy⟩⟩ =
        toV (F := F) ⟨y, hdomF ⟨y, hy⟩⟩ - toV (F := F) ⟨y', hdomF ⟨y', hy'⟩⟩ := rfl
    rw [e1] at hn''
    rw [e2] at hn''
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn''
  have hSsa : IsSelfAdjoint (sqrtOp P (1 - F.bound)) := sqrtOp_selfAdjoint P _
  have hSclosed : IsClosed (((sqrtOp P (1 - F.bound)).graph : Submodule ℂ (E × E)) : Set (E × E)) :=
    hSsa.isClosed
  -- (B') the form domain lies in D(S), and S is isometric for the form norm
  have hB : ∀ x : F.domain, ∃ hxS : (x : E) ∈ (sqrtOp P (1 - F.bound)).domain,
      ‖sqrtOp P (1 - F.bound) ⟨(x : E), hxS⟩‖ = ‖toV (F := F) x‖ := by
    intro x
    obtain ⟨u, hu, h1, h2⟩ := hcore x
    have hAu : ∀ n, ∃ hS : (u n : E) ∈ domain P (rootSym (1 - F.bound)),
        ‖operator P (rootSym (1 - F.bound)) (rootSym_meas _) ⟨(u n : E), hS⟩‖ ^ 2 =
          ‖toV (F := F) ⟨(u n : E), hu n⟩‖ ^ 2 := fun n => hA (u n : E) (u n).property
    choose hS hSn using hAu
    set z : ℕ → E := fun n => operator P (rootSym (1 - F.bound)) (rootSym_meas _)
      ⟨(u n : E), hS n⟩ with hz
    set a : ℕ → F.domain := fun n => ⟨(u n : E), hu n⟩ with ha
    have hV : Tendsto (fun n => ‖toV (F := F) (x - a n)‖) atTop (𝓝 0) :=
      h1.congr fun n => hfn (x - a n)
    have haV : Tendsto (fun n => toV (F := F) (a n)) atTop (𝓝 (toV (F := F) x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine hV.congr fun n => ?_
      rw [norm_sub_rev]
      rfl
    have hcV := haV.cauchySeq
    have hdist : ∀ n m, dist (z n) (z m) = dist (toV (F := F) (a n)) (toV (F := F) (a m)) := by
      intro n m
      rw [dist_eq_norm, dist_eq_norm]
      exact hdistS (u n : E) (u m : E) (u n).property (u m).property (hS n) (hS m)
    have hzC : CauchySeq z := by
      rw [Metric.cauchySeq_iff] at hcV ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hcV ε hε
      exact ⟨N, fun m hm n hn => by rw [hdist]; exact hN m hm n hn⟩
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hzC
    have hmem : ((x : E), y) ∈ (sqrtOp P (1 - F.bound)).graph := by
      refine hSclosed.mem_of_tendsto (f := fun n => ((u n : E), z n)) (b := atTop)
        (h2.prodMk_nhds hy) (Eventually.of_forall fun n => ?_)
      exact (sqrtOp P (1 - F.bound)).mem_graph ⟨(u n : E), hS n⟩
    obtain ⟨w, hw⟩ := (sqrtOp P (1 - F.bound)).mem_graph_iff.mp hmem
    have hwx : (w : E) = (x : E) := hw.1
    have hwy : sqrtOp P (1 - F.bound) w = y := hw.2
    have hxS : (x : E) ∈ (sqrtOp P (1 - F.bound)).domain := by
      rw [← hwx]; exact w.property
    refine ⟨hxS, ?_⟩
    have hxw : (⟨(x : E), hxS⟩ : (sqrtOp P (1 - F.bound)).domain) = w := Subtype.ext hwx.symm
    rw [hxw, hwy]
    have hnorm : ∀ n, ‖z n‖ = ‖toV (F := F) (a n)‖ := fun n =>
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hSn n)
    exact tendsto_nhds_unique (hy.norm.congr fun n => (hnorm n)) haV.norm
  choose hBS hBn using hB
  -- (A) D(S) ⊆ form domain, via spectral windows
  have hAin : ∀ x : E, x ∈ (sqrtOp P (1 - F.bound)).domain → x ∈ F.domain := by
    intro x hx
    let s : ℕ → Set ℝ := fun n => Set.Icc (-(n : ℝ)) n
    have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Icc
    have hmono : Monotone s := fun m n hmn =>
      Set.Icc_subset_Icc (neg_le_neg (Nat.cast_le.mpr hmn)) (Nat.cast_le.mpr hmn)
    have hu : ⋃ n, s n = Set.univ := by
      apply Set.eq_univ_of_forall
      intro t
      obtain ⟨n, hn⟩ := exists_nat_ge |t|
      exact Set.mem_iUnion.mpr ⟨n, abs_le.mp hn⟩
    have hvT : ∀ n : ℕ, P.toFun (s n) x ∈ domain P idSym := fun n =>
      bounded_window_mem P idSym idSym_meas (s n) (hs n) n (fun t ht => by
        change ‖(t : ℂ)‖ ≤ n
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ht) x
    have hvS : ∀ n : ℕ, P.toFun (s n) x ∈ domain P (rootSym (1 - F.bound)) := fun n =>
      projection_mem P (rootSym (1 - F.bound)) (s n) (hs n) x hx
    have hSv : ∀ n : ℕ, operator P (rootSym (1 - F.bound)) (rootSym_meas _)
        ⟨P.toFun (s n) x, hvS n⟩ = P.toFun (s n)
          (operator P (rootSym (1 - F.bound)) (rootSym_meas _) ⟨x, hx⟩) := fun n =>
      projection_commutes P (rootSym (1 - F.bound)) (rootSym_meas _) (s n) (hs n) x hx
    have hvx : Tendsto (fun n : ℕ => P.toFun (s n) x) atTop (𝓝 x) :=
      Ext025B7SpectralCompression.exhaustion_strong P s hs hmono hu x
    have hSvx : Tendsto (fun n : ℕ => operator P (rootSym (1 - F.bound)) (rootSym_meas _)
        ⟨P.toFun (s n) x, hvS n⟩) atTop
        (𝓝 (operator P (rootSym (1 - F.bound)) (rootSym_meas _) ⟨x, hx⟩)) :=
      (Ext025B7SpectralCompression.exhaustion_strong P s hs hmono hu _).congr
        fun n => (hSv n).symm
    have hcauch := hSvx.cauchySeq
    let a : ℕ → F.domain := fun n => ⟨P.toFun (s n) x, hdomF ⟨P.toFun (s n) x, hvT n⟩⟩
    have hraw : ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, ∀ m ≥ M,
        Real.sqrt ((F.q (a n - a m) (a n - a m)).re +
          (1 - F.bound) * ‖((a n - a m : F.domain) : E)‖ ^ 2) < ε := by
      intro ε hε
      obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hcauch ε hε
      refine ⟨M, fun n hn m hm => ?_⟩
      rw [hfn]
      have := hdistS (P.toFun (s n) x) (P.toFun (s m) x) (hvT n) (hvT m) (hvS n) (hvS m)
      have h3 := hM n hn m hm
      rw [dist_eq_norm] at h3
      change ‖toV (F := F) (a n) - toV (F := F) (a m)‖ < ε
      exact lt_of_eq_of_lt this.symm h3
    obtain ⟨vv, hvv, -⟩ := F.closed a x hraw hvx
    exact hvv ▸ vv.property
  -- the root, as a linear isometry on the form space
  let Ψ : FormSpace F →ₗᵢ[ℂ] E :=
    { toFun := fun v => sqrtOp P (1 - F.bound) ⟨ambient F v, hBS (toDomain F v)⟩
      map_add' := fun v w => by
        have := (sqrtOp P (1 - F.bound)).map_add ⟨ambient F v, hBS (toDomain F v)⟩
          ⟨ambient F w, hBS (toDomain F w)⟩
        exact this
      map_smul' := fun c v => by
        have := (sqrtOp P (1 - F.bound)).map_smul c ⟨ambient F v, hBS (toDomain F v)⟩
        exact this
      norm_map' := fun v => hBn (toDomain F v) }
  have hform : ∀ (v u : F.domain) (hv : (v : E) ∈ (sqrtOp P (1 - F.bound)).domain)
      (hu : (u : E) ∈ (sqrtOp P (1 - F.bound)).domain),
      F.q v u + ((1 - F.bound : ℝ) : ℂ) * ⟪(v : E), (u : E)⟫_ℂ =
        ⟪sqrtOp P (1 - F.bound) ⟨v, hv⟩, sqrtOp P (1 - F.bound) ⟨u, hu⟩⟫_ℂ := by
    intro v u hv hu
    have h := Ψ.inner_map_map (toV (F := F) v) (toV (F := F) u)
    rw [inner_eq F (toV (F := F) v) (toV (F := F) u)] at h
    exact h.symm
  -- assemble
  unfold GP07_root_prop
  refine ⟨fun x => ⟨hAin x, fun hx => ?_⟩, hSsa, ?_, hform, ?_⟩
  · exact (hBS ⟨x, hx⟩)
  · -- nonnegativity
    intro x
    have hint := operator_inner P (rootSym (1 - F.bound)) (rootSym_meas _) (x : E) x.property
    have hx : (⟨(x : E), x.property⟩ : (sqrtOp P (1 - F.bound)).domain) = x := rfl
    change 0 ≤ (⟪(x : E), operator P (rootSym (1 - F.bound)) (rootSym_meas _) ⟨(x : E), x.property⟩⟫_ℂ).re
    rw [hint]
    have h : (∫ t, rootSym (1 - F.bound) t ∂scalarMeasure P (x : E)) =
        ((∫ t, Real.sqrt (t + (1 - F.bound)) ∂scalarMeasure P (x : E) : ℝ) : ℂ) :=
      integral_ofReal
    rw [h, Complex.ofReal_re]
    exact integral_nonneg fun t => Real.sqrt_nonneg _
  · -- S ∘ S = T + c
    intro x f
    constructor
    · rintro ⟨hx, hTx⟩
      have hxF : x ∈ F.domain := hdomF ⟨x, hx⟩
      have hxS : x ∈ (sqrtOp P (1 - F.bound)).domain := (hBS ⟨x, hxF⟩)
      have hdense : Dense ((sqrtOp P (1 - F.bound)).domain : Set E) := hSsa.dense_domain
      have hadj : ∀ w : (sqrtOp P (1 - F.bound)).domain,
          ⟪f + ((1 - F.bound : ℝ) : ℂ) • x, (w : E)⟫_ℂ =
            ⟪sqrtOp P (1 - F.bound) ⟨x, hxS⟩, sqrtOp P (1 - F.bound) w⟫_ℂ := by
        intro w
        have hwF : (w : E) ∈ F.domain := hAin w w.property
        have hf := hform ⟨w, hwF⟩ ⟨x, hxF⟩ w.property hxS
        have hqw : F.q ⟨w, hwF⟩ ⟨x, hxF⟩ = ⟪(w : E), f⟫_ℂ := by
          have := (hrep x f).mp ⟨hx, hTx⟩
          obtain ⟨hxF', hq'⟩ := this
          exact hq' ⟨w, hwF⟩
        rw [hqw] at hf
        have hf' : ⟪(w : E), f⟫_ℂ + ((1 - F.bound : ℝ) : ℂ) * ⟪(w : E), x⟫_ℂ =
            ⟪sqrtOp P (1 - F.bound) w, sqrtOp P (1 - F.bound) ⟨x, hxS⟩⟫_ℂ := hf
        calc ⟪f + ((1 - F.bound : ℝ) : ℂ) • x, (w : E)⟫_ℂ
            = (starRingEnd ℂ) ⟪(w : E), f + ((1 - F.bound : ℝ) : ℂ) • x⟫_ℂ :=
              (inner_conj_symm _ _).symm
          _ = (starRingEnd ℂ) (⟪(w : E), f⟫_ℂ + ((1 - F.bound : ℝ) : ℂ) * ⟪(w : E), x⟫_ℂ) := by
              rw [inner_add_right, inner_smul_right]
          _ = (starRingEnd ℂ) ⟪sqrtOp P (1 - F.bound) w, sqrtOp P (1 - F.bound) ⟨x, hxS⟩⟫_ℂ := by
              rw [hf']
          _ = _ := inner_conj_symm _ _
      have hy : sqrtOp P (1 - F.bound) ⟨x, hxS⟩ ∈ (sqrtOp P (1 - F.bound))†.domain :=
        LinearPMap.mem_adjoint_domain_of_exists _
          ⟨f + ((1 - F.bound : ℝ) : ℂ) • x, hadj⟩
      have hval := LinearPMap.adjoint_apply_eq hdense
        (⟨sqrtOp P (1 - F.bound) ⟨x, hxS⟩, hy⟩ : (sqrtOp P (1 - F.bound))†.domain) hadj
      have hEq : (sqrtOp P (1 - F.bound))† = sqrtOp P (1 - F.bound) := hSsa
      have hdomEq : ((sqrtOp P (1 - F.bound))†).domain = (sqrtOp P (1 - F.bound)).domain := by
        rw [hEq]
      have hy' : sqrtOp P (1 - F.bound) ⟨x, hxS⟩ ∈ (sqrtOp P (1 - F.bound)).domain := by
        have hy2 := hy
        rw [hdomEq] at hy2
        exact hy2
      refine ⟨hxS, hy', ?_⟩
      have hc := pmap_congr hEq ⟨_, hy⟩ ⟨_, hy'⟩ rfl
      rw [← hc]
      exact hval
    · rintro ⟨hx, hy, hSSx⟩
      have hxF : x ∈ F.domain := hAin x hx
      refine (hrep x f).mpr ⟨hxF, fun v => ?_⟩
      have hvS : (v : E) ∈ (sqrtOp P (1 - F.bound)).domain := hBS v
      have hf := hform v ⟨x, hxF⟩ hvS hx
      have hsym : ⟪sqrtOp P (1 - F.bound) ⟨v, hvS⟩, sqrtOp P (1 - F.bound) ⟨x, hx⟩⟫_ℂ =
          ⟪(v : E), sqrtOp P (1 - F.bound) ⟨sqrtOp P (1 - F.bound) ⟨x, hx⟩, hy⟩⟫_ℂ :=
        real_formalAdjoint P (fun t => Real.sqrt (t + (1 - F.bound)))
          (Real.continuous_sqrt.measurable.comp (measurable_id.add measurable_const))
          ⟨v, hvS⟩ ⟨_, hy⟩
      rw [hSSx, inner_add_right, inner_smul_right] at hsym
      have hf' : F.q v ⟨x, hxF⟩ + ((1 - F.bound : ℝ) : ℂ) * ⟪(v : E), x⟫_ℂ =
          ⟪sqrtOp P (1 - F.bound) ⟨v, hvS⟩, sqrtOp P (1 - F.bound) ⟨x, hx⟩⟫_ℂ := hf
      change F.q v ⟨x, hxF⟩ = ⟪(v : E), f⟫_ℂ
      linear_combination hf'.trans hsym


universe u'

/-- FIN-EXT025-GP-07 as a Lean theorem, FULL.  Conjuncts 1-3 are the frozen
`Ext025LGP07.contract_GP07`; conjunct 4 is the spectral square-root identification
(`D(S) = F.domain`, `S` selfadjoint nonnegative, `q(v,u) + c<v,u> = <S v, S u>`, `S∘S = T + c`)
for every projection-valued measure `P` of `T` (`T = ∫ t dP`), `c = 1 - F.bound`. -/
theorem contract_GP07_full {E : Type u'} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (F : QuantumNLS.Ext025B7ClosedForm.FormData E) :
    ∃ T : E →ₗ.[ℂ] E,
      (IsSelfAdjoint T ∧
        ∀ x f : E, (∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = f) ↔
          ∃ hx : x ∈ F.domain, ∀ v : F.domain, F.q v ⟨x, hx⟩ = ⟪(v : E), f⟫_ℂ) ∧
      (∀ T' : E →ₗ.[ℂ] E, GP07_prop F T' → T' = T) ∧ GP07_formdomain F T ∧
      (∀ P : ProjectionMeasure E,
        operator P (fun t : ℝ => (t : ℂ)) Complex.measurable_ofReal = T →
          GP07_root_prop F T (sqrtOp P (1 - F.bound))) := by
  obtain ⟨T, hp, hu, hf⟩ := gp07_main F
  exact ⟨T, hp, hu, hf, fun P hP => gp07_root F T hp P hP⟩

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.gp07_root
#print axioms QuantumNLS.Ext025L.contract_GP07_full
