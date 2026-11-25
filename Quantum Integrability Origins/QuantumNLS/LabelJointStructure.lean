import QuantumNLS.LabelJointWeak

/-!
# PROP-002 `lem:B3-weak-joint-limit`, part (2c): every joint limit is a graph measure

Source: `source/chapters/propagation/label_periods.tex:59-66`. "If `μ_n(E) = γ(E × {n})`, the
support of `μ_n` lies to the left of the support of `μ_m` when `n < m`. Two such supports can
intersect only at one endpoint. Since the first marginal `μ` is nonatomic, their countably many
possible common endpoints have zero mass. Thus `γ(dt,dn) = μ(dt) δ_{n(t)}(dn)` for a ... integer-valued
function `n(t)` defined `μ`-almost everywhere."

Imports PJ1 `LabelJointWeak` (`d7bdce1d…`, own, frozen).

* `slice γ n` (`= μ_n`), `slice_apply`, `measure_eq_tsum`, `map_fst_eq_tsum`;
* `null_upperCut`, `null_lowerCut`: for a nonatomic `ν` on `ℝ`, `ν{t | ν(t,∞) = 0} = 0` and
  `ν{t | ν(−∞,t) = 0} = 0` (the "one common endpoint" argument);
* **`graph_of_ordering`** (generic): a measure on `ℝ × ℤ` with nonatomic first marginal and the
  support ordering of PJ1's `limit_ordering` equals `(γ.map fst).map (t ↦ (t, g t))` for a measurable
  `g : ℝ → ℤ`;
* **`limit_graph`**: every subsequential joint limit is `μ.map (t ↦ (t, g t))`, `g` measurable;
* **`limit_label_bound`**: the uniform label bound passes to the limit:
  `|g t| ≤ (L/2π)(|t| + 3√(κ/L))` for `μ`-a.e. `t`.
(The monotonicity of `g`, also printed, is not needed downstream and is not stated.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.LabelJointStructure

open QuantumNLS.LabelJointLimit QuantumNLS.LabelTightness QuantumNLS.LabelJointWeak

/-! ## 1. Slices of a measure on `ℝ × ℤ` -/

section Slice

variable (γ : Measure (ℝ × ℤ))

/-- `μ_n(E) = γ(E × {n})`. -/
def slice (n : ℤ) : Measure ℝ := (γ.restrict (univ ×ˢ {n})).map Prod.fst

lemma slice_apply (n : ℤ) {E : Set ℝ} (hE : MeasurableSet E) : slice γ n E = γ (E ×ˢ {n}) := by
  rw [slice, Measure.map_apply measurable_fst hE,
    Measure.restrict_apply (measurable_fst hE)]
  congr 1
  ext ⟨t, k⟩
  simp

lemma measure_eq_tsum {S : Set (ℝ × ℤ)} (hS : MeasurableSet S) :
    γ S = ∑' n : ℤ, γ (((fun t => (t, n)) ⁻¹' S) ×ˢ ({n} : Set ℤ)) := by
  have hU : S = ⋃ n : ℤ, ((fun t => (t, n)) ⁻¹' S) ×ˢ ({n} : Set ℤ) := by
    ext ⟨t, k⟩
    simp only [mem_iUnion, mem_prod, mem_preimage, mem_singleton_iff]
    exact ⟨fun h => ⟨k, h, rfl⟩, fun ⟨n, h, hn⟩ => hn ▸ h⟩
  conv_lhs => rw [hU]
  refine measure_iUnion ?_ fun n => (measurable_prodMk_right hS).prod (measurableSet_singleton n)
  intro n m hnm
  rw [Function.onFun, Set.disjoint_left]
  rintro ⟨t, k⟩ h1 h2
  simp only [mem_prod, mem_preimage, mem_singleton_iff] at h1 h2
  exact hnm (h1.2.symm.trans h2.2)

lemma map_fst_eq_tsum {E : Set ℝ} (hE : MeasurableSet E) :
    γ.map Prod.fst E = ∑' n, slice γ n E := by
  rw [Measure.map_apply measurable_fst hE, measure_eq_tsum γ (measurable_fst hE)]
  congr 1
  funext n
  rw [slice_apply γ n hE]
  rfl

lemma slice_le (n : ℤ) {E : Set ℝ} (hE : MeasurableSet E) : slice γ n E ≤ γ.map Prod.fst E := by
  rw [map_fst_eq_tsum γ hE]
  exact ENNReal.le_tsum (f := fun k => slice γ k E) n

instance slice_noAtoms [NullSingletonClass (γ.map Prod.fst)] (n : ℤ) : NullSingletonClass (slice γ n) :=
  ⟨fun x => le_antisymm ((slice_le γ n (measurableSet_singleton x)).trans
    (measure_singleton x).le) bot_le⟩

end Slice

/-! ## 2. Cut sets of a nonatomic measure are null -/

/-- `ν{t | ν(t, ∞) = 0} = 0` for nonatomic `ν`. -/
lemma null_upperCut (ν : Measure ℝ) [NullSingletonClass ν] : ν {t | ν (Ioi t) = 0} = 0 := by
  set T := {t | ν (Ioi t) = 0}
  have hsub : T ⊆ (⋃ q : {q : ℚ // (q : ℝ) ∈ T}, Ioi ((q : ℚ) : ℝ)) ∪
      {t | t ∈ T ∧ ∀ s ∈ T, t ≤ s} := by
    intro t ht
    by_cases h : ∃ s ∈ T, s < t
    · obtain ⟨s, hs, hst⟩ := h
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hst
      left
      exact mem_iUnion.2 ⟨⟨q, measure_mono_null (Ioi_subset_Ioi hq1.le) hs⟩, hq2⟩
    · right
      push Not at h
      exact ⟨ht, h⟩
  have hss : ({t | t ∈ T ∧ ∀ s ∈ T, t ≤ s} : Set ℝ).Subsingleton := fun a ha b hb =>
    le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)
  exact measure_mono_null hsub (measure_union_null (measure_iUnion_null fun q => q.2)
    (hss.measure_zero ν))

/-- `ν{t | ν(−∞, t) = 0} = 0` for nonatomic `ν`. -/
lemma null_lowerCut (ν : Measure ℝ) [NullSingletonClass ν] : ν {t | ν (Iio t) = 0} = 0 := by
  set T := {t | ν (Iio t) = 0}
  have hsub : T ⊆ (⋃ q : {q : ℚ // (q : ℝ) ∈ T}, Iio ((q : ℚ) : ℝ)) ∪
      {t | t ∈ T ∧ ∀ s ∈ T, s ≤ t} := by
    intro t ht
    by_cases h : ∃ s ∈ T, t < s
    · obtain ⟨s, hs, hst⟩ := h
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hst
      left
      exact mem_iUnion.2 ⟨⟨q, measure_mono_null (Iio_subset_Iio hq2.le) hs⟩, hq1⟩
    · right
      push Not at h
      exact ⟨ht, h⟩
  have hss : ({t | t ∈ T ∧ ∀ s ∈ T, s ≤ t} : Set ℝ).Subsingleton := fun a ha b hb =>
    le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)
  exact measure_mono_null hsub (measure_union_null (measure_iUnion_null fun q => q.2)
    (hss.measure_zero ν))

lemma measurableSet_lowerCut (ν : Measure ℝ) : MeasurableSet {t | ν (Iio t) = 0} := by
  refine IsLowerSet.ordConnected (fun a b hba ha => ?_) |>.measurableSet
  exact measure_mono_null (Iio_subset_Iio hba) ha

/-! ## 3. The graph structure -/

/-- **(2c), generic form.** A measure on `ℝ × ℤ` whose first marginal is nonatomic and whose slices
are ordered (`n < m` ⇒ for every `a`, no `n`-mass right of `a` or no `m`-mass left of `a`) is the
image of its first marginal under `t ↦ (t, g t)` for a measurable `g : ℝ → ℤ`. -/
theorem graph_of_ordering (γ : Measure (ℝ × ℤ)) [NullSingletonClass (γ.map Prod.fst)]
    (hord : ∀ n m : ℤ, n < m → ∀ a : ℝ, γ (Ioi a ×ˢ {n}) = 0 ∨ γ (Iio a ×ˢ {m}) = 0) :
    ∃ g : ℝ → ℤ, Measurable g ∧ γ = (γ.map Prod.fst).map (fun t => (t, g t)) := by
  classical
  set U : ℤ → Set ℝ := fun m => {t | slice γ m (Iio t) = 0}
  have hUm : ∀ m, MeasurableSet (U m) := fun m => measurableSet_lowerCut _
  have hUnull : ∀ m, slice γ m (U m) = 0 := fun m => null_lowerCut _
  have hUc : ∀ n m, n < m → slice γ n (U m)ᶜ = 0 := by
    intro n m hnm
    refine measure_mono_null ?_ (null_upperCut (slice γ n))
    intro a ha
    simp only [mem_compl_iff, U, Set.mem_ofPred_eq] at ha
    rw [slice_apply _ _ measurableSet_Iio] at ha
    show slice γ n (Ioi a) = 0
    rw [slice_apply _ _ measurableSet_Ioi]
    exact (hord n m hnm a).resolve_right ha
  set A : ℤ → Set ℝ := fun m => (U m)ᶜ ∩ ⋂ (k : ℤ) (_ : m < k), U k
  have hAm : ∀ m, MeasurableSet (A m) := fun m =>
    (hUm m).compl.inter (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => hUm k)
  have hAc : ∀ m, slice γ m (A m)ᶜ = 0 := by
    intro m
    have hsub : (A m)ᶜ ⊆ U m ∪ ⋃ (k : ℤ) (_ : m < k), (U k)ᶜ := by
      intro t ht
      by_contra hc
      simp only [mem_union, mem_iUnion, mem_compl_iff, not_or, not_exists, not_not] at hc
      exact ht ⟨hc.1, mem_iInter₂.2 hc.2⟩
    exact measure_mono_null hsub (measure_union_null (hUnull m)
      (measure_iUnion_null fun k => measure_iUnion_null fun hk => hUc m k hk))
  have hdisj : ∀ n m, n ≠ m → ∀ t, t ∈ A n → t ∉ A m := by
    have key : ∀ n m, n < m → ∀ t, t ∈ A n → t ∉ A m := fun n m hnm t hn hm =>
      hm.1 (mem_iInter₂.1 hn.2 m hnm)
    intro n m hnm t hn hm
    rcases lt_or_gt_of_ne hnm with h | h
    · exact key n m h t hn hm
    · exact key m n h t hm hn
  let g : ℝ → ℤ := fun t => if h : ∃ m, t ∈ A m then h.choose else 0
  have hg : ∀ m t, t ∈ A m → g t = m := by
    intro m t ht
    have h : ∃ m, t ∈ A m := ⟨m, ht⟩
    simp only [g, h, dite_true]
    by_contra hne
    exact hdisj _ _ hne t h.choose_spec ht
  have hgpre : ∀ m, g ⁻¹' {m} = A m ∪ ((⋃ k, A k)ᶜ ∩ {_t | m = 0}) := by
    intro m
    ext t
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_compl_iff,
      mem_iUnion, not_exists, Set.mem_ofPred_eq]
    by_cases h : ∃ k, t ∈ A k
    · obtain ⟨k, hk⟩ := h
      rw [hg k t hk]
      constructor
      · rintro rfl; exact Or.inl hk
      · rintro (h | h)
        · by_contra hne; exact hdisj k m hne t hk h
        · exact absurd hk (h.1 k)
    · have h0 : g t = 0 := by simp only [g, h, dite_false]
      push Not at h
      rw [h0]
      constructor
      · rintro rfl; exact Or.inr ⟨h, rfl⟩
      · rintro (h' | h')
        · exact absurd h' (h m)
        · exact h'.2.symm
  have hgm : Measurable g := measurable_to_countable' fun m => by
    rw [hgpre m]
    exact (hAm m).union ((MeasurableSet.iUnion hAm).compl.inter (MeasurableSet.const _))
  have hkey : ∀ m (E : Set ℝ), MeasurableSet E →
      γ.map Prod.fst (E ∩ g ⁻¹' {m}) = slice γ m E := by
    intro m E hE
    have hpm : MeasurableSet (g ⁻¹' {m}) := hgm (measurableSet_singleton m)
    rw [map_fst_eq_tsum γ (hE.inter hpm), tsum_eq_single m]
    · refine measure_inter_conull (measure_mono_null
        (show (g ⁻¹' {m})ᶜ ⊆ (A m)ᶜ from fun t ht hA => ht (hg m t hA)) (hAc m))
    · intro n hn
      refine measure_mono_null (show E ∩ g ⁻¹' {m} ⊆ (A n)ᶜ from fun t ht hA => hn ?_) (hAc n)
      rw [← hg n t hA]
      exact ht.2
  refine ⟨g, hgm, ?_⟩
  ext S hS
  have hG : Measurable fun t => (t, g t) := measurable_id.prodMk hgm
  rw [Measure.map_apply hG hS, measure_eq_tsum γ hS]
  have hdec : (fun t => (t, g t)) ⁻¹' S =
      ⋃ n : ℤ, ((fun t => (t, n)) ⁻¹' S ∩ g ⁻¹' {n}) := by
    ext t
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h => ⟨g t, h, rfl⟩, fun ⟨n, h, hn⟩ => hn ▸ h⟩
  rw [hdec, measure_iUnion]
  · congr 1
    funext n
    rw [hkey n _ (measurable_prodMk_right hS), slice_apply γ n (measurable_prodMk_right hS)]
  · intro n m hnm
    rw [Function.onFun, Set.disjoint_left]
    intro t h1 h2
    exact hnm (h1.2.symm.trans h2.2)
  · exact fun n => (measurable_prodMk_right hS).inter (hgm (measurableSet_singleton n))

/-! ## 4. Application to the joint empirical limits -/

section Seq

variable {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, OnShellBethe L κ (N k)}
  {μ : ProbabilityMeasure ℝ}

/-- **(2c)**: every subsequential joint limit is `μ(dt) δ_{g(t)}(dn)` with `g` measurable. -/
theorem limit_graph [NullSingletonClass (μ : Measure ℝ)]
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {γ : ProbabilityMeasure (ℝ × ℤ)}
    (hγ : Tendsto (fun k => jointP (B (φ k)) (hN (φ k))) atTop (𝓝 γ)) :
    ∃ g : ℝ → ℤ, Measurable g ∧
      (γ : Measure (ℝ × ℤ)) = (μ : Measure ℝ).map (fun t => (t, g t)) := by
  have hmarg : (γ : Measure (ℝ × ℤ)).map Prod.fst = (μ : Measure ℝ) := by
    rw [← ProbabilityMeasure.toMeasure_map, limit_map_fst hconv hφ hγ]
  have : NullSingletonClass ((γ : Measure (ℝ × ℤ)).map Prod.fst) := by rw [hmarg]; infer_instance
  obtain ⟨g, hg, heq⟩ := graph_of_ordering (γ : Measure (ℝ × ℤ))
    fun n m hnm a => limit_ordering hγ hnm a
  exact ⟨g, hg, heq.trans (by rw [hmarg])⟩

/-- The closed set `{(t, n) : |n| ≤ (L/2π)(|t| + 3√(κ/L))}`. -/
def labelBoundSet (L κ : ℝ) : Set (ℝ × ℤ) :=
  {p | |(p.2 : ℝ)| ≤ (L / (2 * Real.pi)) * (|p.1| + 3 * Real.sqrt (κ / L))}

lemma isClosed_labelBoundSet (L κ : ℝ) : IsClosed (labelBoundSet L κ) := by
  have h1 : Continuous fun z : ℤ => (z : ℝ) := continuous_of_discreteTopology
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- **The uniform label bound passes to the limit**: `|g t| ≤ (L/2π)(|t| + 3√(κ/L))`
for `μ`-a.e. `t`. -/
theorem limit_label_bound (hL : 0 < L) (hκ : 0 < κ) {φ : ℕ → ℕ}
    {γ : ProbabilityMeasure (ℝ × ℤ)}
    (hγ : Tendsto (fun k => jointP (B (φ k)) (hN (φ k))) atTop (𝓝 γ))
    {g : ℝ → ℤ} (hg : Measurable g)
    (heq : (γ : Measure (ℝ × ℤ)) = (μ : Measure ℝ).map (fun t => (t, g t))) :
    ∀ᵐ t ∂(μ : Measure ℝ),
      |(g t : ℝ)| ≤ (L / (2 * Real.pi)) * (|t| + 3 * Real.sqrt (κ / L)) := by
  have hF := isClosed_labelBoundSet L κ
  have hone : ∀ k, (jointP (B (φ k)) (hN (φ k)) : Measure (ℝ × ℤ)) (labelBoundSet L κ) = 1 := by
    intro k
    have hc : (jointP (B (φ k)) (hN (φ k)) : Measure (ℝ × ℤ)) (labelBoundSet L κ)ᶜ = 0 := by
      show emp (pts (B (φ k))) _ = 0
      refine emp_eq_zero hF.measurableSet.compl fun j hj => hj ?_
      have hb := label_abs_le_bound hL hκ (hN (φ k)) (B (φ k)) j
      exact hb
    rw [measure_compl hF.measurableSet (measure_ne_top _ _), measure_univ] at hc
    exact le_antisymm prob_le_one (tsub_eq_zero_iff_le.1 hc)
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hγ hF
  simp only [hone, limsup_const] at hlim
  have hγc : (γ : Measure (ℝ × ℤ)) (labelBoundSet L κ)ᶜ = 0 := by
    rw [measure_compl hF.measurableSet (measure_ne_top _ _), measure_univ]
    exact tsub_eq_zero_iff_le.2 hlim
  have hG : Measurable fun t => (t, g t) := measurable_id.prodMk hg
  rw [heq, Measure.map_apply hG hF.measurableSet.compl] at hγc
  exact measure_eq_zero_iff_ae_notMem.1 hγc |>.mono fun t ht => by
    simpa [labelBoundSet] using ht

end Seq

#print axioms null_upperCut
#print axioms null_lowerCut
#print axioms graph_of_ordering
#print axioms limit_graph
#print axioms limit_label_bound

end QuantumNLS.LabelJointStructure
