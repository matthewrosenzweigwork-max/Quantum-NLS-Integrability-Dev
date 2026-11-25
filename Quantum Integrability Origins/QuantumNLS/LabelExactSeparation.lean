import QuantumNLS.LabelSeparationCore
import QuantumNLS.LabelWeakJointLimit

/-!
# PROP-003 `thm:B3-exact-separation` (label_periods.tex:117-224)

Source statement. Suppose a sequence of on-shell configurations satisfies `N⁻¹Σ_j δ_{q_j} ⇀ μ`. Let
`x` be a real point outside `supp μ` for which `2πa < F(x) < 2π(a+1)` for an integer `a`. Then there
are `δ > 0` and `N₀` such that, for `N ≥ N₀`, every root satisfies `n_j ≤ a ⇒ q_j < x − δ` and
`n_j ≥ a+1 ⇒ q_j > x + δ`. Consequently there are no roots in `[x−δ, x+δ]`, and `q_j < x ⇔ n_j ≤ a`.
The conclusion is uniform over any family of on-shell configurations whose empirical measures
converge weakly to `μ` uniformly (for any fixed metric for weak convergence).

Realization. `μ` and `F` are DEF-043's (`IndexedScalarMeasureCuts` `641aaaf7…`, read-only):
`F = exteriorForce L κ S.μ`, and `x` is a regular cut, `x ∈ S.cuts` (`⊆ (supp μ)ᶜ`), where the
DEF-043 separation hypothesis applies — the source's proof uses exactly that hypothesis through
`lem:B3-weak-joint-limit` ("the limiting joint measure assigns zero mass to this set").
PROP-002 is used through WJ1 `LabelWeakJointLimit` (`6900f39a…`, own, frozen, under review).

* `clip`, `exteriorForce_eq_clip`: away from `supp μ`, `F(y) = Ly − 2κ ∫ dμ(t)/(y−t)` with a bounded
  continuous extension of `t ↦ 1/(y − t)`;
* `exists_good_delta`: the printed choice of `δ` ([x−3δ, x+3δ] in the gap, here even
  `|x − t| ≥ 4δ` on `supp μ`, and `2πa < F(x−2δ)`, `F(x+2δ) < 2π(a+1)`);
* `clusterL_frac_tendsto`, `clusterR_frac_tendsto`: `k_N/N → 0` (joint limit, closed-set
  portmanteau, DEF-043 separation, `μ([x−3δ, x+3δ]) = 0`);
* `exterior_avg_tendsto`: removing the cluster does not change the limit of the exterior average;
* **`exact_separation_seq`**: for every sequence (`N_k → ∞`) eventually eq:B3-exact-cutoff, with
  `δ` depending only on `(μ, x, a)` (`exact_separation_of_good`);
* **`exact_separation_uniform`**: there are a weak neighbourhood `U` of `μ` and `N₀` such that every
  on-shell configuration with `N ≥ N₀` and `L_N ∈ U` satisfies eq:B3-exact-cutoff (the uniform
  statement; for any metric compatible with weak convergence, a ball is such a neighbourhood);
* `no_roots_near`, `lt_iff_label_le`: the two printed consequences.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.LabelExactSeparation

open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelWeakJointLimit
  QuantumNLS.LabelSeparationCore QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
  QuantumNLS.EmpiricalRapidity

/-! ## 1. A bounded continuous extension of `1/u` -/

/-- `clip w u = u / max(u², w²)`; it equals `1/u` for `|u| ≥ w`. -/
def clip (w u : ℝ) : ℝ := u / max (u ^ 2) (w ^ 2)

lemma clip_eq {w u : ℝ} (hw : 0 < w) (hu : w ≤ |u|) : clip w u = 1 / u := by
  have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
  have : w ^ 2 ≤ u ^ 2 := by rw [← sq_abs u]; exact pow_le_pow_left₀ hw.le hu 2
  rw [clip, max_eq_left this]
  field_simp

lemma abs_clip_le {w : ℝ} (hw : 0 < w) (u : ℝ) : |clip w u| ≤ 1 / w := by
  have hm : 0 < max (u ^ 2) (w ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  rw [clip, abs_div, abs_of_pos hm, div_le_div_iff₀ hm hw, one_mul]
  rcases le_total w |u| with h | h
  · calc |u| * w ≤ |u| * |u| := by gcongr
      _ = u ^ 2 := by rw [← sq, sq_abs]
      _ ≤ _ := le_max_left _ _
  · calc |u| * w ≤ w * w := by gcongr
      _ = w ^ 2 := by ring
      _ ≤ _ := le_max_right _ _

lemma continuous_clip {w : ℝ} (hw : 0 < w) : Continuous (clip w) :=
  continuous_id.div ((continuous_pow 2).max continuous_const) fun u =>
    (lt_of_lt_of_le (by positivity) (le_max_right _ _)).ne'

lemma ae_mem_support (μ : Measure ℝ) : ∀ᵐ t ∂μ, t ∈ μ.support :=
  measure_eq_zero_iff_ae_notMem.1 Measure.measure_compl_support |>.mono fun _ h => not_not.1 h

/-- Away from the support, `F(y) = Ly − 2κ ∫ clip_w(y − t) dμ(t)` (= `Ly − 2κ∫ dμ(t)/(y−t)`). -/
lemma exteriorForce_eq_clip (L κ : ℝ) (μ : Measure ℝ) {y w : ℝ} (hw : 0 < w)
    (hs : ∀ t ∈ μ.support, w ≤ |y - t|) :
    exteriorForce L κ μ y = L * y - 2 * κ * ∫ t, clip w (y - t) ∂μ := by
  unfold exteriorForce cauchyTransform
  congr 3
  have : ∫ t, ((y : ℂ) - (t : ℂ))⁻¹ ∂μ = ∫ t, ((clip w (y - t) : ℝ) : ℂ) ∂μ := by
    refine integral_congr_ae ((ae_mem_support μ).mono fun t ht => ?_)
    show ((y : ℂ) - (t : ℂ))⁻¹ = ((clip w (y - t) : ℝ) : ℂ)
    rw [clip_eq hw (hs t ht), one_div]
    push_cast
    rfl
  rw [this, integral_complex_ofReal, Complex.ofReal_re]

/-! ## 2. The choice of `δ` -/

/-- The printed choice of `δ`. -/
theorem exists_good_delta {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) {x : ℝ} (hx : x ∈ S.cuts)
    {a : ℤ} (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x)
    (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1)) :
    ∃ δ > 0, (∀ t ∈ S.μ.support, 4 * δ ≤ |x - t|) ∧
      2 * Real.pi * a < exteriorForce L κ S.μ (x - 2 * δ) ∧
      exteriorForce L κ S.μ (x + 2 * δ) < 2 * Real.pi * (a + 1) := by
  have : IsProbabilityMeasure S.μ := S.isProb
  have hxs : x ∈ (S.μ.support)ᶜ := S.cuts_sub hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 Measure.isClosed_support.isOpen_compl x hxs
  have hrs : ∀ t ∈ S.μ.support, r ≤ |x - t| := by
    intro t ht
    by_contra h
    push Not at h
    exact hball (by rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]; exact h) ht
  set w := r / 2
  have hw : 0 < w := by positivity
  set G : ℝ → ℝ := fun z => L * z - 2 * κ * ∫ t, clip w (z - t) ∂S.μ
  have hGc : Continuous G := by
    refine (continuous_const.mul continuous_id).sub (continuous_const.mul ?_)
    exact continuous_of_dominated (bound := fun _ => 1 / w)
      (fun z => ((continuous_clip hw).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (fun z => ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact abs_clip_le hw _)
      (integrable_const _) (ae_of_all _ fun t => (continuous_clip hw).comp
        (continuous_id.sub continuous_const))
  have hFG : ∀ z, |z - x| ≤ w → exteriorForce L κ S.μ z = G z := by
    intro z hz
    exact exteriorForce_eq_clip L κ S.μ hw fun t ht => by
      have := hrs t ht
      have hwr : w = r / 2 := rfl
      have h3 : |x - t| ≤ |z - t| + |z - x| := by
        calc |x - t| = |(z - t) - (z - x)| := by ring_nf
          _ ≤ |z - t| + |z - x| := abs_sub _ _
      linarith
  have hGx : G x = exteriorForce L κ S.μ x := (hFG x (by simp; positivity)).symm
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousAt_iff.1 hGc.continuousAt
    (min (exteriorForce L κ S.μ x - 2 * Real.pi * a)
      (2 * Real.pi * (a + 1) - exteriorForce L κ S.μ x)) (lt_min (by linarith) (by linarith))
  refine ⟨min (r / 8) (ρ / 4), by positivity, ?_, ?_, ?_⟩
  · intro t ht
    have := hrs t ht
    have : min (r / 8) (ρ / 4) ≤ r / 8 := min_le_left _ _
    linarith
  · have hz : |x - 2 * min (r / 8) (ρ / 4) - x| ≤ w := by
      rw [show x - 2 * min (r / 8) (ρ / 4) - x = -(2 * min (r / 8) (ρ / 4)) by ring, abs_neg,
        abs_of_pos (by positivity)]
      have : min (r / 8) (ρ / 4) ≤ r / 8 := min_le_left _ _
      simp only [w]; linarith
    rw [hFG _ hz]
    have hd := hρ' (x := x - 2 * min (r / 8) (ρ / 4)) (by
      rw [Real.dist_eq, show x - 2 * min (r / 8) (ρ / 4) - x = -(2 * min (r / 8) (ρ / 4)) by ring,
        abs_neg, abs_of_pos (by positivity)]
      have : min (r / 8) (ρ / 4) ≤ ρ / 4 := min_le_right _ _
      linarith)
    rw [Real.dist_eq, hGx] at hd
    have := (abs_lt.1 hd).1
    have := min_le_left (exteriorForce L κ S.μ x - 2 * Real.pi * a)
      (2 * Real.pi * (a + 1) - exteriorForce L κ S.μ x)
    linarith
  · have hz : |x + 2 * min (r / 8) (ρ / 4) - x| ≤ w := by
      rw [show x + 2 * min (r / 8) (ρ / 4) - x = 2 * min (r / 8) (ρ / 4) by ring,
        abs_of_pos (by positivity)]
      have : min (r / 8) (ρ / 4) ≤ r / 8 := min_le_left _ _
      simp only [w]; linarith
    rw [hFG _ hz]
    have hd := hρ' (x := x + 2 * min (r / 8) (ρ / 4)) (by
      rw [Real.dist_eq, show x + 2 * min (r / 8) (ρ / 4) - x = 2 * min (r / 8) (ρ / 4) by ring,
        abs_of_pos (by positivity)]
      have : min (r / 8) (ρ / 4) ≤ ρ / 4 := min_le_right _ _
      linarith)
    rw [Real.dist_eq, hGx] at hd
    have := (abs_lt.1 hd).2
    have := min_le_right (exteriorForce L κ S.μ x - 2 * Real.pi * a)
      (2 * Real.pi * (a + 1) - exteriorForce L κ S.μ x)
    linarith

/-! ## 3. Sequence estimates -/

lemma card_div_le_emp {X : Type*} [MeasurableSpace X] {N : ℕ} (p : Fin N → X) {S : Set X}
    (hS : MeasurableSet S) (J : Finset (Fin N)) (hJ : ∀ j ∈ J, p j ∈ S) :
    (J.card : ℝ) / N ≤ (emp p S).toReal := by
  have h1 : (J.card : ℝ≥0∞) ≤ ∑ j, Measure.dirac (p j) S := by
    calc (J.card : ℝ≥0∞) = ∑ j ∈ J, Measure.dirac (p j) S := by
          rw [Finset.sum_congr rfl fun j hj => by
            rw [Measure.dirac_apply' _ hS, indicator_of_mem (hJ j hj)]]
          simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ j, Measure.dirac (p j) S :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ J)
  have he : emp p S = (N : ℝ≥0∞)⁻¹ * ∑ j, Measure.dirac (p j) S := by
    simp only [emp, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  have hfin : ∑ j, Measure.dirac (p j) S ≠ ⊤ := by
    refine ENNReal.sum_ne_top.2 fun j _ => ?_
    exact (measure_ne_top _ _)
  rw [he, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, div_eq_inv_mul]
  have h2 : (J.card : ℝ) ≤ (∑ j, Measure.dirac (p j) S).toReal := by
    have := ENNReal.toReal_mono hfin h1
    simpa using this
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

section Seq

variable {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, OnShellBethe L κ (N k)}
  {μ : ProbabilityMeasure ℝ}

/-- A cluster whose joint-measure envelope has vanishing limit mass has vanishing density. -/
lemma frac_tendsto_of_closed {C : Set (ℝ × ℤ)} (hC : IsClosed C) {γ : ProbabilityMeasure (ℝ × ℤ)}
    (hJ : Tendsto (fun k => jointP (B k) (hN k)) atTop (𝓝 γ)) (hγ : (γ : Measure (ℝ × ℤ)) C = 0)
    (J : ∀ k, Finset (Fin (N k))) (hJC : ∀ k, ∀ j ∈ J k, pts (B k) j ∈ C) :
    Tendsto (fun k => ((J k).card : ℝ) / N k) atTop (𝓝 0) := by
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hJ hC
  rw [hγ] at hlim
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev : ∀ᶠ k in atTop, (jointP (B k) (hN k) : Measure (ℝ × ℤ)) C < ENNReal.ofReal ε :=
    eventually_lt_of_limsup_lt (hlim.trans_lt (ENNReal.ofReal_pos.2 hε))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨K, fun k hk => ?_⟩
  have h1 := card_div_le_emp (pts (B k)) hC.measurableSet (J k) (hJC k)
  have h2 : (emp (pts (B k)) C).toReal < ε := by
    have := hK k hk
    have h3 : (emp (pts (B k)) C) < ENNReal.ofReal ε := this
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 h3 |>.trans_le
      (ENNReal.toReal_ofReal hε.le).le
  have h0 : 0 ≤ ((J k).card : ℝ) / N k := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

/-- Exterior averages: removing a cluster of vanishing density does not change the limit. -/
lemma exterior_avg_tendsto (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    {w : ℝ} (_hw : 0 < w) (h : ℝ → ℝ) (hhc : Continuous h) (hhb : ∀ t, |h t| ≤ 1 / w)
    (J : ∀ k, Finset (Fin (N k)))
    (hfrac : Tendsto (fun k => ((J k).card : ℝ) / N k) atTop (𝓝 0)) :
    Tendsto (fun k => (1 / (N k : ℝ)) * ∑ l ∈ Finset.univ.filter (· ∉ J k), h ((B k).q l))
      atTop (𝓝 (∫ t, h t ∂(μ : Measure ℝ))) := by
  set H : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨h, hhc⟩ (2 / w) (fun s t => by
      show |h s - h t| ≤ 2 / w
      have := hhb s; have := hhb t
      have e : (2 : ℝ) / w = 1 / w + 1 / w := by ring
      rw [e]
      exact (abs_sub _ _).trans (by linarith))
  have hall := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv) H
  have hall' : Tendsto (fun k => (1 / (N k : ℝ)) * ∑ l, h ((B k).q l)) atTop
      (𝓝 (∫ t, h t ∂(μ : Measure ℝ))) := by
    refine hall.congr fun k => ?_
    show ∫ t, h t ∂(emp (B k).q) = _
    rw [integral_emp, one_div]
  have hJs : Tendsto (fun k => (1 / (N k : ℝ)) * ∑ l ∈ J k, h ((B k).q l)) atTop (𝓝 0) := by
    have hb := hfrac.const_mul (1 / w)
    rw [mul_zero] at hb
    refine squeeze_zero_norm (fun k => ?_) hb
    have hNk : (0 : ℝ) < N k := Nat.cast_pos.2 (hN k)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N k : ℝ))]
    calc 1 / (N k : ℝ) * |∑ l ∈ J k, h ((B k).q l)|
        ≤ 1 / (N k : ℝ) * ∑ l ∈ J k, |h ((B k).q l)| := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ 1 / (N k : ℝ) * ∑ _l ∈ J k, 1 / w := by gcongr with l; exact hhb _
      _ = 1 / w * (((J k).card : ℝ) / N k) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hsplit : ∀ k, (1 / (N k : ℝ)) * ∑ l ∈ Finset.univ.filter (· ∉ J k), h ((B k).q l) =
      (1 / (N k : ℝ)) * ∑ l, h ((B k).q l) - (1 / (N k : ℝ)) * ∑ l ∈ J k, h ((B k).q l) := by
    intro k
    have := Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ J k) (fun l => h ((B k).q l))
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter] at this
    rw [← this]
    ring
  simp only [hsplit]
  simpa using hall'.sub hJs

/-- **Exact separation along a sequence, for a good `δ`.** -/
theorem exact_separation_of_good (S : IndexedScalarMeasureCuts L κ)
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hμ : (μ : Measure ℝ) = S.μ)
    (hNtop : Tendsto N atTop atTop) {x : ℝ} (hx : x ∈ S.cuts) {a : ℤ}
    (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x)
    (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1))
    {δ : ℝ} (hδ : 0 < δ) (hsupp : ∀ t ∈ S.μ.support, 4 * δ ≤ |x - t|)
    (hFl : 2 * Real.pi * a < exteriorForce L κ S.μ (x - 2 * δ))
    (hFr : exteriorForce L κ S.μ (x + 2 * δ) < 2 * Real.pi * (a + 1)) :
    ∀ᶠ k in atTop, ∀ j, ((B k).n j ≤ a → (B k).q j < x - δ) ∧
      (a + 1 ≤ (B k).n j → x + δ < (B k).q j) := by
  have : IsProbabilityMeasure S.μ := S.isProb
  have hL := S.hL
  have hκ := S.hκ
  obtain ⟨⟨ns, hnsm, hns⟩, hall⟩ := weak_joint_limit_DEF043 S hconv hμ hNtop
  have hJ := hall ns hns
  obtain ⟨sepL, sepR⟩ := S.separation x hx a h1 h2
  have hsuppae := ae_mem_support S.μ
  have hgapnull : S.μ (Icc (x - 3 * δ) (x + 3 * δ)) = 0 := by
    refine measure_mono_null (fun t ht => ?_) Measure.measure_compl_support
    have h' : |x - t| ≤ 3 * δ := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    intro hts
    have := hsupp t hts
    linarith
  -- closed envelopes of the two clusters
  set CL : Set (ℝ × ℤ) := {p | p.2 ≤ a ∧ x - 3 * δ ≤ p.1}
  set CR : Set (ℝ × ℤ) := {p | a + 1 ≤ p.2 ∧ p.1 ≤ x + 3 * δ}
  have hCL : IsClosed CL :=
    (isClosed_le continuous_snd continuous_const).inter (isClosed_le continuous_const continuous_fst)
  have hCR : IsClosed CR :=
    (isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_fst continuous_const)
  have hG : Measurable fun t => (t, ns t) := measurable_id.prodMk hnsm
  have hnsae : ∀ᵐ t ∂S.μ, (ns t : ℝ) = indexLabel L κ S.reG t := hns
  have hnullR : S.μ {t | x < t ∧ ns t ≤ a} = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ((sepR.and hnsae).mono fun t ht ht' => ?_)
    obtain ⟨hxt, hle⟩ := ht'
    have h3 := ht.1 hxt
    rw [← ht.2] at h3
    have : a + 1 ≤ ns t := by exact_mod_cast h3
    omega
  have hnullL : S.μ {t | t < x ∧ a + 1 ≤ ns t} = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ((sepL.and hnsae).mono fun t ht ht' => ?_)
    obtain ⟨hxt, hle⟩ := ht'
    have h3 := ht.1 hxt
    rw [← ht.2] at h3
    have : ns t ≤ a := by exact_mod_cast h3
    omega
  have hγL : (graphP μ ns : Measure (ℝ × ℤ)) CL = 0 := by
    rw [graphP_toMeasure, Measure.map_apply hG hCL.measurableSet, hμ]
    refine measure_mono_null (fun t ht => ?_) (measure_union_null hgapnull hnullR)
    simp only [mem_preimage, CL, Set.mem_ofPred_eq] at ht
    by_cases hxt : x < t
    · exact Or.inr ⟨hxt, ht.1⟩
    · exact Or.inl ⟨ht.2, by linarith [not_lt.1 hxt]⟩
  have hγR : (graphP μ ns : Measure (ℝ × ℤ)) CR = 0 := by
    rw [graphP_toMeasure, Measure.map_apply hG hCR.measurableSet, hμ]
    refine measure_mono_null (fun t ht => ?_) (measure_union_null hgapnull hnullL)
    simp only [mem_preimage, CR, Set.mem_ofPred_eq] at ht
    by_cases hxt : t < x
    · exact Or.inr ⟨hxt, ht.1⟩
    · exact Or.inl ⟨by linarith [not_lt.1 hxt], ht.2⟩
  have hfracL := frac_tendsto_of_closed hCL hJ hγL (fun k => clusterL (B k) a x δ)
    (fun k j hj => by
      simp only [clusterL, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact ⟨hj.1, hj.2.le⟩)
  have hfracR := frac_tendsto_of_closed hCR hJ hγR (fun k => clusterR (B k) a x δ)
    (fun k j hj => by
      simp only [clusterR, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact ⟨hj.1, hj.2.le⟩)
  -- exterior averages
  have hfarL : ∀ t ∈ S.μ.support, δ ≤ |x - 2 * δ - t| := fun t ht => by
    have := hsupp t ht
    have : |x - t| ≤ |x - 2 * δ - t| + 2 * δ := by
      calc |x - t| = |(x - 2 * δ - t) + 2 * δ| := by ring_nf
        _ ≤ |x - 2 * δ - t| + |2 * δ| := abs_add_le _ _
        _ = _ := by rw [abs_of_pos (show (0 : ℝ) < 2 * δ by positivity)]
    linarith
  have hfarR : ∀ t ∈ S.μ.support, δ ≤ |x + 2 * δ - t| := fun t ht => by
    have := hsupp t ht
    have : |x - t| ≤ |x + 2 * δ - t| + 2 * δ := by
      calc |x - t| = |(x + 2 * δ - t) - 2 * δ| := by ring_nf
        _ ≤ |x + 2 * δ - t| + |2 * δ| := abs_sub _ _
        _ = _ := by rw [abs_of_pos (show (0 : ℝ) < 2 * δ by positivity)]
    linarith
  have hFL := exteriorForce_eq_clip L κ S.μ hδ hfarL
  have hFR := exteriorForce_eq_clip L κ S.μ hδ hfarR
  have havgL := exterior_avg_tendsto hconv hδ (fun t => clip δ (x - 2 * δ - t))
    ((continuous_clip hδ).comp (continuous_const.sub continuous_id))
    (fun t => abs_clip_le hδ _) (fun k => clusterL (B k) a x δ) hfracL
  have havgR := exterior_avg_tendsto hconv hδ (fun t => clip δ (x + 2 * δ - t))
    ((continuous_clip hδ).comp (continuous_const.sub continuous_id))
    (fun t => abs_clip_le hδ _) (fun k => clusterR (B k) a x δ) hfracR
  rw [hμ] at havgL havgR
  have herr : Tendsto (fun k => 2 * κ ^ 3 / ((N k : ℝ) ^ 2 * δ ^ 3)) atTop (𝓝 0) := by
    have : Tendsto (fun k => ((N k : ℝ) ^ 2 * δ ^ 3)) atTop atTop :=
      Tendsto.atTop_mul_const (by positivity)
        ((tendsto_pow_atTop two_ne_zero).comp (tendsto_natCast_atTop_atTop.comp hNtop))
    exact this.const_div_atTop _
  have hevL : ∀ᶠ k in atTop, 2 * Real.pi * a < L * (x - 2 * δ) -
      2 * κ * ((1 / (N k : ℝ)) * ∑ l ∈ Finset.univ.filter (· ∉ clusterL (B k) a x δ),
        clip δ (x - 2 * δ - (B k).q l)) - 2 * κ ^ 3 / ((N k : ℝ) ^ 2 * δ ^ 3) := by
    have hlim := ((tendsto_const_nhds (x := L * (x - 2 * δ))).sub (havgL.const_mul (2 * κ))).sub herr
    rw [sub_zero, ← hFL] at hlim
    exact hlim.eventually (lt_mem_nhds hFl)
  have hevR : ∀ᶠ k in atTop, L * (x + 2 * δ) -
      2 * κ * ((1 / (N k : ℝ)) * ∑ l ∈ Finset.univ.filter (· ∉ clusterR (B k) a x δ),
        clip δ (x + 2 * δ - (B k).q l)) + 2 * κ ^ 3 / ((N k : ℝ) ^ 2 * δ ^ 3) <
      2 * Real.pi * (a + 1) := by
    have hlim := ((tendsto_const_nhds (x := L * (x + 2 * δ))).sub (havgR.const_mul (2 * κ))).add herr
    rw [add_zero, ← hFR] at hlim
    exact hlim.eventually (gt_mem_nhds hFr)
  have hsq : ∀ {J : ∀ k, Finset (Fin (N k))},
      Tendsto (fun k => ((J k).card : ℝ) / N k) atTop (𝓝 0) →
      ∀ᶠ k in atTop, 3 * Real.sqrt (κ / N k * (J k).card / L) < δ := by
    intro J hf
    have h1 : Tendsto (fun k => 3 * Real.sqrt (κ / L * (((J k).card : ℝ) / N k))) atTop (𝓝 0) := by
      have h0 := hf.const_mul (κ / L)
      rw [mul_zero] at h0
      have := ((Real.continuous_sqrt.tendsto 0).comp h0).const_mul 3
      rw [Real.sqrt_zero, mul_zero] at this
      exact this
    refine (h1.eventually (gt_mem_nhds hδ)).mono fun k hk => ?_
    have e : κ / N k * (J k).card / L = κ / L * (((J k).card : ℝ) / N k) := by ring
    rw [e]; exact hk
  filter_upwards [hevL, hevR, hsq hfracL, hsq hfracR] with k hkL hkR hk1 hk2
  intro j
  refine ⟨core_left hL hκ (hN k) (B k) a hδ _ (fun t ht => clip_eq hδ ht) hkL hk1 j,
    core_right hL hκ (hN k) (B k) a hδ _ (fun t ht => clip_eq hδ ht) hkR hk2 j⟩

/-- **PROP-003 along a sequence**: there is `δ > 0` (depending only on `μ, x, a`) such that
eventually eq:B3-exact-cutoff holds for every root. -/
theorem exact_separation_seq (S : IndexedScalarMeasureCuts L κ)
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hμ : (μ : Measure ℝ) = S.μ)
    (hNtop : Tendsto N atTop atTop) {x : ℝ} (hx : x ∈ S.cuts) {a : ℤ}
    (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x)
    (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1)) :
    ∃ δ > 0, ∀ᶠ k in atTop, ∀ j, ((B k).n j ≤ a → (B k).q j < x - δ) ∧
      (a + 1 ≤ (B k).n j → x + δ < (B k).q j) := by
  obtain ⟨δ, hδ, hs, hl, hr⟩ := exists_good_delta S hx h1 h2
  exact ⟨δ, hδ, exact_separation_of_good S hconv hμ hNtop hx h1 h2 hδ hs hl hr⟩

end Seq

/-- **PROP-003, uniform form**: there are `δ > 0`, a weak neighbourhood `U` of `μ` and `N₀` such
that every on-shell configuration with `N ≥ N₀` roots and root empirical measure in `U` satisfies
eq:B3-exact-cutoff. -/
theorem exact_separation_uniform {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {x : ℝ} (hx : x ∈ S.cuts) {a : ℤ}
    (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x)
    (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1)) :
    ∃ δ > 0, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
        ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j) := by
  obtain ⟨δ, hδ, hs, hl, hr⟩ := exists_good_delta S hx h1 h2
  refine ⟨δ, hδ, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu⟩ := (𝓝 μ).exists_antitone_basis
  have hpick : ∀ k : ℕ, ∃ N : ℕ, ∃ hN : 0 < N, k + 1 ≤ N ∧ ∃ B : OnShellBethe L κ N,
      rootP B hN ∈ u k ∧ ∃ j, ¬ ((B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) := by
    intro k
    obtain ⟨N, hN, hkN, B, hB, j, hj⟩ := hcon (u k) (hu.1.mem_of_mem trivial) (k + 1)
    exact ⟨N, hN, hkN, B, hB, j, fun h => by
      rcases h with ⟨hl', hr'⟩
      obtain ⟨h1', h2'⟩ := hj hl'
      exact not_lt.2 h2' (hr' h1')⟩
  choose Nk hNk hkN Bk hBk jk hjk using hpick
  have hconv : Tendsto (fun k => rootP (Bk k) (hNk k)) atTop (𝓝 μ) := hu.tendsto hBk
  have hNtop : Tendsto Nk atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_succ k).trans (hkN k)) tendsto_id
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (exact_separation_of_good S hconv hμ hNtop hx h1 h2 hδ hs hl hr)
  exact hjk K (hK K le_rfl (jk K))

/-- Consequence: no roots in `[x − δ, x + δ]`. -/
theorem no_roots_near {L κ : ℝ} {N : ℕ} (B : OnShellBethe L κ N) {a : ℤ} {x δ : ℝ}
    (h : ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) (j : Fin N) :
    B.q j ∉ Icc (x - δ) (x + δ) := by
  intro hm
  by_cases hn : B.n j ≤ a
  · linarith [(h j).1 hn, hm.1]
  · linarith [(h j).2 (by omega), hm.2]

/-- Consequence: `q_j < x ↔ n_j ≤ a`. -/
theorem lt_iff_label_le {L κ : ℝ} {N : ℕ} (B : OnShellBethe L κ N) {a : ℤ} {x δ : ℝ} (hδ : 0 < δ)
    (h : ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) (j : Fin N) :
    B.q j < x ↔ B.n j ≤ a := by
  constructor
  · intro hq
    by_contra hn
    have := (h j).2 (by omega)
    linarith
  · intro hn
    have := (h j).1 hn
    linarith

end QuantumNLS.LabelExactSeparation

#print axioms QuantumNLS.LabelExactSeparation.exteriorForce_eq_clip
#print axioms QuantumNLS.LabelExactSeparation.exists_good_delta
#print axioms QuantumNLS.LabelExactSeparation.exterior_avg_tendsto
#print axioms QuantumNLS.LabelExactSeparation.exact_separation_of_good
#print axioms QuantumNLS.LabelExactSeparation.exact_separation_seq
#print axioms QuantumNLS.LabelExactSeparation.exact_separation_uniform
#print axioms QuantumNLS.LabelExactSeparation.no_roots_near
#print axioms QuantumNLS.LabelExactSeparation.lt_iff_label_le
