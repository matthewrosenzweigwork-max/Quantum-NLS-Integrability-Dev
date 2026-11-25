import QuantumNLS.ExternalConfinement

/-!
# CC:F04:local-height (R-1842678C): a root in a band determines its real label

Source: `source/chapters/root_response/F04.tex`.
* Standing setup (lines 3-18): `L, κ > 0`; for the probability measure `μ`,
  `θ(x) = Lx/2 − κ ∫ dμ(y)/(x − y)` (`CC:F04:phase`) for `x` off the support of `μ`.
* `CC:F04:real-bethe` (lines 96-103): `q_{1,N} < ⋯ < q_{N,N}`, `ν_{1,N} ≤ ⋯ ≤ ν_{N,N}`,
  `L q_{i,N} − 2 Σ_{j≠i} arctan (c_N/(q_{i,N} − q_{j,N})) = 2π ν_{i,N}`, `c_N = κ/N`, and the empirical
  measures `μ_N` converge weakly to `μ`.
* The external force `CC:F04:external-force`, its slope-`L` extension, the cluster comparison
  (lines 104-121) and `CC:F04:external-limit` (lines 123-135).
* Lemma `CC:F04:local-height` (lines 137-145) and proof (lines 146-155): if `q_{i_N,N} → x` and
  `x ∉ supp μ`, then `ν_{i_N,N} → θ(x)/π`.

Conventions: the particle number runs through `n = N + 1 ≥ 1` (`N : ℕ`), arrays are `Fin (N+1)`,
`c = κ/(N+1)`. Weak convergence of the empirical measures is tested against every bounded
continuous function. The support is Mathlib's `Measure.support`.

Route (as printed): a small interval about `x` with `μ`-null neighbourhood; `K_N/N → 0`
(`cluster_density`); the external force `extForce` with its slope-`L` extension (`extForce_continuous`,
`extForce_slope`); the cluster equations (`cluster_equations`) and the accepted cluster comparison
R-52E511D4 (`ExternalConfinement.external_confinement`), so `|p_N − q_{i_N,N}| ≤ 4√(κK_N/(LN)) → 0`;
then `CC:F04:external-limit` at the points `p_N → x` gives `2πν_{i_N,N} = H_N(p_N) → 2θ(x)`.

Recorded deviations (none changes the statement):
* The cluster is the set of roots in the closed interval `[x − 2ε, x + 2ε]` (the printed open `U`
  with its `μ`-null boundary is replaced by a closed interval inside a `μ`-null neighbourhood), so
  every external root is at positive distance and the force is continuous up to the endpoints.
* `CC:F04:external-limit` is used only along the sequence `p_N → x` (not uniformly on compacts);
  the arctangent replacement uses `|arctan z − z| ≤ |z|³`, and the weak limit is taken against the
  bounded continuous kernel `g(y) = (x − y)/max((x − y)², ε²)`, equal to `1/(x − y)` off the null set.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
open Finset Filter MeasureTheory

namespace QuantumNLS.LocalHeight

/-! ## 1. An elementary arctangent bound -/

lemma arctan_sub_self_le (z : ℝ) : |Real.arctan z - z| ≤ |z| ^ 3 := by
  set f : ℝ → ℝ := fun t => Real.arctan t - t + t ^ 3
  have hd : ∀ t, HasDerivAt f (1 / (1 + t ^ 2) - 1 + 3 * t ^ 2) t := by
    intro t
    have := ((Real.hasDerivAt_arctan t).sub (hasDerivAt_id t)).add (hasDerivAt_pow 3 t)
    convert this using 1
    funext s; simp [f]
  have hmono : Monotone f := by
    refine monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt) fun t => ?_
    rw [(hd t).deriv]
    have h1 : 0 < 1 + t ^ 2 := by positivity
    rw [show 1 / (1 + t ^ 2) - 1 + 3 * t ^ 2 = (2 * t ^ 2 + 3 * t ^ 4) / (1 + t ^ 2) by
      field_simp; ring]
    positivity
  have hf0 : f 0 = 0 := by simp [f]
  rcases le_total 0 z with hz | hz
  · have h1 := hmono hz
    rw [hf0] at h1
    have h2 := Real.arctan_le_self hz
    rw [abs_of_nonneg hz, abs_le]
    simp only [f] at h1
    constructor <;> nlinarith
  · have h1 := hmono hz
    rw [hf0] at h1
    have h2 := Real.self_le_arctan hz
    rw [abs_of_nonpos hz, abs_le]
    simp only [f] at h1
    constructor <;> nlinarith

/-! ## 2. The external force of a cluster (fixed particle number) -/

section Force

variable {n : ℕ}

/-- The cluster: indices of the roots in `[a, b]`. -/
def cluster (a b : ℝ) (q : Fin n → ℝ) : Finset (Fin n) := univ.filter fun j => q j ∈ Set.Icc a b

/-- `CC:F04:external-force` on `[a, b]`: `G(z) = Lz − 2 Σ_{q_j ∉ [a,b]} arctan (c/(z − q_j))`. -/
def force (L c a b : ℝ) (q : Fin n → ℝ) (z : ℝ) : ℝ :=
  L * z - 2 * ∑ j ∈ univ.filter (fun j => q j ∉ Set.Icc a b), Real.arctan (c / (z - q j))

/-- Clamp to `[a, b]`. -/
def clamp (a b z : ℝ) : ℝ := max a (min z b)

lemma clamp_mem {a b : ℝ} (hab : a ≤ b) (z : ℝ) : clamp a b z ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

lemma clamp_of_mem {a b z : ℝ} (hz : z ∈ Set.Icc a b) : clamp a b z = z := by
  unfold clamp; rw [min_eq_left hz.2, max_eq_right hz.1]

lemma clamp_mono (a b : ℝ) : Monotone (clamp a b) := fun _ _ h =>
  max_le_max le_rfl (min_le_min h le_rfl)

lemma clamp_continuous (a b : ℝ) : Continuous (clamp a b) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The external force extended outside `[a, b]` linearly with slope `L`. -/
def extForce (L c a b : ℝ) (q : Fin n → ℝ) (z : ℝ) : ℝ :=
  force L c a b q (clamp a b z) + L * (z - clamp a b z)

lemma extForce_of_mem {L c a b : ℝ} {q : Fin n → ℝ} {z : ℝ} (hz : z ∈ Set.Icc a b) :
    extForce L c a b q z = force L c a b q z := by
  unfold extForce; rw [clamp_of_mem hz]; ring

lemma force_continuousOn (L c a b : ℝ) (q : Fin n → ℝ) :
    ContinuousOn (force L c a b q) (Set.Icc a b) := by
  unfold force
  refine (continuous_const.mul continuous_id).continuousOn.sub
    (continuousOn_const.mul (continuousOn_finsetSum _ fun j hj => ?_))
  have hj' := (Finset.mem_filter.mp hj).2
  refine Real.continuous_arctan.comp_continuousOn
    (continuousOn_const.div (continuous_id.sub continuous_const).continuousOn fun z hz => ?_)
  intro h0
  apply hj'
  have : z = q j := sub_eq_zero.mp h0
  rw [← this]; exact hz

lemma extForce_continuous {L c a b : ℝ} (hab : a ≤ b) (q : Fin n → ℝ) :
    Continuous (extForce L c a b q) := by
  unfold extForce
  exact ((force_continuousOn L c a b q).comp_continuous (clamp_continuous a b)
    (clamp_mem hab)).add (continuous_const.mul (continuous_id.sub (clamp_continuous a b)))

lemma div_anti_same_sign {c s s' : ℝ} (hc : 0 ≤ c) (hss : 0 < s * s') (h : s ≤ s') :
    c / s' ≤ c / s := by
  have hs : s ≠ 0 := by rintro rfl; simp at hss
  have hs' : s' ≠ 0 := by rintro rfl; simp at hss
  have e : c / s' - c / s = c * (s - s') / (s * s') := by field_simp
  have : c * (s - s') / (s * s') ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc (by linarith)) hss.le
  linarith

/-- The extended force has the lower slope `L` required by `CC:F04:external-confinement`. -/
lemma extForce_slope {L c a b : ℝ} (hc : 0 ≤ c) (hab : a ≤ b) (q : Fin n → ℝ) :
    ∀ z w, z ≤ w → L * (w - z) ≤ extForce L c a b q w - extForce L c a b q z := by
  intro z w hzw
  set u := clamp a b z
  set v := clamp a b w
  have huv : u ≤ v := clamp_mono a b hzw
  have hu := clamp_mem hab z
  have hv := clamp_mem hab w
  have hterm : ∀ j ∈ univ.filter (fun j => q j ∉ Set.Icc a b),
      Real.arctan (c / (v - q j)) ≤ Real.arctan (c / (u - q j)) := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    apply Real.arctan_strictMono.monotone
    apply div_anti_same_sign hc _ (by linarith)
    rcases lt_or_ge (q j) a with h | h
    · exact mul_pos (by linarith [hu.1]) (by linarith [hv.1])
    · have : b < q j := by
        by_contra h'; exact hj' ⟨h, not_lt.mp h'⟩
      exact mul_pos_of_neg_of_neg (by linarith [hu.2]) (by linarith [hv.2])
  have hsum := Finset.sum_le_sum hterm
  unfold extForce force
  nlinarith

/-- The equations of the cluster roots with the external force. -/
lemma cluster_equations {L c a b : ℝ} {q ν : Fin n → ℝ}
    (heq : ∀ i, L * q i - 2 * ∑ j ∈ univ.erase i, Real.arctan (c / (q i - q j)) =
      2 * Real.pi * ν i) {i : Fin n} (hi : i ∈ cluster a b q) :
    extForce L c a b q (q i) - 2 * ∑ j ∈ (cluster a b q).erase i,
      Real.arctan (c / (q i - q j)) = 2 * Real.pi * ν i := by
  have hiI : q i ∈ Set.Icc a b := (Finset.mem_filter.mp hi).2
  rw [extForce_of_mem hiI]
  have e1 : ∑ j ∈ univ.erase i, Real.arctan (c / (q i - q j)) =
      ∑ j ∈ (cluster a b q).erase i, Real.arctan (c / (q i - q j)) +
        ∑ j ∈ univ.filter (fun j => q j ∉ Set.Icc a b), Real.arctan (c / (q i - q j)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (univ.erase i) (fun j => q j ∈ Set.Icc a b)]
    congr 1
    · congr 1; ext j; simp [cluster, and_comm]
    · congr 1; ext j; simp only [mem_filter, mem_erase, mem_univ, and_true, true_and]
      exact ⟨fun h => h.2, fun h => ⟨fun hj => h (hj ▸ hiI), h⟩⟩
  have := heq i
  unfold force
  linarith

/-- **Cluster comparison** (from the accepted R-52E511D4): for a cluster root `q_i` and any `p` with
`H(p) = 2πν_i`, `|q_i − p| ≤ 4 √(c K/L)`, `K = #cluster`. -/
lemma cluster_bound {L c a b : ℝ} (hL : 0 < L) (hc : 0 < c) (hab : a ≤ b) {q ν : Fin n → ℝ}
    (hq : StrictMono q) (hν : Monotone ν)
    (heq : ∀ i, L * q i - 2 * ∑ j ∈ univ.erase i, Real.arctan (c / (q i - q j)) =
      2 * Real.pi * ν i) {i : Fin n} (hi : i ∈ cluster a b q) {p : ℝ}
    (hp : extForce L c a b q p = 2 * Real.pi * ν i) :
    |q i - p| ≤ 4 * Real.sqrt (c * (cluster a b q).card / L) := by
  set S := cluster a b q
  set e := S.orderIsoOfFin (k := S.card) rfl
  have hK : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
  have ht : StrictMono (fun k => q (e k)) := fun k1 k2 h =>
    hq (show (e k1 : Fin n) < e k2 from e.strictMono h)
  have hν' : Monotone (fun k => ν (e k)) := fun k1 k2 h =>
    hν (show (e k1 : Fin n) ≤ e k2 from e.monotone h)
  have heq' : ∀ k, extForce L c a b q (q (e k)) -
      2 * ∑ l ∈ univ.erase k, Real.arctan (c / (q (e k) - q (e l))) = 2 * Real.pi * ν (e k) := by
    intro k
    have := cluster_equations (L := L) (c := c) heq (e k).2
    rw [ExternalConfinement.sum_erase_transport e (fun j => Real.arctan (c / (q (e k) - q j)))] at this
    exact this
  obtain ⟨-, -, hb⟩ := ExternalConfinement.external_confinement hK hL hc
    (extForce_continuous hab q) (extForce_slope hc.le hab q) ht hν' heq'
  obtain ⟨k, hk⟩ : ∃ k, e k = ⟨i, hi⟩ := e.surjective _
  have := hb k p (by rw [hk]; exact hp)
  rw [hk] at this
  exact this

end Force

/-! ## 3. The bounded kernel and the external-limit estimate -/

/-- The bounded continuous kernel `g(y) = (x − y)/max((x − y)², ε²)`. -/
def gK (x ε y : ℝ) : ℝ := (x - y) / max ((x - y) ^ 2) (ε ^ 2)

lemma gK_eq {x ε y : ℝ} (hε : 0 < ε) (h : ε ≤ |x - y|) : gK x ε y = 1 / (x - y) := by
  unfold gK
  have h2 : ε ^ 2 ≤ (x - y) ^ 2 := by
    rw [← sq_abs (x - y)]; exact pow_le_pow_left₀ hε.le h 2
  rw [max_eq_left h2]
  have hne : x - y ≠ 0 := by
    intro h0; rw [h0, abs_zero] at h; linarith
  field_simp

lemma gK_abs_le {x ε : ℝ} (hε : 0 < ε) (y : ℝ) : |gK x ε y| ≤ 1 / ε := by
  unfold gK
  have hm : 0 < max ((x - y) ^ 2) (ε ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  rw [abs_div, abs_of_pos hm, div_le_div_iff₀ hm hε, one_mul]
  rcases le_total |x - y| ε with h | h
  · have : |x - y| * ε ≤ ε ^ 2 := by nlinarith [abs_nonneg (x - y)]
    exact this.trans (le_max_right _ _)
  · have : |x - y| * ε ≤ (x - y) ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg (x - y)]
    exact this.trans (le_max_left _ _)

lemma gK_continuous {x ε : ℝ} (hε : 0 < ε) : Continuous (gK x ε) := by
  unfold gK
  refine (continuous_const.sub continuous_id).div
    (((continuous_const.sub continuous_id).pow 2).max continuous_const) fun y => ?_
  exact (lt_of_lt_of_le (by positivity) (le_max_right _ _)).ne'

/-- `g` as a bounded continuous function. -/
def gBCF (x ε : ℝ) (hε : 0 < ε) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (gK x ε) (gK_continuous hε) (1 / ε)
    (fun y => by rw [Real.norm_eq_abs]; exact gK_abs_le hε y)

lemma inv_sub_inv_le {x p y ε : ℝ} (hε : 0 < ε) (h1 : ε ≤ |p - y|) (h2 : ε ≤ |x - y|) :
    |1 / (p - y) - 1 / (x - y)| ≤ |x - p| / ε ^ 2 := by
  have hp : p - y ≠ 0 := by intro h0; rw [h0, abs_zero] at h1; linarith
  have hx : x - y ≠ 0 := by intro h0; rw [h0, abs_zero] at h2; linarith
  have e : 1 / (p - y) - 1 / (x - y) = (x - p) / ((p - y) * (x - y)) := by field_simp; ring
  rw [e, abs_div, abs_mul]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  nlinarith [abs_nonneg (p - y), abs_nonneg (x - y)]

lemma abs3 (A B C : ℝ) : |A + B - C| ≤ |A| + |B| + |C| := by
  have h1 := abs_add_le (A + B) (-C)
  have h2 := abs_add_le A B
  rw [abs_neg] at h1
  rw [sub_eq_add_neg]
  linarith

/-- **Deterministic form of `CC:F04:external-limit`** at a point `p` with `|p − x| ≤ ε`, for the
cluster interval `[x − 2ε, x + 2ε]`. -/
lemma force_approx {n : ℕ} {L c x ε p : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) (q : Fin n → ℝ)
    (hp : |p - x| ≤ ε) :
    |force L c (x - 2 * ε) (x + 2 * ε) q p - (L * p - 2 * c * ∑ j, gK x ε (q j))| ≤
      2 * (n * (c / ε) ^ 3 + c * (n * (|x - p| / ε ^ 2)) +
        c * ((cluster (x - 2 * ε) (x + 2 * ε) q).card * (1 / ε))) := by
  set a := x - 2 * ε
  set b := x + 2 * ε
  set S := cluster a b q
  set T := univ.filter (fun j => q j ∉ Set.Icc a b)
  have hsplit : ∑ j, gK x ε (q j) = ∑ j ∈ S, gK x ε (q j) + ∑ j ∈ T, gK x ε (q j) :=
    (Finset.sum_filter_add_sum_filter_not univ (fun j => q j ∈ Set.Icc a b) _).symm
  have hT : ∀ j ∈ T, 2 * ε < |q j - x| := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    by_contra h
    push Not at h
    exact hj' ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
  have hTp : ∀ j ∈ T, ε ≤ |p - q j| := by
    intro j hj
    have := hT j hj
    have h3 : |q j - x| ≤ |p - q j| + |p - x| := by
      calc |q j - x| = |-(p - q j) + (p - x)| := by ring_nf
        _ ≤ |-(p - q j)| + |p - x| := abs_add_le _ _
        _ = |p - q j| + |p - x| := by rw [abs_neg]
    linarith
  have hTx : ∀ j ∈ T, ε ≤ |x - q j| := by
    intro j hj; have := hT j hj; rw [abs_sub_comm]; linarith
  -- decomposition
  have hdec : force L c a b q p - (L * p - 2 * c * ∑ j, gK x ε (q j)) =
      -2 * (∑ j ∈ T, (Real.arctan (c / (p - q j)) - c / (p - q j)) +
        ∑ j ∈ T, (c / (p - q j) - c * gK x ε (q j)) - c * ∑ j ∈ S, gK x ε (q j)) := by
    unfold force
    rw [hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hdec, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hcardT : (T.card : ℝ) ≤ n := by
    have := Finset.card_le_univ T; simp only [Fintype.card_fin] at this; exact_mod_cast this
  have b1 : |∑ j ∈ T, (Real.arctan (c / (p - q j)) - c / (p - q j))| ≤ n * (c / ε) ^ 3 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ((c / ε) ^ 3) fun j hj => ?_).trans ?_
    · refine (arctan_sub_self_le _).trans (pow_le_pow_left₀ (abs_nonneg _) ?_ 3)
      rw [abs_div, abs_of_nonneg hc]
      exact div_le_div_of_nonneg_left hc hε (hTp j hj)
    · rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hcardT (by positivity)
  have b2 : |∑ j ∈ T, (c / (p - q j) - c * gK x ε (q j))| ≤ c * (n * (|x - p| / ε ^ 2)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (c * (|x - p| / ε ^ 2)) fun j hj => ?_).trans ?_
    · rw [gK_eq hε (hTx j hj), show c / (p - q j) - c * (1 / (x - q j)) =
        c * (1 / (p - q j) - 1 / (x - q j)) by ring, abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (inv_sub_inv_le hε (hTp j hj) (hTx j hj)) hc
    · rw [nsmul_eq_mul]
      have : 0 ≤ c * (|x - p| / ε ^ 2) := by positivity
      nlinarith
  have b3 : |c * ∑ j ∈ S, gK x ε (q j)| ≤ c * (S.card * (1 / ε)) := by
    rw [abs_mul, abs_of_nonneg hc]
    apply mul_le_mul_of_nonneg_left _ hc
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (1 / ε) fun j _ => gK_abs_le hε _).trans ?_
    rw [nsmul_eq_mul]
  have h3 := abs3 (∑ j ∈ T, (Real.arctan (c / (p - q j)) - c / (p - q j)))
    (∑ j ∈ T, (c / (p - q j) - c * gK x ε (q j))) (c * ∑ j ∈ S, gK x ε (q j))
  linarith

/-! ## 4. The lemma -/

/-- `CC:F04:real-bethe` at particle number `N + 1` (`c = κ/(N+1)`): strictly ordered roots,
nondecreasing real labels and the real-label Bose equations. -/
structure RealBethe (L κ : ℝ) (N : ℕ) (q ν : Fin (N + 1) → ℝ) : Prop where
  sorted : StrictMono q
  labels : Monotone ν
  eqn : ∀ i, L * q i - 2 * ∑ j ∈ univ.erase i, Real.arctan (κ / ((N : ℝ) + 1) / (q i - q j)) =
    2 * Real.pi * ν i

/-- The empirical measures `μ_N = N^{-1} Σ_i δ_{q_{i,N}}` converge weakly to `μ`. -/
def EmpiricalWeakConv (q : (N : ℕ) → Fin (N + 1) → ℝ) (μ : Measure ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * ∑ j, f (q N j)) atTop
    (𝓝 (∫ y, f y ∂μ))

/-- `CC:F04:phase`: `θ(x) = Lx/2 − κ ∫ dμ(y)/(x − y)`. -/
def theta (L κ : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ := L * x / 2 - κ * ∫ y, 1 / (x - y) ∂μ

/-- **CC:F04:local-height** (R-1842678C): under `CC:F04:real-bethe` with weakly convergent
empirical measures, if `q_{i_N,N} → x` and `x ∉ supp μ`, then `ν_{i_N,N} → θ(x)/π`. -/
theorem local_height {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {q ν : (N : ℕ) → Fin (N + 1) → ℝ}
    (hB : ∀ N, RealBethe L κ N (q N) (ν N)) (hw : EmpiricalWeakConv q μ)
    (i : (N : ℕ) → Fin (N + 1)) {x : ℝ} (hx : Tendsto (fun N => q N (i N)) atTop (𝓝 x))
    (hsupp : x ∉ μ.support) :
    Tendsto (fun N => ν N (i N)) atTop (𝓝 (theta L κ μ x / Real.pi)) := by
  -- (A) a `μ`-null neighbourhood of `x`
  obtain ⟨U, hU, hU0⟩ := Measure.notMem_support_iff_exists.mp hsupp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = r / 8 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hnull : μ (Set.Icc (x - 4 * ε) (x + 4 * ε)) = 0 := by
    refine measure_mono_null (fun y hy => hball ?_) hU0
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hae : ∀ᵐ y ∂μ, 4 * ε < |y - x| := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
    by_contra h
    push Not at h
    exact hy ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
  have hab : x - 2 * ε ≤ x + 2 * ε := by linarith
  -- (B) `K_N / N → 0`
  set f1 : ℝ → ℝ := fun y => max 0 (min 1 (3 - |y - x| / ε)) with hf1
  have hf1c : Continuous f1 :=
    continuous_const.max (continuous_const.min (continuous_const.sub
      ((continuous_id.sub continuous_const).abs.div_const ε)))
  have hf1b : ∀ y, ‖f1 y‖ ≤ 1 := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (min_le_left _ _)
  have hf1int : ∫ y, (BoundedContinuousFunction.ofNormedAddCommGroup f1 hf1c 1 hf1b) y ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with y hy
    simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup, hf1, Pi.zero_apply]
    have : 3 - |y - x| / ε < 0 := by
      rw [sub_neg, lt_div_iff₀ hε]; linarith
    rw [min_eq_right (by linarith), max_eq_left this.le]
  have hK : Tendsto (fun N : ℕ =>
      ((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have h := hw (BoundedContinuousFunction.ofNormedAddCommGroup f1 hf1c 1 hf1b)
    rw [hf1int] at h
    refine squeeze_zero (fun N => by positivity) (fun N => ?_) h
    simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
    rw [div_eq_mul_inv, mul_comm, one_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : ((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) =
        ∑ j ∈ cluster (x - 2 * ε) (x + 2 * ε) (q N), f1 (q N j) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := (Finset.mem_filter.mp hj).2
      have : |q N j - x| ≤ 2 * ε := abs_le.mpr ⟨by linarith [hj'.1], by linarith [hj'.2]⟩
      have h3 : 1 ≤ 3 - |q N j - x| / ε := by
        rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hε]; linarith
      simp only [hf1]
      rw [min_eq_left h3, max_eq_right zero_le_one]
    rw [h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => le_max_left _ _)
  -- (C) the kernel
  have hgint : ∫ y, (gBCF x ε hε) y ∂μ = ∫ y, 1 / (x - y) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    show gK x ε y = 1 / (x - y)
    exact gK_eq hε (by rw [abs_sub_comm]; linarith)
  have hA : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j)) atTop
      (𝓝 (∫ y, 1 / (x - y) ∂μ)) := by
    rw [← hgint]; exact hw (gBCF x ε hε)
  -- (D) the external forces and the points `p_N`
  have hcN : ∀ N : ℕ, 0 < κ / ((N : ℝ) + 1) := fun N => by positivity
  have hsurj : ∀ N : ℕ, Function.Surjective
      (extForce L (κ / ((N : ℝ) + 1)) (x - 2 * ε) (x + 2 * ε) (q N)) := fun N =>
    ExternalConfinement.H_surjective hL (extForce_continuous hab _)
      (extForce_slope (hcN N).le hab _)
  set p : ℕ → ℝ := fun N => Function.surjInv (hsurj N) (2 * Real.pi * ν N (i N)) with hpdef
  have hp : ∀ N : ℕ, extForce L (κ / ((N : ℝ) + 1)) (x - 2 * ε) (x + 2 * ε) (q N) (p N) =
      2 * Real.pi * ν N (i N) := fun N => Function.surjInv_eq (hsurj N) _
  have hqev : ∀ᶠ N in atTop, |q N (i N) - x| < ε := by
    have := (Metric.tendsto_nhds.mp hx) ε hε
    simpa [Real.dist_eq] using this
  have hpq : Tendsto (fun N => p N - q N (i N)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun N : ℕ => 4 * Real.sqrt (κ / L *
        (((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1)))) atTop (𝓝 0) := by
      have h0 := hK.const_mul (κ / L)
      rw [mul_zero] at h0
      have := ((Real.continuous_sqrt.tendsto 0).comp h0).const_mul 4
      simpa using this
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hqev] with N hN
    have hi : i N ∈ cluster (x - 2 * ε) (x + 2 * ε) (q N) :=
      Finset.mem_filter.mpr ⟨mem_univ _, by
        constructor <;> linarith [(abs_lt.mp hN).1, (abs_lt.mp hN).2]⟩
    have := cluster_bound hL (hcN N) hab (hB N).sorted (hB N).labels (hB N).eqn hi (hp N)
    rw [Real.norm_eq_abs, abs_sub_comm]
    convert this using 3
    field_simp
  have hpx : Tendsto p atTop (𝓝 x) := by
    have := hpq.add hx
    simpa using this
  -- (E) `CC:F04:external-limit` along `p_N`
  have hpev : ∀ᶠ N in atTop, |p N - x| ≤ ε := by
    have := (Metric.tendsto_nhds.mp hpx) ε hε
    filter_upwards [this] with N hN
    rw [Real.dist_eq] at hN; exact hN.le
  have hmain : Tendsto (fun N : ℕ => L * p N - 2 * κ * ((1 / ((N : ℝ) + 1)) *
      ∑ j, gK x ε (q N j))) atTop (𝓝 (2 * theta L κ μ x)) := by
    have := (hpx.const_mul L).sub (hA.const_mul (2 * κ))
    unfold theta
    convert this using 2
    ring
  have herr : Tendsto (fun N : ℕ => 2 * (κ ^ 3 / ε ^ 3 * (1 / ((N : ℝ) + 1)) ^ 2 +
      κ * (|x - p N| / ε ^ 2) + κ / ε *
        (((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
      simpa using this
    have h2 : Tendsto (fun N : ℕ => |x - p N|) atTop (𝓝 0) := by
      have h2' : Tendsto (fun N => x - p N) atTop (𝓝 0) := by
        have := hpx.const_sub x
        simpa using this
      have := (continuous_abs.tendsto 0).comp h2'
      rw [abs_zero] at this
      exact this
    have := (((h1.const_mul (κ ^ 3 / ε ^ 3)).add ((h2.div_const (ε ^ 2)).const_mul κ)).add
      (hK.const_mul (κ / ε))).const_mul 2
    simpa using this
  have hH : Tendsto (fun N : ℕ => extForce L (κ / ((N : ℝ) + 1)) (x - 2 * ε) (x + 2 * ε) (q N)
      (p N)) atTop (𝓝 (2 * theta L κ μ x)) := by
    have hdiff : Tendsto (fun N : ℕ => extForce L (κ / ((N : ℝ) + 1)) (x - 2 * ε) (x + 2 * ε) (q N)
        (p N) - (L * p N - 2 * κ * ((1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j)))) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ herr
      filter_upwards [hpev] with N hN
      have hmem : p N ∈ Set.Icc (x - 2 * ε) (x + 2 * ε) :=
        ⟨by linarith [(abs_le.mp hN).1], by linarith [(abs_le.mp hN).2]⟩
      rw [extForce_of_mem hmem, Real.norm_eq_abs]
      have := force_approx (n := N + 1) (L := L) (hcN N).le hε (q N) hN
      have e1 : 2 * (κ / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j) =
          2 * κ * ((1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j)) := by
        field_simp
      have e2 : 2 * ((((N + 1 : ℕ) : ℝ)) * (κ / ((N : ℝ) + 1) / ε) ^ 3 +
          κ / ((N : ℝ) + 1) * (((N + 1 : ℕ) : ℝ) * (|x - p N| / ε ^ 2)) +
          κ / ((N : ℝ) + 1) * ((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card * (1 / ε))) =
          2 * (κ ^ 3 / ε ^ 3 * (1 / ((N : ℝ) + 1)) ^ 2 + κ * (|x - p N| / ε ^ 2) + κ / ε *
            (((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1))) := by
        push_cast
        field_simp
      rw [e1, e2] at this
      exact this
    have := hdiff.add hmain
    simpa using this
  -- (F) conclusion
  have := hH.div_const (2 * Real.pi)
  convert this using 1
  · funext N
    rw [hp N]
    field_simp
  · field_simp

#print axioms arctan_sub_self_le
#print axioms extForce_continuous
#print axioms extForce_slope
#print axioms cluster_equations
#print axioms cluster_bound
#print axioms gK_eq
#print axioms gK_abs_le
#print axioms gK_continuous
#print axioms inv_sub_inv_le
#print axioms abs3
#print axioms force_approx
#print axioms local_height

end QuantumNLS.LocalHeight
