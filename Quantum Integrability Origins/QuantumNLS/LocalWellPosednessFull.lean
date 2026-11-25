import QuantumNLS.LocalWellPosedness

/-!
# F04:lem-local (R-501CA032), remaining clauses

Builds on the frozen `LocalWellPosedness` (LW1, read-only). Source: `source/chapters/foundations/F04.tex`,
Lemma `F04:lem-local` (lines 130-147) and its proof (lines 149-…). Spaces: F04's `H^s` on its Fourier
side `h04 L s` (realized SobolevSpaces), as in LW1.

Proved here (closing the three clauses left open by LW1):
1. **`C¹_t H^{s−2}` and the equation** (`mild_C1`): for a mild solution on `I`, the `H^{s−2}`-valued
   `G(t) = −i(−∂_x²u) − 2iκF(u)` (`Gder`) is continuous on `I`, `u(T) − u(t₀) = ∫_{t₀}^T G` in `H^{s−2}`,
   `u` has derivative `G(t)` within every compact subinterval and at interior points, and
   `i G = −∂_x²u + 2κ|u|²u` in `H^{s−2}` (`lapOp` is `−∂_x²: H^s → H^{s−2}`). Route as printed:
   coefficient-wise differentiation of the Duhamel formula (`scalar_integral_eq`), equality of Fourier
   coefficients (`coefL`, `integral_val`).
2. **Maximal interval and blow-up alternative**: mild solutions based at any time (`IsMildFrom`),
   time translation (`IsMild.shift`, `IsMildFrom.shift`), rebasing (`IsMildFrom.rebase`, the reverse
   rebasing identity), uniqueness/stability at any base, concatenation (`concat`), extension by the
   existence time of the endpoint value (`extend_right`, `extend_left`), the union `Imax` of all
   solution intervals with the glued solution `umax` (`umax_mild`), `maximal_interval` (a unique open
   interval containing `0` that carries a mild solution and contains every interval that carries one),
   and `blowup_right` / `blowup_left` (at a finite endpoint the `H^s` norm is unbounded as the endpoint
   is approached), via the uniform existence time `tauM` (`tauM_le_tau`).
3. **Distributional solutions are mild**: the du Bois-Reymond lemma (`dbr`, via the primitive and
   `const_of_zero_deriv`: zero distributional derivative ⇒ constant, proved with a normalized bump,
   the primitive test function and Mathlib's fundamental lemma); `IsDistSol` (equation tested against
   `φ(t) \overline{e_n(x)}`, `φ ∈ C_c^∞(I)`, coefficient-wise, which every space-time distributional
   solution satisfies); `dist_mildFrom` (Duhamel based at every `t₀ ∈ I`), `dist_isMild`; and the printed
   `F04:eq-stability` (`dist_stability`, constant `exp(4κ C_{1,L} K²|t − t₀|)`) and uniqueness
   (`dist_unique`) among `C_tH¹` distributional solutions.

Deviations: the derivative in `H^{s−2}` is stated as `HasDerivWithinAt` on every compact subinterval of
`I` plus `HasDerivAt` at interior points (Mathlib's FTC filters do not cover arbitrary intervals);
distributional solutions are formulated coefficient-wise with real test functions (complex ones are
real combinations); the maximal interval is the union of all solution intervals.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators Topology ContDiff
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness

namespace QuantumNLS.LocalWellPosednessFull

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. Mild solutions based at an arbitrary time; translation and rebasing -/

/-- Mild solution on `K` with data `a` at the base time `t₁ ∈ K`:
`u(t) = S(t − t₁)a − 2iκ ∫_{t₁}^t S(t − r) F(u(r)) dr`. -/
structure IsMildFrom {s : ℝ} (hs : 1 ≤ s) (κ : ℝ) (t1 : ℝ) (K : Set ℝ) (a : h04 L s)
    (u : ℝ → h04 L s) : Prop where
  mem : t1 ∈ K
  ordConnected : K.OrdConnected
  cont : ContinuousOn u K
  eq : ∀ t ∈ K, u t = Sgrp s (t - t1) a -
    (2 * Complex.I * κ) • ∫ r in t1..t, Sgrp s (t - r) (Fh hs (u r))

variable {s : ℝ} {hs : 1 ≤ s} {κ : ℝ}

lemma IsMild.toFrom {I : Set ℝ} {u0 : h04 L s} {u : ℝ → h04 L s} (h : IsMild hs κ I u0 u) :
    IsMildFrom hs κ 0 I u0 u :=
  ⟨h.zero_mem, h.ordConnected, h.cont, fun t ht => by
    rw [h.duhamel_eq t ht, duhamel, sub_zero]⟩

lemma IsMildFrom.toMild {I : Set ℝ} {u0 : h04 L s} {u : ℝ → h04 L s}
    (h : IsMildFrom hs κ 0 I u0 u) : IsMild hs κ I u0 u :=
  ⟨h.mem, h.ordConnected, h.cont, fun t ht => by
    rw [h.eq t ht, duhamel, sub_zero]⟩

lemma IsMildFrom.at_base {t1 : ℝ} {K : Set ℝ} {a : h04 L s} {u : ℝ → h04 L s}
    (h : IsMildFrom hs κ t1 K a u) : u t1 = a := by
  rw [h.eq t1 h.mem]; simp [Sgrp_zero]

lemma ordConnected_shift {K : Set ℝ} (hK : K.OrdConnected) (d : ℝ) :
    ({t | t + d ∈ K} : Set ℝ).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  exact hK.out hx hy ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-- Shift a mild solution based at `t₁` to one based at `0`. -/
lemma IsMildFrom.shift {t1 : ℝ} {K : Set ℝ} {a : h04 L s} {u : ℝ → h04 L s}
    (h : IsMildFrom hs κ t1 K a u) :
    IsMild hs κ {t | t + t1 ∈ K} a (fun t => u (t + t1)) := by
  refine ⟨by simpa using h.mem, ordConnected_shift h.ordConnected t1,
    h.cont.comp (continuous_id.add continuous_const).continuousOn (fun t ht => ht), fun t ht => ?_⟩
  rw [h.eq (t + t1) ht, duhamel, add_sub_cancel_right]
  congr 2
  have := intervalIntegral.integral_comp_add_right
    (fun r => Sgrp s (t + t1 - r) (Fh hs (u r))) t1 (a := 0) (b := t)
  simp only [zero_add] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun r _ => ?_
  rw [show t + t1 - (r + t1) = t - r by ring]

/-- Translate a mild solution based at `0` to one based at `t₁`. -/
lemma IsMild.shift {J : Set ℝ} {a : h04 L s} {w : ℝ → h04 L s} (h : IsMild hs κ J a w)
    (t1 : ℝ) : IsMildFrom hs κ t1 {t | t + -t1 ∈ J} a (fun t => w (t + -t1)) := by
  refine ⟨by simpa using h.zero_mem, ordConnected_shift h.ordConnected (-t1),
    h.cont.comp (continuous_id.add continuous_const).continuousOn (fun t ht => ht), fun t ht => ?_⟩
  rw [h.duhamel_eq _ ht, duhamel, show t - t1 = t + -t1 by ring]
  congr 2
  have := intervalIntegral.integral_comp_add_right
    (fun r => Sgrp s (t + -t1 - r) (Fh hs (w r))) (-t1) (a := t1) (b := t)
  simp only [add_neg_cancel] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun r _ => ?_
  rw [show t + -t1 - (r + -t1) = t - r by ring]

lemma shift_shift_set (K : Set ℝ) (t1 : ℝ) : {t | t + -t1 ∈ {t | t + t1 ∈ K}} = K := by
  ext t; simp

/-- **Rebasing**: a mild solution based at `t₁` is a mild solution based at any `t₂ ∈ K`, with
data `u(t₂)`. -/
lemma IsMildFrom.rebase {t1 t2 : ℝ} {K : Set ℝ} {a : h04 L s} {u : ℝ → h04 L s}
    (h : IsMildFrom hs κ t1 K a u) (ht2 : t2 ∈ K) : IsMildFrom hs κ t2 K (u t2) u := by
  have hv := h.shift
  refine ⟨ht2, h.ordConnected, h.cont, fun t ht => ?_⟩
  have h1 := duhamel_rebase hs hv (t0 := t2 - t1) (t := t - t1)
    (by simpa using ht2) (by simpa using ht)
  simp only [sub_add_cancel] at h1
  rw [h1, show t - t1 - (t2 - t1) = t - t2 by ring]
  congr 2
  have := intervalIntegral.integral_comp_add_right
    (fun r => Sgrp s (t - t1 - r) (Fh hs (u (r + t1)))) (-t1) (a := t2) (b := t)
  rw [show t2 + -t1 = t2 - t1 by ring, show t + -t1 = t - t1 by ring] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun r _ => ?_
  rw [show t - t1 - (r + -t1) = t - r by ring, show r + -t1 + t1 = r by ring]

/-- **Uniqueness** for mild solutions with the same base and data. -/
lemma IsMildFrom.unique (hκ : 0 ≤ κ) {t1 : ℝ} {K : Set ℝ} {a : h04 L s} {u v : ℝ → h04 L s}
    (hu : IsMildFrom hs κ t1 K a u) (hv : IsMildFrom hs κ t1 K a v) : ∀ t ∈ K, u t = v t := by
  intro t ht
  have := mild_unique hs hκ hu.shift hv.shift (t - t1) (by simpa using ht)
  simpa using this

/-- **Stability** for mild solutions based at the same time (from LW1's `stability`). -/
lemma IsMildFrom.stability (hκ : 0 ≤ κ) {t1 : ℝ} {K : Set ℝ} {a b : h04 L s}
    {u v : ℝ → h04 L s} (hu : IsMildFrom hs κ t1 K a u) (hv : IsMildFrom hs κ t1 K b v) {M : ℝ}
    (hM : ∀ r ∈ K, ‖u r‖ ≤ M ∧ ‖v r‖ ≤ M) {t0 t : ℝ} (ht0 : t0 ∈ K) (ht : t ∈ K) :
    ‖u t - v t‖ ≤ Real.exp (4 * κ * Cs L s * M ^ 2 * |t - t0|) * ‖u t0 - v t0‖ := by
  have := LocalWellPosedness.stability hs hκ hu.shift hv.shift (K := M)
    (fun r hr => hM (r + t1) hr) (t0 := t0 - t1) (t := t - t1) (by simpa using ht0)
    (by simpa using ht)
  simpa [show t - t1 - (t0 - t1) = t - t0 by ring] using this

#print axioms IsMildFrom.shift
#print axioms IsMild.shift
#print axioms IsMildFrom.rebase
#print axioms IsMildFrom.unique
#print axioms IsMildFrom.stability

/-! ## 2. Continuation: concatenation, extension, the maximal interval, blow-up -/

lemma IsMildFrom.mono {t1 : ℝ} {K K' : Set ℝ} {a : h04 L s} {u : ℝ → h04 L s}
    (h : IsMildFrom hs κ t1 K a u) (hK : K' ⊆ K) (ht1 : t1 ∈ K') (hc : K'.OrdConnected) :
    IsMildFrom hs κ t1 K' a u :=
  ⟨ht1, hc, h.cont.mono hK, fun t ht => h.eq t (hK ht)⟩

/-- **Concatenation** of two mild solutions based at the common endpoint `y`. -/
lemma concat {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) {a : h04 L s} {u v : ℝ → h04 L s}
    (hu : IsMildFrom hs κ y (Set.Icc x y) a u) (hv : IsMildFrom hs κ y (Set.Icc y z) a v) :
    IsMildFrom hs κ y (Set.Icc x z) a (fun t => if t ≤ y then u t else v t) := by
  set w : ℝ → h04 L s := fun t => if t ≤ y then u t else v t
  have hwu : Set.EqOn w u (Set.Icc x y) := fun t ht => by simp [w, ht.2]
  have hwv : Set.EqOn w v (Set.Icc y z) := fun t ht => by
    by_cases h : t ≤ y
    · have : t = y := le_antisymm h ht.1
      subst this
      simp only [w, h, ↓reduceIte]
      rw [hu.at_base, hv.at_base]
    · simp [w, h]
  have hunion : Set.Icc x z = Set.Icc x y ∪ Set.Icc y z := (Set.Icc_union_Icc_eq_Icc hxy hyz).symm
  refine ⟨⟨hxy, hyz⟩, Set.ordConnected_Icc, ?_, fun t ht => ?_⟩
  · rw [hunion]
    exact (hu.cont.congr hwu).union_of_isClosed (hv.cont.congr hwv) isClosed_Icc isClosed_Icc
  · by_cases h : t ≤ y
    · have htI : t ∈ Set.Icc x y := ⟨ht.1, h⟩
      rw [hwu htI, hu.eq t htI]
      congr 2
      refine intervalIntegral.integral_congr fun r hr => ?_
      have : r ∈ Set.Icc x y := by
        rw [Set.uIcc_of_ge h] at hr; exact ⟨le_trans htI.1 hr.1, hr.2⟩
      simp only [hwu this]
    · push Not at h
      have htI : t ∈ Set.Icc y z := ⟨h.le, ht.2⟩
      rw [hwv htI, hv.eq t htI]
      congr 2
      refine intervalIntegral.integral_congr fun r hr => ?_
      have : r ∈ Set.Icc y z := by
        rw [Set.uIcc_of_le h.le] at hr; exact ⟨hr.1, le_trans hr.2 htI.2⟩
      simp only [hwv this]

/-- A uniform lower bound for the existence time: `τ(a) ≥ τ_M` when `‖a‖ ≤ M`. -/
def tauM (L s κ M : ℝ) : ℝ := (64 * (1 + κ) * Cs L s * (max 1 M) ^ 2)⁻¹

lemma tauM_pos (hκ : 0 ≤ κ) (M : ℝ) : 0 < tauM L s κ M := by
  have := one_le_Cs L s
  unfold tauM; positivity

lemma tauM_le_tau (hκ : 0 ≤ κ) {M : ℝ} {a : h04 L s} (ha : ‖a‖ ≤ M) :
    tauM L s κ M ≤ tau L s κ a := by
  unfold tauM tau
  have hC := one_le_Cs L s
  apply inv_anti₀ (by positivity)
  have h1 : max 1 ‖a‖ ≤ max 1 M := max_le_max le_rfl ha
  have h2 : (max 1 ‖a‖) ^ 2 ≤ (max 1 M) ^ 2 :=
    pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) h1 2
  have : 0 ≤ 64 * (1 + κ) * Cs L s := by positivity
  exact mul_le_mul_of_nonneg_left h2 this

/-- **Extension to the right** by `τ(u(T))`. -/
lemma extend_right (hκ : 0 ≤ κ) {a T : ℝ} (ha : a ≤ 0) (hT : 0 ≤ T) {u0 : h04 L s}
    {u : ℝ → h04 L s} (hu : IsMild hs κ (Set.Icc a T) u0 u) :
    ∃ w : ℝ → h04 L s, IsMild hs κ (Set.Icc a (T + tau L s κ (u T))) u0 w := by
  obtain ⟨hτ, v, hv, -⟩ := local_existence hs hκ (u T)
  set τ := tau L s κ (u T)
  have hvT := (IsMild.shift hv T).mono (K' := Set.Icc T (T + τ))
    (fun t ht => show t + -T ∈ Set.Icc (-τ) τ from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    ⟨le_rfl, by linarith⟩ Set.ordConnected_Icc
  have huT := (IsMild.toFrom hu).rebase (t2 := T) ⟨le_trans ha hT, le_rfl⟩
  have hc := concat (le_trans ha hT) (by linarith) huT hvT
  refine ⟨fun t => if t ≤ T then u t else v (t + -T), ?_⟩
  have := (hc.rebase (t2 := 0) ⟨ha, by linarith⟩).toMild
  simp only [hT, ↓reduceIte] at this
  rwa [hu.at_zero] at this

/-- **Extension to the left** by `τ(u(a))`. -/
lemma extend_left (hκ : 0 ≤ κ) {a T : ℝ} (ha : a ≤ 0) (hT : 0 ≤ T) {u0 : h04 L s}
    {u : ℝ → h04 L s} (hu : IsMild hs κ (Set.Icc a T) u0 u) :
    ∃ w : ℝ → h04 L s, IsMild hs κ (Set.Icc (a - tau L s κ (u a)) T) u0 w := by
  obtain ⟨hτ, v, hv, -⟩ := local_existence hs hκ (u a)
  set τ := tau L s κ (u a)
  have hva := (IsMild.shift hv a).mono (K' := Set.Icc (a - τ) a)
    (fun t ht => show t + -a ∈ Set.Icc (-τ) τ from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    ⟨by linarith, le_rfl⟩ Set.ordConnected_Icc
  have hua := (IsMild.toFrom hu).rebase (t2 := a) ⟨le_rfl, le_trans ha hT⟩
  have hc := concat (by linarith) (le_trans ha hT) hva hua
  refine ⟨fun t => if t ≤ a then v (t + -a) else u t, ?_⟩
  have hw0 : (if (0 : ℝ) ≤ a then v (0 + -a) else u 0) = u0 := by
    by_cases h0 : (0 : ℝ) ≤ a
    · have ha0 : a = 0 := le_antisymm ha h0
      simp only [h0, ↓reduceIte]
      have h1 := hv.at_zero
      have h2 := hu.at_zero
      rw [ha0] at h1 ⊢
      rw [neg_zero, add_zero, h1, h2]
    · simp only [h0, ↓reduceIte]; exact hu.at_zero
  convert (hc.rebase (t2 := 0) ⟨by linarith, hT⟩).toMild using 2
  exact hw0.symm

/-- Intervals containing `0` that carry a mild solution with data `u₀`. -/
def Good (hs : 1 ≤ s) (κ : ℝ) (u0 : h04 L s) (J : Set ℝ) : Prop :=
  J.OrdConnected ∧ (0 : ℝ) ∈ J ∧ ∃ u : ℝ → h04 L s, IsMild hs κ J u0 u

/-- The maximal interval: the union of all intervals carrying a mild solution. -/
def Imax (hs : 1 ≤ s) (κ : ℝ) (u0 : h04 L s) : Set ℝ := ⋃₀ {J | Good hs κ u0 J}

lemma subset_Imax {u0 : h04 L s} {J : Set ℝ} (h : Good hs κ u0 J) : J ⊆ Imax hs κ u0 :=
  Set.subset_sUnion_of_mem h

/-- Two mild solutions agree on the intersection of their intervals. -/
lemma agree (hκ : 0 ≤ κ) {u0 : h04 L s} {J1 J2 : Set ℝ} {u v : ℝ → h04 L s}
    (hu : IsMild hs κ J1 u0 u) (hv : IsMild hs κ J2 u0 v) : ∀ t ∈ J1 ∩ J2, u t = v t := by
  have hc : (J1 ∩ J2).OrdConnected := hu.ordConnected.inter hv.ordConnected
  exact mild_unique hs hκ (hu.mono Set.inter_subset_left ⟨hu.zero_mem, hv.zero_mem⟩ hc)
    (hv.mono Set.inter_subset_right ⟨hu.zero_mem, hv.zero_mem⟩ hc)

lemma Imax_ordConnected (u0 : h04 L s) : (Imax hs κ u0).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  obtain ⟨J1, hJ1, hx1⟩ := hx
  obtain ⟨J2, hJ2, hy2⟩ := hy
  rcases le_total z 0 with h | h
  · exact ⟨J1, hJ1, hJ1.1.out hx1 hJ1.2.1 ⟨hz.1, h⟩⟩
  · exact ⟨J2, hJ2, hJ2.1.out hJ2.2.1 hy2 ⟨h, hz.2⟩⟩

lemma good_local (hκ : 0 ≤ κ) (u0 : h04 L s) :
    Good hs κ u0 (Set.Icc (-tau L s κ u0) (tau L s κ u0)) := by
  obtain ⟨hτ, v, hv, -⟩ := local_existence hs hκ u0
  exact ⟨Set.ordConnected_Icc, ⟨by linarith, hτ.le⟩, v, hv⟩

lemma zero_mem_Imax (hκ : 0 ≤ κ) (u0 : h04 L s) : (0 : ℝ) ∈ Imax hs κ u0 :=
  subset_Imax (good_local (hs := hs) hκ u0) (good_local (hs := hs) hκ u0).2.1

/-- Every point of `Imax` has a neighbourhood carried by one mild solution. -/
lemma nbhd_good (hκ : 0 ≤ κ) (u0 : h04 L s) {t : ℝ} (ht : t ∈ Imax hs κ u0) :
    ∃ J : Set ℝ, J ∈ 𝓝 t ∧ Good hs κ u0 J := by
  obtain ⟨J, hJ, htJ⟩ := ht
  obtain ⟨hc, h0, v, hv⟩ := hJ
  rcases lt_trichotomy t 0 with h | h | h
  · -- restrict to `[t, 0]` and extend to the left
    have hv' := hv.mono (J := Set.Icc t 0) (hc.out htJ h0) ⟨h.le, le_rfl⟩ Set.ordConnected_Icc
    obtain ⟨w, hw⟩ := extend_left hκ h.le le_rfl hv'
    have hτ := (local_existence hs hκ (v t)).1
    refine ⟨Set.Icc (t - tau L s κ (v t)) 0, Icc_mem_nhds (by linarith) h,
      Set.ordConnected_Icc, ⟨by linarith, le_rfl⟩, w, hw⟩
  · subst h
    have hτ := (local_existence hs hκ u0).1
    exact ⟨_, Icc_mem_nhds (by linarith) hτ, good_local hκ u0⟩
  · have hv' := hv.mono (J := Set.Icc 0 t) (hc.out h0 htJ) ⟨le_rfl, h.le⟩ Set.ordConnected_Icc
    obtain ⟨w, hw⟩ := extend_right hκ le_rfl h.le hv'
    have hτ := (local_existence hs hκ (v t)).1
    refine ⟨Set.Icc 0 (t + tau L s κ (v t)), Icc_mem_nhds h (by linarith),
      Set.ordConnected_Icc, ⟨le_rfl, by linarith⟩, w, hw⟩

lemma Imax_isOpen (hκ : 0 ≤ κ) (u0 : h04 L s) : IsOpen (Imax hs κ u0) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨J, hJn, hJ⟩ := nbhd_good hκ u0 ht
  exact Filter.mem_of_superset hJn (subset_Imax hJ)

/-- The maximal solution. -/
def umax (hs : 1 ≤ s) (κ : ℝ) (u0 : h04 L s) (t : ℝ) : h04 L s := by
  classical
  exact if h : ∃ J : Set ℝ, t ∈ J ∧ Good hs κ u0 J then
    (Classical.choose (Classical.choose_spec h).2.2.2) t else 0

lemma umax_eq (hκ : 0 ≤ κ) {u0 : h04 L s} {J : Set ℝ} {v : ℝ → h04 L s}
    (hv : IsMild hs κ J u0 v) {t : ℝ} (ht : t ∈ J) : umax hs κ u0 t = v t := by
  have h : ∃ J : Set ℝ, t ∈ J ∧ Good hs κ u0 J := ⟨J, ht, hv.ordConnected, hv.zero_mem, v, hv⟩
  unfold umax
  simp only [h, ↓reduceDIte]
  set J' := Classical.choose h
  have hJ' := Classical.choose_spec h
  have hw := Classical.choose_spec hJ'.2.2.2
  exact agree hκ hw hv t ⟨hJ'.1, ht⟩

/-- **The maximal solution is a mild solution on the maximal interval.** -/
lemma umax_mild (hκ : 0 ≤ κ) (u0 : h04 L s) : IsMild hs κ (Imax hs κ u0) u0 (umax hs κ u0) := by
  refine ⟨zero_mem_Imax hκ u0, Imax_ordConnected u0, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨J, hJn, -, -, v, hv⟩ := nbhd_good hκ u0 ht
    have hcont : ContinuousAt v t := (hv.cont t (mem_of_mem_nhds hJn)).continuousAt hJn
    have heq : umax hs κ u0 =ᶠ[𝓝 t] v :=
      Filter.mem_of_superset hJn fun r hr => umax_eq hκ hv hr
    exact (hcont.congr heq.symm).continuousWithinAt
  · obtain ⟨J, hJ, htJ⟩ := ht
    obtain ⟨hc, h0, v, hv⟩ := hJ
    rw [umax_eq hκ hv htJ, hv.duhamel_eq t htJ, duhamel, duhamel]
    congr 2
    refine intervalIntegral.integral_congr fun r hr => ?_
    simp only [umax_eq hκ hv (hc.uIcc_subset h0 htJ hr)]

/-- **Maximal interval**: there is a unique open interval containing `0` that carries a mild
solution and contains every interval (containing `0`) that carries one. -/
theorem maximal_interval (hκ : 0 ≤ κ) (u0 : h04 L s) :
    ∃! I : Set ℝ, IsOpen I ∧ I.OrdConnected ∧ (0 : ℝ) ∈ I ∧
      (∃ u : ℝ → h04 L s, IsMild hs κ I u0 u) ∧
      ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → (∃ v : ℝ → h04 L s, IsMild hs κ J u0 v) →
        J ⊆ I := by
  refine ⟨Imax hs κ u0, ⟨Imax_isOpen hκ u0, Imax_ordConnected u0, zero_mem_Imax hκ u0,
    ⟨_, umax_mild hκ u0⟩, fun J hc h0 hv => subset_Imax ⟨hc, h0, hv⟩⟩, ?_⟩
  rintro I ⟨-, hc, h0, hu, hmax⟩
  exact Set.Subset.antisymm (subset_Imax ⟨hc, h0, hu⟩)
    (hmax _ (Imax_ordConnected u0) (zero_mem_Imax hκ u0) ⟨_, umax_mild hκ u0⟩)

/-- **Blow-up alternative at a finite right endpoint**: if `Imax` is bounded above with supremum
`b`, then `‖u(t)‖_{H^s}` is unbounded as `t ↑ b`. -/
theorem blowup_right (hκ : 0 ≤ κ) (u0 : h04 L s) (hb : BddAbove (Imax hs κ u0)) :
    ∀ M δ : ℝ, 0 < δ → ∃ t ∈ Imax hs κ u0, sSup (Imax hs κ u0) - δ < t ∧
      M < ‖umax hs κ u0 t‖ := by
  intro M δ hδ
  set I := Imax hs κ u0
  set b := sSup I
  by_contra hcon
  push Not at hcon
  have hne : I.Nonempty := ⟨0, zero_mem_Imax hκ u0⟩
  obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.mp (Imax_isOpen hκ u0) 0 (zero_mem_Imax hκ u0)
  have hb0 : 0 < b := by
    have : ε / 2 ∈ I := hεI (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith)
    exact lt_of_lt_of_le (half_pos hε) (le_csSup hb this)
  set τM := tauM L s κ M
  have hτM := tauM_pos (L := L) (s := s) hκ M
  obtain ⟨t1, ht1I, ht1⟩ := exists_lt_of_lt_csSup hne
    (show max 0 (b - min δ (τM / 2)) < b from max_lt hb0 (by
      have : 0 < min δ (τM / 2) := lt_min hδ (half_pos hτM)
      linarith))
  have ht10 : 0 < t1 := lt_of_le_of_lt (le_max_left _ _) ht1
  have ht1b : b - min δ (τM / 2) < t1 := lt_of_le_of_lt (le_max_right _ _) ht1
  have hM1 : ‖umax hs κ u0 t1‖ ≤ M := hcon t1 ht1I (by linarith [min_le_left δ (τM / 2)])
  have hsub : Set.Icc 0 t1 ⊆ I :=
    (Imax_ordConnected u0).out (zero_mem_Imax hκ u0) ht1I
  have hu := (umax_mild hκ u0).mono hsub ⟨le_rfl, ht10.le⟩ Set.ordConnected_Icc
  obtain ⟨w, hw⟩ := extend_right hκ le_rfl ht10.le hu
  have hτ := tauM_le_tau (L := L) (s := s) hκ hM1
  have hmem : t1 + tau L s κ (umax hs κ u0 t1) ∈ I :=
    subset_Imax ⟨Set.ordConnected_Icc, ⟨le_rfl, by linarith [(local_existence hs hκ (umax hs κ u0 t1)).1]⟩,
      w, hw⟩ ⟨by linarith [(local_existence hs hκ (umax hs κ u0 t1)).1], le_rfl⟩
  have := le_csSup hb hmem
  linarith [min_le_right δ (τM / 2)]

/-- **Blow-up alternative at a finite left endpoint**. -/
theorem blowup_left (hκ : 0 ≤ κ) (u0 : h04 L s) (hb : BddBelow (Imax hs κ u0)) :
    ∀ M δ : ℝ, 0 < δ → ∃ t ∈ Imax hs κ u0, t < sInf (Imax hs κ u0) + δ ∧
      M < ‖umax hs κ u0 t‖ := by
  intro M δ hδ
  set I := Imax hs κ u0
  set b := sInf I
  by_contra hcon
  push Not at hcon
  have hne : I.Nonempty := ⟨0, zero_mem_Imax hκ u0⟩
  obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.mp (Imax_isOpen hκ u0) 0 (zero_mem_Imax hκ u0)
  have hb0 : b < 0 := by
    have : -(ε / 2) ∈ I := hεI (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]; linarith)
    exact lt_of_le_of_lt (csInf_le hb this) (by linarith)
  set τM := tauM L s κ M
  have hτM := tauM_pos (L := L) (s := s) hκ M
  obtain ⟨t1, ht1I, ht1⟩ := exists_lt_of_csInf_lt hne
    (show b < min 0 (b + min δ (τM / 2)) from lt_min hb0 (by
      have : 0 < min δ (τM / 2) := lt_min hδ (half_pos hτM)
      linarith))
  have ht10 : t1 < 0 := lt_of_lt_of_le ht1 (min_le_left _ _)
  have ht1b : t1 < b + min δ (τM / 2) := lt_of_lt_of_le ht1 (min_le_right _ _)
  have hM1 : ‖umax hs κ u0 t1‖ ≤ M := hcon t1 ht1I (by linarith [min_le_left δ (τM / 2)])
  have hsub : Set.Icc t1 0 ⊆ I :=
    (Imax_ordConnected u0).out ht1I (zero_mem_Imax hκ u0)
  have hu := (umax_mild hκ u0).mono hsub ⟨ht10.le, le_rfl⟩ Set.ordConnected_Icc
  obtain ⟨w, hw⟩ := extend_left hκ ht10.le le_rfl hu
  have hτ := tauM_le_tau (L := L) (s := s) hκ hM1
  have hmem : t1 - tau L s κ (umax hs κ u0 t1) ∈ I :=
    subset_Imax ⟨Set.ordConnected_Icc,
      ⟨by linarith [(local_existence hs hκ (umax hs κ u0 t1)).1], le_rfl⟩, w, hw⟩
      ⟨le_rfl, by linarith [(local_existence hs hκ (umax hs κ u0 t1)).1]⟩
  have := csInf_le hb hmem
  linarith [min_le_right δ (τM / 2)]

#print axioms concat
#print axioms extend_right
#print axioms extend_left
#print axioms umax_mild
#print axioms maximal_interval
#print axioms blowup_right
#print axioms blowup_left

/-! ## 3. `C¹_t H^{s−2}` regularity and the equation in `H^{s−2}` -/

/-- The coefficient functional `a ↦ a_n` on `h^s`. -/
def coefL (s : ℝ) (n : ℤ) : h04 L s →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => a.val n
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
    (Real.sqrt ((f04W L s).w n))⁻¹ (fun a => by
      have hw := (f04W L s).pos n
      have h1 : (f04W L s).w n * ‖a.val n‖ ^ 2 ≤ ‖a‖ ^ 2 :=
        le_hasSum (hasSum_norm_sq _ a) n (fun j _ => mul_nonneg ((f04W L s).pos j).le (sq_nonneg _))
      have hs := Real.sqrt_pos.mpr hw
      show ‖a.val n‖ ≤ (Real.sqrt ((f04W L s).w n))⁻¹ * ‖a‖
      rw [inv_mul_eq_div, le_div_iff₀ hs]
      have h2 : (‖a.val n‖ * Real.sqrt ((f04W L s).w n)) ^ 2 ≤ ‖a‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hw.le]; linarith
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp h2)

@[simp] lemma coefL_apply (s : ℝ) (n : ℤ) (a : h04 L s) : coefL s n a = a.val n := rfl

/-- Coefficients of an interval integral. -/
lemma integral_val {g : ℝ → h04 L s} {a b : ℝ} (hg : IntervalIntegrable g volume a b) (n : ℤ) :
    (∫ r in a..b, g r).val n = ∫ r in a..b, (g r).val n := by
  have := (coefL s n).intervalIntegral_comp_comm hg
  simpa using this.symm

/-- `−∂_x²` as a bounded map `H^s → H^{s−2}`: `(Δ a)_n = p_n² a_n`. -/
def lapOp (s : ℝ) : h04 L s →L[ℂ] h04 L (s - 2) :=
  LinearMap.mkContinuous
    { toFun := fun a => WSeq.mk _ (fun n => ((freq L n ^ 2 : ℝ) : ℂ) * a.val n) (by
        refine Summable.of_nonneg_of_le (fun n => mul_nonneg ((f04W L (s - 2)).pos n).le
          (sq_nonneg _)) (fun n => ?_) a.summable
        exact lap_weight_le s n (a.val n))
      map_add' := fun a b => WSeq.ext (by funext n; simp [mul_add])
      map_smul' := fun c a => WSeq.ext (by funext n; simp; ring) }
    1 (fun a => by
      rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_tsum, norm_sq_eq_tsum]
      refine Summable.tsum_le_tsum (fun n => lap_weight_le s n (a.val n)) ?_ a.summable
      exact (WSeq.summable _))
where
  lap_weight_le (s : ℝ) (n : ℤ) (z : ℂ) :
      (f04W L (s - 2)).w n * ‖((freq L n ^ 2 : ℝ) : ℂ) * z‖ ^ 2 ≤ (f04W L s).w n * ‖z‖ ^ 2 := by
    show f04Weight L (s - 2) n * _ ≤ f04Weight L s n * _
    unfold f04Weight
    have hb : 0 < 1 + freq L n ^ 2 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), mul_pow]
    have e : (1 + freq L n ^ 2) ^ (s - 2) * (1 + freq L n ^ 2) ^ 2 = (1 + freq L n ^ 2) ^ s := by
      rw [← Real.rpow_add_natCast hb.ne']; congr 1; push_cast; ring
    rw [← e]
    have hp : (freq L n ^ 2) ^ 2 ≤ (1 + freq L n ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) (by linarith) 2
    have h0 : 0 ≤ (1 + freq L n ^ 2) ^ (s - 2) := Real.rpow_nonneg hb.le _
    have := mul_le_mul_of_nonneg_left hp h0
    nlinarith [sq_nonneg ‖z‖]

@[simp] lemma lapOp_val (s : ℝ) (a : h04 L s) (n : ℤ) :
    (lapOp s a).val n = ((freq L n ^ 2 : ℝ) : ℂ) * a.val n := rfl

/-- The inclusion `H^s ↪ H^{s−2}`. -/
abbrev ι2 (s : ℝ) : h04 L s →L[ℂ] h04 L (s - 2) := h04_mono L (by linarith : s - 2 ≤ s)

/-- The time derivative `G = i∂_x²u − 2iκF(u) = −i(−∂_x²u) − 2iκF(u)` in `H^{s−2}`. -/
def Gder (hs : 1 ≤ s) (κ : ℝ) (a : h04 L s) : h04 L (s - 2) :=
  -(Complex.I • lapOp s a) - (2 * Complex.I * κ) • ι2 s (Fh hs a)

/-- **The equation in `H^{s−2}`**: `i G = −∂_x²u + 2κ|u|²u`. -/
lemma Gder_eq (hs : 1 ≤ s) (κ : ℝ) (a : h04 L s) :
    Complex.I • Gder hs κ a = lapOp s a + ((2 * κ : ℝ) : ℂ) • ι2 s (Fh hs a) := by
  unfold Gder
  rw [smul_sub, smul_neg, smul_smul, smul_smul, Complex.I_mul_I]
  have : Complex.I * (2 * Complex.I * κ) = -((2 * κ : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [this]
  simp only [neg_smul, one_smul, neg_neg, sub_neg_eq_add]

lemma Gder_val (hs : 1 ≤ s) (κ : ℝ) (a : h04 L s) (n : ℤ) :
    (Gder hs κ a).val n = -(Complex.I * ((freq L n ^ 2 : ℝ) : ℂ)) * a.val n -
      (2 * Complex.I * κ) * (Fh hs a).val n := by
  simp [Gder, ι2, h04_mono, incl_val]
  ring

lemma continuous_Gder (hs : 1 ≤ s) (κ : ℝ) : Continuous (Gder (L := L) hs κ) :=
  (((lapOp s).continuous.const_smul Complex.I).neg).sub
    (((ι2 s).continuous.comp (continuous_Fh hs)).const_smul (2 * Complex.I * (κ : ℂ)))

lemma hasDerivAt_phase (n : ℤ) (t0 x : ℝ) :
    HasDerivAt (fun t : ℝ => phase L (t - t0) n)
      (-(Complex.I * ((freq L n ^ 2 : ℝ) : ℂ)) * phase L (x - t0) n) x := by
  unfold phase
  have h : HasDerivAt (fun t : ℝ => -(Complex.I * (((t - t0) * freq L n ^ 2 : ℝ) : ℂ)))
      (-(Complex.I * ((freq L n ^ 2 : ℝ) : ℂ))) x := by
    have := (((hasDerivAt_id x).sub_const t0).mul_const (freq L n ^ 2)).ofReal_comp.const_mul
      Complex.I |>.neg
    convert this using 1
    · funext t; simp
    · simp
  have := h.cexp
  convert this using 1; ring

/-- **Scalar Duhamel ⇒ integral equation.** If `f(t) = φ(t−t₀)(f₀ − c∫_{t₀}^t φ(t₀−r) h(r) dr)` on
`[t₀, T]` (`φ` the phase) with `h` continuous there, then
`f(T) − f(t₀) = ∫_{t₀}^T (−i p_n² f(r) − c h(r)) dr`. -/
lemma scalar_integral_eq (n : ℤ) (c : ℂ) {t0 T : ℝ} {f h : ℝ → ℂ}
    (hh : ContinuousOn h (Set.uIcc t0 T)) (f0 : ℂ)
    (hf : ∀ t ∈ Set.uIcc t0 T, f t = phase L (t - t0) n *
      (f0 - c * ∫ r in t0..t, phase L (t0 - r) n * h r)) :
    f T - f t0 = ∫ r in t0..T, (-(Complex.I * ((freq L n ^ 2 : ℝ) : ℂ)) * f r - c * h r) := by
  set lo := min t0 T
  set hi := max t0 T
  have hlohi : lo ≤ hi := min_le_max
  set hext : ℝ → ℂ := fun r => h (Set.projIcc lo hi hlohi r)
  have hextc : Continuous hext :=
    hh.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun r => (Set.projIcc lo hi hlohi r).2)
  have hexteq : ∀ r ∈ Set.uIcc t0 T, hext r = h r := fun r hr => by
    simp only [hext, Set.projIcc_of_mem hlohi hr]
  set g : ℝ → ℂ := fun r => phase L (t0 - r) n * hext r
  have hgc : Continuous g := ((continuous_phase L n).comp (continuous_const.sub continuous_id)).mul
    hextc
  set A : ℝ → ℂ := fun t => phase L (t - t0) n * (f0 - c * ∫ r in t0..t, g r)
  have hA : ∀ x, HasDerivAt A (-(Complex.I * ((freq L n ^ 2 : ℝ) : ℂ)) * A x - c * hext x) x := by
    intro x
    have h1 := hasDerivAt_phase (L := L) n t0 x
    have h2 := ((hgc.integral_hasStrictDerivAt t0 x).hasDerivAt.const_mul c).const_sub f0
    have := h1.mul h2
    convert this using 1
    simp only [A, g]
    have hp : phase L (x - t0) n * phase L (t0 - x) n = 1 := by
      rw [← phase_add, show x - t0 + (t0 - x) = 0 by ring, phase_zero]
    linear_combination (c * hext x) * hp
  have hAc : Continuous fun x => -(Complex.I * ((freq L n ^ 2 : ℝ) : ℂ)) * A x - c * hext x :=
    (continuous_const.mul (continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt)).sub
      (continuous_const.mul hextc)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hA x)
    (hAc.intervalIntegrable t0 T)
  have hAf : ∀ t ∈ Set.uIcc t0 T, A t = f t := by
    intro t ht
    rw [hf t ht]
    simp only [A, g]
    congr 3
    refine intervalIntegral.integral_congr fun r hr => ?_
    have : r ∈ Set.uIcc t0 T := Set.uIcc_subset_uIcc_left ht hr
    simp only [hexteq r this]
  rw [← hAf T Set.right_mem_uIcc, ← hAf t0 Set.left_mem_uIcc, ← hFTC]
  refine intervalIntegral.integral_congr fun r hr => ?_
  simp only [hAf r hr, hexteq r hr]

/-- Coefficients of a mild solution satisfy the integrated equation between any two times. -/
lemma coeff_integral_eq {I : Set ℝ} {u0 : h04 L s} {u : ℝ → h04 L s} (hu : IsMild hs κ I u0 u)
    {t0 T : ℝ} (ht0 : t0 ∈ I) (hT : T ∈ I) (n : ℤ) :
    (u T).val n - (u t0).val n = ∫ r in t0..T, (Gder hs κ (u r)).val n := by
  have hsub : Set.uIcc t0 T ⊆ I := hu.ordConnected.uIcc_subset ht0 hT
  have hreb := (IsMild.toFrom hu).rebase ht0
  have hh : ContinuousOn (fun r => (Fh hs (u r)).val n) (Set.uIcc t0 T) :=
    ((coefL s n).continuous.comp (continuous_Fh hs)).comp_continuousOn (hu.cont.mono hsub)
  have key := scalar_integral_eq (L := L) n (2 * Complex.I * κ) hh ((u t0).val n)
    (f := fun t => (u t).val n) (fun t ht => by
      have htI := hsub ht
      have hrebt := hreb.eq t htI
      have hint := integrable_duhamel hs hu.ordConnected hu.cont t t0 t ht0 htI
      have := congrArg (coefL s n) hrebt
      rw [map_sub, map_smul, smul_eq_mul, coefL_apply, coefL_apply, coefL_apply, Sgrp_val] at this
      show (u t).val n = _
      rw [this, integral_val hint n]
      simp only [Sgrp_val]
      have e : ∫ r in t0..t, phase L (t - r) n * (Fh hs (u r)).val n =
          phase L (t - t0) n * ∫ r in t0..t, phase L (t0 - r) n * (Fh hs (u r)).val n := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun r _ => ?_
        rw [← mul_assoc, ← phase_add, show t - t0 + (t0 - r) = t - r by ring]
      rw [e]; ring)
  rw [key]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [Gder_val]

/-- **`C¹_t H^{s−2}` and the equation** (F04:lem-local, second sentence): for a mild solution on `I`,
`G(t) = −i(−∂²u) − 2iκF(u)` is continuous into `H^{s−2}`, `u(T) − u(t₀) = ∫_{t₀}^T G` in `H^{s−2}`,
`u` has derivative `G(t)` (within `I`) in `H^{s−2}` at every `t ∈ I`, and `i ∂_t u = −∂_x²u + 2κ|u|²u`
holds in `H^{s−2}`. -/
theorem mild_C1 {I : Set ℝ} {u0 : h04 L s} {u : ℝ → h04 L s} (hu : IsMild hs κ I u0 u) :
    ContinuousOn (fun t => Gder hs κ (u t)) I ∧
    (∀ t0 ∈ I, ∀ T ∈ I, ι2 s (u T) - ι2 s (u t0) = ∫ r in t0..T, Gder hs κ (u r)) ∧
    (∀ a b, Set.Icc a b ⊆ I → ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun t => ι2 s (u t)) (Gder hs κ (u t)) (Set.Icc a b) t) ∧
    (∀ t ∈ interior I, HasDerivAt (fun t => ι2 s (u t)) (Gder hs κ (u t)) t) ∧
    (∀ t ∈ I, Complex.I • Gder hs κ (u t) = lapOp s (u t) + ((2 * κ : ℝ) : ℂ) • ι2 s (Fh hs (u t))) := by
  have hGc : ContinuousOn (fun t => Gder hs κ (u t)) I :=
    (continuous_Gder hs κ).comp_continuousOn hu.cont
  have hint : ∀ t0 ∈ I, ∀ T ∈ I, ι2 s (u T) - ι2 s (u t0) = ∫ r in t0..T, Gder hs κ (u r) := by
    intro t0 ht0 T hT
    have hsub : Set.uIcc t0 T ⊆ I := hu.ordConnected.uIcc_subset ht0 hT
    apply WSeq.ext; funext n
    rw [integral_val ((hGc.mono hsub).intervalIntegrable) n]
    simp only [WSeq.val_sub, Pi.sub_apply, ι2, h04_mono, incl_val]
    exact coeff_integral_eq hu ht0 hT n
  have hderIcc : ∀ a b, Set.Icc a b ⊆ I → ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun t => ι2 s (u t)) (Gder hs κ (u t)) (Set.Icc a b) t := by
    intro a b hab t ht
    have ha : a ∈ I := hab ⟨le_rfl, le_trans ht.1 ht.2⟩
    have hGab := hGc.mono hab
    have : Fact (t ∈ Set.Icc a b) := ⟨ht⟩
    have hd := intervalIntegral.integral_hasDerivWithinAt_right
      (f := fun r => Gder hs κ (u r)) (a := a) (b := t) (s := Set.Icc a b) (t := Set.Icc a b)
      ((hGab.mono (Set.uIcc_subset_Icc ⟨le_rfl, le_trans ht.1 ht.2⟩ ht)).intervalIntegrable)
      (hGab.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hGab t ht)
    have hd2 := hd.const_add (ι2 s (u a))
    refine hd2.congr (fun r hr => ?_) ?_
    · rw [← hint a ha r (hab hr)]; abel
    · rw [← hint a ha t (hab ht)]; abel
  refine ⟨hGc, hint, hderIcc, fun t ht => ?_, fun t _ => Gder_eq hs κ (u t)⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior t ht
  have hsub : Set.Icc (t - ε / 2) (t + ε / 2) ⊆ I := by
    intro x hx
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact (hderIcc _ _ hsub t ⟨by linarith, by linarith⟩).hasDerivAt
    (Icc_mem_nhds (by linarith) (by linarith))

#print axioms coefL_apply
#print axioms integral_val
#print axioms Gder_eq
#print axioms scalar_integral_eq
#print axioms coeff_integral_eq
#print axioms mild_C1

/-! ## 4. The du Bois-Reymond lemma -/

/-- A test function on `I`: smooth, compactly supported, support in `I`. -/
def IsTest (I : Set ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ I

/-- A compact subset of an open interval lies strictly inside a closed subinterval. -/
lemma bracket {I K : Set ℝ} (hI : IsOpen I) (hc : I.OrdConnected) (hK : IsCompact K)
    (hKI : K ⊆ I) {t0 : ℝ} (ht0 : t0 ∈ I) :
    ∃ a b : ℝ, Set.Icc a b ⊆ I ∧ K ⊆ Set.Ioo a b ∧ t0 ∈ Set.Ioo a b := by
  set K' := insert t0 K
  have hK' : IsCompact K' := hK.insert t0
  have hne : K'.Nonempty := ⟨t0, Set.mem_insert _ _⟩
  have hK'I : K' ⊆ I := Set.insert_subset ht0 hKI
  have hm := hK'.sInf_mem hne
  have hM := hK'.sSup_mem hne
  obtain ⟨ε1, hε1, hb1⟩ := Metric.isOpen_iff.mp hI _ (hK'I hm)
  obtain ⟨ε2, hε2, hb2⟩ := Metric.isOpen_iff.mp hI _ (hK'I hM)
  set ε := min ε1 ε2
  have hε : 0 < ε := lt_min hε1 hε2
  have ha : sInf K' - ε / 2 ∈ I := hb1 (by
    rw [Metric.mem_ball, Real.dist_eq, show sInf K' - ε / 2 - sInf K' = -(ε / 2) by ring, abs_neg,
      abs_of_pos (half_pos hε)]
    linarith [min_le_left ε1 ε2])
  have hb : sSup K' + ε / 2 ∈ I := hb2 (by
    rw [Metric.mem_ball, Real.dist_eq, show sSup K' + ε / 2 - sSup K' = ε / 2 by ring,
      abs_of_pos (half_pos hε)]
    linarith [min_le_right ε1 ε2])
  have hsub : K' ⊆ Set.Ioo (sInf K' - ε / 2) (sSup K' + ε / 2) := fun x hx =>
    ⟨by linarith [csInf_le hK'.bddBelow hx, half_pos hε],
      by linarith [le_csSup hK'.bddAbove hx, half_pos hε]⟩
  exact ⟨_, _, hc.out ha hb, fun x hx => hsub (Set.mem_insert_of_mem _ hx),
    hsub (Set.mem_insert _ _)⟩

lemma eq_zero_of_not_mem {φ : ℝ → ℝ} {a b : ℝ} (h : tsupport φ ⊆ Set.Ioo a b) {x : ℝ}
    (hx : x ∉ Set.Ioo a b) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h' => hx (h h'))

lemma integral_eq_interval {F : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∉ Set.Ioo a b, F x = 0) : ∫ x, F x = ∫ x in a..b, F x := by
  rw [intervalIntegral.integral_of_le hab]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc a b) (fun x hx =>
    hF x (fun h => hx ⟨h.1, h.2.le⟩))).symm

/-- `φ • H` is continuous with compact support for a test function `φ` and `H` continuous on `I`. -/
lemma test_smul {I : Set ℝ} (hI : IsOpen I) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφI : tsupport φ ⊆ I) {H : ℝ → ℂ} (hH : ContinuousOn H I) :
    Integrable (fun t => φ t • H t) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (hφs.smul_right (f' := H))
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ I
  · exact hφc.continuousAt.smul (hH.continuousAt (hI.mem_nhds hx))
  · have hx' : x ∉ tsupport φ := fun h => hx (hφI h)
    have h0 : (fun t => φ t • H t) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with t ht
      simp [ht]
    exact (continuousAt_const.congr h0.symm)

lemma IsTest.deriv {I : Set ℝ} {φ : ℝ → ℝ} (h : IsTest I φ) : IsTest I (deriv φ) :=
  ⟨(contDiff_infty_iff_deriv.mp h.1).2, h.2.1.deriv, (tsupport_deriv_subset).trans h.2.2⟩

/-- A continuous function on an open set that vanishes a.e. there vanishes everywhere there. -/
lemma eq_zero_of_ae {I : Set ℝ} (hI : IsOpen I) {F : ℝ → ℂ} (hF : ContinuousOn F I)
    (hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ I → F x = 0) : ∀ x ∈ I, F x = 0 := by
  intro x hx
  by_contra hne
  have hS : {y | y ∈ I ∧ F y ≠ 0} ∈ 𝓝 x := by
    have h1 := (hF.continuousAt (hI.mem_nhds hx)).eventually_ne hne
    filter_upwards [hI.mem_nhds hx, h1] with y hy1 hy2
    exact ⟨hy1, hy2⟩
  have hpos := Measure.measure_pos_of_mem_nhds (μ := (volume : Measure ℝ)) hS
  rw [ae_iff] at hae
  have : volume {y | y ∈ I ∧ F y ≠ 0} = 0 :=
    measure_mono_null (fun y hy => show ¬ (y ∈ I → F y = 0) from fun h' => hy.2 (h' hy.1)) hae
  rw [this] at hpos
  exact lt_irrefl _ hpos

/-- **Zero distributional derivative ⇒ constant** on an open interval. -/
lemma const_of_zero_deriv {I : Set ℝ} (hI : IsOpen I) (hc : I.OrdConnected) {H : ℝ → ℂ}
    (hH : ContinuousOn H I) (h : ∀ φ, IsTest I φ → ∫ t, deriv φ t • H t = 0) {t0 : ℝ}
    (ht0 : t0 ∈ I) : ∀ t ∈ I, H t = H t0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hI t0 ht0
  let ψb : ContDiffBump t0 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  set ψ := ψb.normed volume
  have hψc : ContDiff ℝ ∞ ψ := ψb.contDiff_normed
  have hψs : HasCompactSupport ψ := ψb.hasCompactSupport_normed
  have hψI : tsupport ψ ⊆ I := by
    rw [ψb.tsupport_normed_eq]
    exact (Metric.closedBall_subset_ball (by show r / 2 < r; linarith)).trans hball
  have hψ1 : ∫ x, ψ x = 1 := ψb.integral_normed
  set c := ∫ t, ψ t • H t
  have key : ∀ φ, IsTest I φ → ∫ t, φ t • (H t - c) = 0 := by
    intro φ hφ
    obtain ⟨hφc, hφs, hφI⟩ := hφ
    set m := ∫ x, φ x
    set ρ : ℝ → ℝ := fun x => φ x - m * ψ x
    have hρc : ContDiff ℝ ∞ ρ := hφc.sub (contDiff_const.mul hψc)
    obtain ⟨a, b, hab, hKab, -⟩ := bracket hI hc (hφs.union hψs) (Set.union_subset hφI hψI) ht0
    have hab' : a < b := by
      obtain ⟨x, hx⟩ : (tsupport ψ).Nonempty := by
        rw [ψb.tsupport_normed_eq]; exact ⟨t0, Metric.mem_closedBall_self (by positivity)⟩
      have := hKab (Or.inr hx); exact this.1.trans this.2
    have hρ0 : ∀ x ∉ Set.Ioo a b, ρ x = 0 := by
      intro x hx
      simp only [ρ, eq_zero_of_not_mem (hKab.trans' Set.subset_union_left) hx,
        eq_zero_of_not_mem (hKab.trans' Set.subset_union_right) hx, mul_zero, sub_zero]
    set χ : ℝ → ℝ := fun t => ∫ x in a..t, ρ x
    have hχd : ∀ t, HasDerivAt χ (ρ t) t := fun t =>
      (hρc.continuous.integral_hasStrictDerivAt a t).hasDerivAt
    have hderiv : deriv χ = ρ := funext fun t => (hχd t).deriv
    have hχc : ContDiff ℝ ∞ χ :=
      contDiff_infty_iff_deriv.mpr ⟨fun t => (hχd t).differentiableAt, by rw [hderiv]; exact hρc⟩
    have hφi : Integrable φ := hφc.continuous.integrable_of_hasCompactSupport hφs
    have hψi : Integrable ψ := hψc.continuous.integrable_of_hasCompactSupport hψs
    have htot : ∫ x in a..b, ρ x = 0 := by
      have e := integral_eq_interval (F := fun x => ((ρ x : ℝ) : ℂ)) hab'.le
        (fun x hx => by simp [hρ0 x hx])
      have e2 : ∫ x, ((ρ x : ℝ) : ℂ) = ((∫ x, ρ x : ℝ) : ℂ) := integral_ofReal
      have e3 : ∫ x in a..b, ((ρ x : ℝ) : ℂ) = ((∫ x in a..b, ρ x : ℝ) : ℂ) :=
        intervalIntegral.integral_ofReal
      have e4 : ∫ x, ρ x = 0 := by
        simp only [ρ]
        rw [integral_sub hφi (hψi.const_mul m), integral_const_mul, hψ1]; ring
      have : ((∫ x in a..b, ρ x : ℝ) : ℂ) = 0 := by rw [← e3, ← e, e2, e4]; simp
      exact_mod_cast this
    have hχ0 : ∀ x ∉ Set.Ioo a b, χ x = 0 := by
      intro x hx
      rcases le_or_gt x a with h | h
      · simp only [χ]
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun y hy => by
          apply hρ0; rw [Set.uIcc_of_ge h] at hy; exact fun h' => by linarith [h'.1, hy.2])]
        simp
      · have hbx : b ≤ x := by
          by_contra h'; push Not at h'; exact hx ⟨h, h'⟩
        simp only [χ]
        rw [← intervalIntegral.integral_add_adjacent_intervals (b := b)
          (hρc.continuous.intervalIntegrable _ _) (hρc.continuous.intervalIntegrable _ _), htot,
          zero_add]
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun y hy => by
          apply hρ0; rw [Set.uIcc_of_le hbx] at hy; exact fun h' => by linarith [h'.2, hy.1])]
        simp
    have hχsupp : tsupport χ ⊆ Set.Icc a b := by
      apply closure_minimal _ isClosed_Icc
      intro x hx
      by_contra h
      exact hx (hχ0 x (fun h' => h ⟨h'.1.le, h'.2.le⟩))
    have hχtest : IsTest I χ :=
      ⟨hχc, IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport χ) hχsupp,
        hχsupp.trans hab⟩
    have h1 := h χ hχtest
    rw [hderiv] at h1
    have hφH := test_smul hI hφc.continuous hφs hφI hH
    have hψH := test_smul hI hψc.continuous hψs hψI hH
    have e1 : ∫ t, ρ t • H t = (∫ t, φ t • H t) - m • c := by
      have : (fun t => ρ t • H t) = fun t => φ t • H t - m • (ψ t • H t) := by
        funext t; simp only [ρ, sub_smul, mul_smul]
      have hψH' : Integrable (fun t => m • (ψ t • H t)) := hψH.smul m
      rw [this, integral_sub hφH hψH', integral_smul]
    have e2 : ∫ t, φ t • (H t - c) = (∫ t, φ t • H t) - m • c := by
      have : (fun t => φ t • (H t - c)) = fun t => φ t • H t - φ t • c := by
        funext t; rw [smul_sub]
      rw [this, integral_sub hφH (hφi.smul_const c), integral_smul_const]
    rw [e2, ← e1, h1]
  have hae := hI.ae_eq_zero_of_integral_contDiff_smul_eq_zero (f := fun t => H t - c)
    ((hH.sub continuousOn_const).locallyIntegrableOn hI.measurableSet)
    (fun g hg hgc hgs => key g ⟨hg, hgc, hgs⟩)
  have hall := eq_zero_of_ae hI (hH.sub continuousOn_const) hae
  intro t ht
  have h1 : H t - c = 0 := hall t ht
  have h2 : H t0 - c = 0 := hall t0 ht0
  rw [sub_eq_zero.mp h1, sub_eq_zero.mp h2]

/-- **du Bois-Reymond lemma.** If `f, g` are continuous on an open interval `I` and
`∫ φ' f = −∫ φ g` for every test function `φ` on `I`, then `f(t) − f(t₀) = ∫_{t₀}^t g` on `I`
(so `f` is `C¹` on `I` with `f' = g`). -/
lemma dbr {I : Set ℝ} (hI : IsOpen I) (hc : I.OrdConnected) {f g : ℝ → ℂ}
    (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (h : ∀ φ, IsTest I φ → ∫ t, deriv φ t • f t = -∫ t, φ t • g t) {t0 : ℝ} (ht0 : t0 ∈ I) :
    ∀ t ∈ I, f t - f t0 = ∫ x in t0..t, g x := by
  set G : ℝ → ℂ := fun t => ∫ x in t0..t, g x
  have hgi : ∀ x ∈ I, IntervalIntegrable g volume t0 x := fun x hx =>
    (hg.mono (hc.uIcc_subset ht0 hx)).intervalIntegrable
  have hGd : ∀ x ∈ I, HasDerivAt G (g x) x := fun x hx =>
    intervalIntegral.integral_hasDerivAt_right (hgi x hx)
      (hg.stronglyMeasurableAtFilter hI x hx) (hg.continuousAt (hI.mem_nhds hx))
  set H : ℝ → ℂ := fun t => f t - G t
  have hH : ContinuousOn H I := hf.sub fun x hx => (hGd x hx).continuousAt.continuousWithinAt
  have hzero : ∀ φ, IsTest I φ → ∫ t, deriv φ t • H t = 0 := by
    intro φ hφ
    obtain ⟨hφc, hφs, hφI⟩ := hφ
    obtain ⟨a, b, hab, hKab, ht0ab⟩ := bracket hI hc hφs hφI ht0
    have hab' : a ≤ b := (ht0ab.1.trans ht0ab.2).le
    have hφ0 : ∀ x ∉ Set.Ioo a b, φ x = 0 := fun x hx => eq_zero_of_not_mem hKab hx
    have hdφ0 : ∀ x ∉ Set.Ioo a b, deriv φ x = 0 := fun x hx =>
      eq_zero_of_not_mem (tsupport_deriv_subset.trans hKab) hx
    have hsubI : Set.uIcc a b ⊆ I := by rw [Set.uIcc_of_le hab']; exact hab
    have hdφc : Continuous (deriv φ) := (contDiff_infty_iff_deriv.mp hφc).2.continuous
    -- reduce to `[a, b]`
    have e0 := integral_eq_interval (F := fun t => deriv φ t • H t) hab'
      (fun x hx => by simp [hdφ0 x hx])
    have e1 := integral_eq_interval (F := fun t => deriv φ t • f t) hab'
      (fun x hx => by simp [hdφ0 x hx])
    have e2 := integral_eq_interval (F := fun t => φ t • g t) hab'
      (fun x hx => by simp [hφ0 x hx])
    have hfab : IntervalIntegrable (fun t => deriv φ t • f t) volume a b :=
      (hdφc.continuousOn.smul (hf.mono hsubI)).intervalIntegrable
    have hGc : ContinuousOn G (Set.uIcc a b) := fun x hx =>
      (hGd x (hsubI hx)).continuousAt.continuousWithinAt
    have hGab : IntervalIntegrable (fun t => deriv φ t • G t) volume a b :=
      (hdφc.continuousOn.smul hGc).intervalIntegrable
    -- integration by parts for `G`
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
      (u := G) (u' := g) (v := fun x => ((φ x : ℝ) : ℂ)) (v' := fun x => ((deriv φ x : ℝ) : ℂ))
      (fun x hx => hGd x (hsubI hx))
      (fun x _ => ((hφc.differentiable (by simp)) x).hasDerivAt.ofReal_comp)
      ((hg.mono hsubI).intervalIntegrable)
      ((Complex.continuous_ofReal.comp hdφc).intervalIntegrable _ _)
    have hφa : φ a = 0 := hφ0 a (fun h => lt_irrefl a h.1)
    have hφb : φ b = 0 := hφ0 b (fun h => lt_irrefl b h.2)
    simp only [hφa, hφb, Complex.ofReal_zero, mul_zero, sub_zero, zero_sub] at hibp
    have hG : ∫ x in a..b, deriv φ x • G x = -∫ x in a..b, φ x • g x := by
      have l : ∫ x in a..b, deriv φ x • G x = ∫ x in a..b, G x * ((deriv φ x : ℝ) : ℂ) :=
        intervalIntegral.integral_congr fun x _ => by
          simp only [Complex.real_smul]; ring
      have r : ∫ x in a..b, φ x • g x = ∫ x in a..b, g x * ((φ x : ℝ) : ℂ) :=
        intervalIntegral.integral_congr fun x _ => by
          simp only [Complex.real_smul]; ring
      rw [l, r, hibp]
    rw [e0]
    have : (fun t => deriv φ t • H t) = fun t => deriv φ t • f t - deriv φ t • G t := by
      funext t; simp only [H, smul_sub]
    rw [this, intervalIntegral.integral_sub hfab hGab, ← e1, h φ ⟨hφc, hφs, hφI⟩, e2, hG]
    ring
  have hconst := const_of_zero_deriv hI hc hH hzero ht0
  intro t ht
  have := hconst t ht
  simp only [H, G, intervalIntegral.integral_same, sub_zero] at this
  rw [← this]; ring

#print axioms bracket
#print axioms test_smul
#print axioms eq_zero_of_ae
#print axioms const_of_zero_deriv
#print axioms dbr

/-! ## 5. Distributional solutions are mild; stability and uniqueness for them -/

/-- **`C_tH¹` distributional solution** of `F04:eq-nls` on an open interval `I`: `u ∈ C(I; H¹)` and the
equation `i∂_t u = −∂_x²u + 2κ|u|²u` holds when tested against `φ(t) \overline{e_n(x)}` for every
spatial mode `n` and every test function `φ ∈ C_c^∞(I)`, i.e.
`−i ∫ φ'(t) û_n(t) dt = ∫ φ(t) (p_n² û_n(t) + 2κ \widehat{F(u(t))}(n)) dt`.
These product test functions are space-time test functions on `I × 𝕋_L`, so every space-time
distributional solution satisfies this (the printed proof uses exactly this "testing against each
spatial Fourier mode"). -/
structure IsDistSol (κ : ℝ) (I : Set ℝ) (u : ℝ → h04 L 1) : Prop where
  isOpen : IsOpen I
  ordConnected : I.OrdConnected
  cont : ContinuousOn u I
  weak : ∀ n : ℤ, ∀ φ : ℝ → ℝ, IsTest I φ →
    -Complex.I * ∫ t, deriv φ t • (u t).val n =
      ∫ t, φ t • (((freq L n ^ 2 : ℝ) : ℂ) * (u t).val n +
        ((2 * κ : ℝ) : ℂ) * (Fh (le_refl (1 : ℝ)) (u t)).val n)

lemma hasDerivAt_of_integral {I : Set ℝ} (hI : IsOpen I) (hc : I.OrdConnected) {f g : ℝ → ℂ}
    (hg : ContinuousOn g I) {t0 : ℝ} (ht0 : t0 ∈ I) (hf : ∀ t ∈ I, f t - f t0 = ∫ x in t0..t, g x) :
    ∀ t ∈ I, HasDerivAt f (g t) t := by
  intro t ht
  have hd := intervalIntegral.integral_hasDerivAt_right
    ((hg.mono (hc.uIcc_subset ht0 ht)).intervalIntegrable)
    (hg.stronglyMeasurableAtFilter hI t ht) (hg.continuousAt (hI.mem_nhds ht))
  have hd2 := hd.const_add (f t0)
  refine hd2.congr_of_eventuallyEq ?_
  filter_upwards [hI.mem_nhds ht] with x hx
  rw [← hf x hx]; ring

lemma hasDerivAt_phase' (n : ℤ) (t0 x : ℝ) :
    HasDerivAt (fun t : ℝ => phase L (t0 - t) n)
      (Complex.I * ((freq L n ^ 2 : ℝ) : ℂ) * phase L (t0 - x) n) x := by
  unfold phase
  have h : HasDerivAt (fun t : ℝ => -(Complex.I * (((t0 - t) * freq L n ^ 2 : ℝ) : ℂ)))
      (Complex.I * ((freq L n ^ 2 : ℝ) : ℂ)) x := by
    have := (((hasDerivAt_id x).const_sub t0).mul_const (freq L n ^ 2)).ofReal_comp.const_mul
      Complex.I |>.neg
    convert this using 1
    · funext t; simp
    · push_cast; ring
  have := h.cexp
  convert this using 1; ring

/-- **Every `C_tH¹` distributional solution is a mild solution**, based at any time `t₀ ∈ I`
(Duhamel formula `F04:eq-duhamel` based at `t₀`, coefficient by coefficient). -/
theorem dist_mildFrom {κ : ℝ} {I : Set ℝ} {u : ℝ → h04 L 1} (hD : IsDistSol κ I u) {t0 : ℝ}
    (ht0 : t0 ∈ I) : IsMildFrom (le_refl (1 : ℝ)) κ t0 I (u t0) u := by
  refine ⟨ht0, hD.ordConnected, hD.cont, fun t ht => ?_⟩
  have hsub : Set.uIcc t0 t ⊆ I := hD.ordConnected.uIcc_subset ht0 ht
  apply WSeq.ext; funext n
  set c : ℂ := 2 * Complex.I * κ
  set p2 : ℂ := ((freq L n ^ 2 : ℝ) : ℂ)
  set f : ℝ → ℂ := fun r => (u r).val n
  set Fn : ℝ → ℂ := fun r => (Fh (le_refl (1 : ℝ)) (u r)).val n
  have hfc : ContinuousOn f I := ((coefL 1 n).continuous).comp_continuousOn hD.cont
  have hFc : ContinuousOn Fn I :=
    ((coefL 1 n).continuous.comp (continuous_Fh (le_refl (1 : ℝ)))).comp_continuousOn hD.cont
  set g : ℝ → ℂ := fun r => -Complex.I * (p2 * f r + ((2 * κ : ℝ) : ℂ) * Fn r)
  have hgc : ContinuousOn g I := continuousOn_const.mul
    ((continuousOn_const.mul hfc).add (continuousOn_const.mul hFc))
  -- the du Bois-Reymond hypothesis
  have hdbr : ∀ φ, IsTest I φ → ∫ r, deriv φ r • f r = -∫ r, φ r • g r := by
    intro φ hφ
    have hw := hD.weak n φ hφ
    have e : ∫ r, φ r • g r = -Complex.I * ∫ r, φ r • (p2 * f r + ((2 * κ : ℝ) : ℂ) * Fn r) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun r => by
        simp only [g, Complex.real_smul]; ring)
    rw [e, ← hw]
    simp only [f]
    rw [neg_mul, neg_neg, ← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  have hint := dbr hD.isOpen hD.ordConnected hfc hgc hdbr ht0
  have hder := hasDerivAt_of_integral hD.isOpen hD.ordConnected hgc ht0 hint
  -- the integrating factor
  set A : ℝ → ℂ := fun r => phase L (t0 - r) n * f r
  have hA : ∀ x ∈ Set.uIcc t0 t, HasDerivAt A (-c * (phase L (t0 - x) n * Fn x)) x := by
    intro x hx
    have := (hasDerivAt_phase' (L := L) n t0 x).mul (hder x (hsub hx))
    convert this using 1
    simp only [g, c, p2]
    push_cast
    ring
  have hAint : IntervalIntegrable (fun x => -c * (phase L (t0 - x) n * Fn x)) volume t0 t :=
    (continuousOn_const.mul (((continuous_phase L n).comp
      (continuous_const.sub continuous_id)).continuousOn.mul (hFc.mono hsub))).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hA hAint
  rw [intervalIntegral.integral_const_mul] at hFTC
  simp only [A, sub_self, phase_zero, one_mul] at hFTC
  -- back to the coefficient of the vector Duhamel formula
  have hvi := integrable_duhamel (le_refl (1 : ℝ)) hD.ordConnected hD.cont t t0 t ht0 ht
  change f t = coefL 1 n (Sgrp 1 (t - t0) (u t0) -
    c • ∫ r in t0..t, Sgrp 1 (t - r) (Fh (le_refl (1 : ℝ)) (u r)))
  rw [map_sub, map_smul, smul_eq_mul, coefL_apply, Sgrp_val,
    ← (coefL 1 n).intervalIntegral_comp_comm hvi]
  simp only [coefL_apply, Sgrp_val]
  have e : ∫ r in t0..t, phase L (t - r) n * Fn r =
      phase L (t - t0) n * ∫ r in t0..t, phase L (t0 - r) n * Fn r := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [← mul_assoc, ← phase_add, show t - t0 + (t0 - r) = t - r by ring]
  show f t = phase L (t - t0) n * f t0 - c * ∫ r in t0..t, phase L (t - r) n * Fn r
  rw [e]
  have hp : phase L (t - t0) n * phase L (t0 - t) n = 1 := by
    rw [← phase_add, show t - t0 + (t0 - t) = 0 by ring, phase_zero]
  linear_combination (-(f t)) * hp + (-(phase L (t - t0) n)) * hFTC

/-- With `0 ∈ I`, a distributional solution is a mild solution in the sense of `F04:eq-duhamel`. -/
theorem dist_isMild {κ : ℝ} {I : Set ℝ} {u : ℝ → h04 L 1} (hD : IsDistSol κ I u)
    (h0 : (0 : ℝ) ∈ I) : IsMild (le_refl (1 : ℝ)) κ I (u 0) u :=
  (dist_mildFrom hD h0).toMild

/-- **`F04:eq-stability` for `C_tH¹` distributional solutions**: if `‖u‖_{H¹}, ‖v‖_{H¹} ≤ K` on `I`,
then for any two times `t₀, t ∈ I`,
`‖u(t) − v(t)‖_{H¹} ≤ exp(4κ C_{1,L} K² |t − t₀|) ‖u(t₀) − v(t₀)‖_{H¹}`. -/
theorem dist_stability {κ : ℝ} (hκ : 0 ≤ κ) {I : Set ℝ} {u v : ℝ → h04 L 1}
    (hu : IsDistSol κ I u) (hv : IsDistSol κ I v) {K : ℝ}
    (hK : ∀ r ∈ I, ‖u r‖ ≤ K ∧ ‖v r‖ ≤ K) {t0 t : ℝ} (ht0 : t0 ∈ I) (ht : t ∈ I) :
    ‖u t - v t‖ ≤ Real.exp (4 * κ * Cs L 1 * K ^ 2 * |t - t0|) * ‖u t0 - v t0‖ :=
  (dist_mildFrom hu ht0).stability hκ (dist_mildFrom hv ht0) hK ht0 ht

/-- **Uniqueness among `C_tH¹` distributional solutions** with the same value at some time. -/
theorem dist_unique {κ : ℝ} (hκ : 0 ≤ κ) {I : Set ℝ} {u v : ℝ → h04 L 1}
    (hu : IsDistSol κ I u) (hv : IsDistSol κ I v) {t0 : ℝ} (ht0 : t0 ∈ I) (h : u t0 = v t0) :
    ∀ t ∈ I, u t = v t := by
  have hv' := dist_mildFrom hv ht0
  rw [← h] at hv'
  exact (dist_mildFrom hu ht0).unique hκ hv'

#print axioms hasDerivAt_of_integral
#print axioms dist_mildFrom
#print axioms dist_isMild
#print axioms dist_stability
#print axioms dist_unique
#print axioms IsMildFrom.mono
#print axioms tauM_le_tau
#print axioms agree
#print axioms Imax_ordConnected
#print axioms Imax_isOpen
#print axioms nbhd_good
#print axioms umax_eq
#print axioms lapOp_val
#print axioms Gder_val
#print axioms continuous_Gder
#print axioms hasDerivAt_phase
#print axioms hasDerivAt_phase'
#print axioms integral_eq_interval
#print axioms IsTest.deriv

end QuantumNLS.LocalWellPosednessFull
