/-
QuantumNLS.CollisionCapacity — R-08EE7BE5 `contact:lem:capacity` (owner: opus_tensor).

Source (`chapters/foundations/A01.tex:62-90`): `C = ⋃_{i<j} Σ_ij`,
`E = ⋃_{{i,j} ≠ {k,l}} (Σ_ij ∩ Σ_kl)` (unordered pairs; triple coincidences and two disjoint pairs).
Lemma: "There are smooth functions `0 ≤ η_ε ≤ 1` on `𝕋_L^N`, identically one on a neighborhood of
`E`, such that `‖η_ε‖_{H¹} → 0`. Consequently, an `H^{-1}(𝕋_L^N)` distribution supported on `E` is
zero."

Literal Lean statements (all proved, standard axioms only):
* `coincE L N` is `E` exactly as in the source (union over ordered pairs of distinct unordered pairs
  `{i<j} ≠ {k<l}` of `Σ_ij ∩ Σ_kl ⊆ 𝕋_L^N`).
* **`exists_capacity_cutoffs`** (part 1): a sequence `η_M` of smooth lattice-periodic functions
  (`IsTorusTest`, i.e. smooth functions on `𝕋_L^N`), real-valued with `0 ≤ η_M ≤ 1`, with `η_M ≡ 1`
  on an open neighbourhood `U_M ⊇ E` (`M ≥ 1`), and `‖η_M‖_{H¹} → 0` in the frozen physical
  `PhysH1` norm (`norm_sq_smoothH1_eta_le : ‖η_M‖²_{H¹} ≤ D/M`).
* `SupportedOnE R` ("supported on `E`", literal): the continuous functional `R` on `PhysH1`
  (an `H^{-1}` distribution) vanishes on every smooth test whose (closed) support is disjoint from
  `E`.  **`eq_zero_of_supportedOnE`** (part 2): such `R` is `0`.

Argument deviations (recorded; statement unchanged):
* D1. Cutoff: instead of the tubular log-cutoff `θ(log r / log ε)` per flat piece, the dyadic
  average `η_{q,M} = M⁻¹ Σ_{n<M} χ(4ⁿ Q_q)` with the global smooth transverse function
  `Q_q = sin²(π(x_a−x_b)/L) + sin²(π(x_c−x_d)/L)` (the same codimension-two capacity mechanism: each
  dyadic shell carries `O(1)` Dirichlet energy, shells are disjoint, averaging gives `O(1/M)`);
  the parameter is `M ∈ ℕ` (`ε ≈ 4^{-M}`) instead of `ε → 0`.
* D2. Union over the finite family via `Ψ(Σ_q η_{q,M})` (`Ψ` = smooth transition) instead of
  `1 − ∏_S (1 − η_{S,ε})`.
* D3. Transverse volume bound `μ{Q_q ≤ t} ≤ c_q L² t` via Haar pushforward along the surjective
  homomorphism `y ↦ (y_a − y_b, y_c − y_d) : 𝕋^N → 𝕋^2` and Jordan's inequality, instead of tubular
  coordinates and the transverse volume element.
* D4. "Multiplication by fixed smooth `φ` is bounded on `H¹`" is proved only on smooth tests
  (`exists_mul_bound`), which is all the argument uses; "`R` vanishes on every smooth test ⇒ `R = 0`"
  uses density of trigonometric polynomials in `PhysH1` (frozen ContactDistribution).
-/
import QuantumNLS.ContactDistribution
import QuantumNLS.CollisionIdentification

open scoped InnerProductSpace ENNReal NNReal ComplexConjugate ContDiff
open MeasureTheory QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor
  QuantumNLS.ProductWeakDerivatives

noncomputable section

namespace QuantumNLS.CollisionCapacity

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-! ## §0 The coincidence set `E` -/

/-- Unordered pairs `{i,j}`, represented by `i < j`. -/
abbrev UPair (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

/-- The collision set `Σ_ij = {x_i = x_j}` on `𝕋_L^N`. -/
def collSet (L : ℝ) (p : UPair N) : Set (Fin N → AddCircle L) := {y | y p.1.1 = y p.1.2}

/-- **The coincidence set** `E = ⋃_{{i,j} ≠ {k,l}} (Σ_ij ∩ Σ_kl)`. -/
def coincE (L : ℝ) (N : ℕ) : Set (Fin N → AddCircle L) :=
  ⋃ (p : UPair N) (q : UPair N) (_ : p ≠ q), collSet L p ∩ collSet L q

/-- Ordered pairs of distinct unordered pairs (index set of the intersections in `E`). -/
abbrev QPair (N : ℕ) := {pq : UPair N × UPair N // pq.1 ≠ pq.2}

/-! ## §1 Haar pushforward along `y ↦ (y_a − y_b, y_c − y_d)` -/

/-- The additive homomorphism `π_q y = (y_a − y_b, y_c − y_d) ∈ 𝕋_L^2`. -/
def piHom (L : ℝ) (q : QPair N) : (Fin N → AddCircle L) →+ (Fin 2 → AddCircle L) where
  toFun y k := if k = 0 then y q.1.1.1.1 - y q.1.1.1.2 else y q.1.2.1.1 - y q.1.2.1.2
  map_zero' := by funext k; by_cases h : k = 0 <;> simp [h]
  map_add' x y := by
    funext k; by_cases h : k = 0 <;> simp only [h, ↓reduceIte, Pi.add_apply] <;> abel

omit [Fact (0 < L)] in
theorem piHom_apply (q : QPair N) (y : Fin N → AddCircle L) (k : Fin 2) :
    piHom L q y k = if k = 0 then y q.1.1.1.1 - y q.1.1.1.2 else y q.1.2.1.1 - y q.1.2.1.2 :=
  rfl

omit [Fact (0 < L)] in
theorem continuous_piHom (q : QPair N) : Continuous (piHom L q) := by
  refine continuous_pi fun k => ?_
  show Continuous fun y : Fin N → AddCircle L =>
    if k = 0 then y q.1.1.1.1 - y q.1.1.1.2 else y q.1.2.1.1 - y q.1.2.1.2
  split_ifs
  · exact (continuous_apply _).sub (continuous_apply _)
  · exact (continuous_apply _).sub (continuous_apply _)

omit [Fact (0 < L)] in
/-- For distinct unordered pairs `{a,b} ≠ {c,d}`: not both `a ∈ {c,d}` and `b ∈ {c,d}`. -/
theorem not_both_mem (q : QPair N) :
    ¬ ((q.1.1.1.1 = q.1.2.1.1 ∨ q.1.1.1.1 = q.1.2.1.2) ∧
       (q.1.1.1.2 = q.1.2.1.1 ∨ q.1.1.1.2 = q.1.2.1.2)) := by
  obtain ⟨⟨⟨⟨a, b⟩, hab⟩, ⟨⟨c, d⟩, hcd⟩⟩, hne⟩ := q
  simp only at hab hcd ⊢
  rintro ⟨h1 | h1, h2 | h2⟩
  · rw [h1, h2] at hab; exact lt_irrefl _ hab
  · subst h1 h2; exact hne rfl
  · rw [h1, h2] at hab; exact lt_asymm hab hcd
  · rw [h1, h2] at hab; exact lt_irrefl _ hab

omit [Fact (0 < L)] in
theorem surjective_piHom (q : QPair N) : Function.Surjective (piHom L q) := by
  intro z
  obtain ⟨⟨⟨⟨a, b⟩, hab⟩, ⟨⟨c, d⟩, hcd⟩⟩, hne⟩ := q
  have hnb := not_both_mem (⟨⟨⟨(a, b), hab⟩, ⟨(c, d), hcd⟩⟩, hne⟩ : QPair N)
  simp only at hnb hab hcd
  have hab' : a ≠ b := ne_of_lt hab
  have hcd' : c ≠ d := ne_of_lt hcd
  let y : Fin N → AddCircle L := fun m => if m = c then z 1 else 0
  have hyc : y c - y d = z 1 := by simp [y, hcd'.symm]
  have key : ∀ x : Fin N → AddCircle L, x a - x b = z 0 → x c - x d = z 1 →
      piHom L ⟨⟨⟨(a, b), hab⟩, ⟨(c, d), hcd⟩⟩, hne⟩ x = z := by
    intro x h0 h1
    funext k
    revert k
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simpa [piHom_apply] using h0
    · simpa [piHom_apply] using h1
  by_cases ha : a = c ∨ a = d
  · have hb : ¬ (b = c ∨ b = d) := fun hb => hnb ⟨ha, hb⟩
    simp only [not_or] at hb
    refine ⟨Function.update y b (y a - z 0), key _ ?_ ?_⟩
    · rw [Function.update_of_ne hab', Function.update_self]; abel
    · rw [Function.update_of_ne (Ne.symm hb.1), Function.update_of_ne (Ne.symm hb.2)]
      exact hyc
  · simp only [not_or] at ha
    refine ⟨Function.update y a (z 0 + y b), key _ ?_ ?_⟩
    · rw [Function.update_self, Function.update_of_ne (Ne.symm hab')]; abel
    · rw [Function.update_of_ne (Ne.symm ha.1), Function.update_of_ne (Ne.symm ha.2)]
      exact hyc

instance isAddHaarMeasure_map_piHom (q : QPair N) :
    (Measure.map (piHom L q) (torusPiMeasure L N)).IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_map_of_isFiniteMeasure (torusPiMeasure L N) (piHom L q)
    (continuous_piHom q) (surjective_piHom q)

/-- The pushforward scale `c_q` (Haar uniqueness on `𝕋_L^2`). -/
def cq (L : ℝ) [Fact (0 < L)] (q : QPair N) : ℝ≥0 :=
  (Measure.map (piHom L q) (torusPiMeasure L N)).addHaarScalarFactor (torusPiMeasure L 2)

/-- **Haar pushforward:** `μ_N(π_q⁻¹ S) = c_q · μ_2(S)`. -/
theorem measure_preimage_piHom (q : QPair N) {S : Set (Fin 2 → AddCircle L)}
    (hS : MeasurableSet S) :
    torusPiMeasure L N (piHom L q ⁻¹' S) = cq L q * torusPiMeasure L 2 S := by
  have h := Measure.isAddLeftInvariant_eq_smul (Measure.map (piHom L q) (torusPiMeasure L N))
    (torusPiMeasure L 2)
  rw [← Measure.map_apply (continuous_piHom q).measurable hS, h, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  rfl

/-! ## §2 The transverse profile `s(r) = sin²(πr/L)` -/

/-- `s(r) = sin²(πr/L)`: smooth, `L`-periodic, vanishing exactly on `Lℤ`. -/
def sfun (L : ℝ) (r : ℝ) : ℝ := Real.sin (Real.pi * r / L) ^ 2

omit [Fact (0 < L)] in
theorem sfun_nonneg (r : ℝ) : 0 ≤ sfun L r := sq_nonneg _

omit [Fact (0 < L)] in
theorem sfun_zero : sfun L 0 = 0 := by simp [sfun]

theorem sfun_periodic : Function.Periodic (sfun L) L := by
  intro r
  have hL : L ≠ 0 := (Fact.out : 0 < L).ne'
  unfold sfun
  rw [show Real.pi * (r + L) / L = Real.pi * r / L + Real.pi by field_simp, Real.sin_add_pi,
    neg_sq]

omit [Fact (0 < L)] in
theorem contDiff_sfun : ContDiff ℝ ∞ (sfun L) :=
  (Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const L)).pow 2

/-- `s` on the circle. -/
def sT (L : ℝ) [Fact (0 < L)] : AddCircle L → ℝ := (sfun_periodic (L := L)).lift

theorem sT_coe (r : ℝ) : sT L (r : AddCircle L) = sfun L r := rfl

theorem continuous_sT : Continuous (sT L) :=
  (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
    (contDiff_sfun.continuous)

/-- `A_t = {u ∈ 𝕋_L : s(u) ≤ t}`. -/
def Aset (L : ℝ) [Fact (0 < L)] (t : ℝ) : Set (AddCircle L) := {u | sT L u ≤ t}

theorem measurableSet_Aset (t : ℝ) : MeasurableSet (Aset L t) :=
  (isClosed_le continuous_sT continuous_const).measurableSet

/-- Jordan: for `|r| ≤ L/2`, `(2|r|/L)² ≤ s(r)`. -/
theorem jordan_sfun {r : ℝ} (hr : |r| ≤ L / 2) : (2 * |r| / L) ^ 2 ≤ sfun L r := by
  have hL : 0 < L := Fact.out
  have h0 : 0 ≤ Real.pi * |r| / L := by positivity
  have h1 : Real.pi * |r| / L ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hL two_pos]; nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin h0 h1
  have e1 : 2 / Real.pi * (Real.pi * |r| / L) = 2 * |r| / L := by
    field_simp
  rw [e1] at hs
  have e2 : sfun L r = Real.sin (Real.pi * |r| / L) ^ 2 := by
    unfold sfun
    rcases le_or_gt 0 r with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, show Real.pi * -r / L = -(Real.pi * r / L) by ring, Real.sin_neg, neg_sq]
  rw [e2]
  exact pow_le_pow_left₀ (by positivity) hs 2

/-- `vol(A_t) ≤ L√t`. -/
theorem volume_Aset_le (t : ℝ) :
    (volume : Measure (AddCircle L)) (Aset L t) ≤ ENNReal.ofReal (L * Real.sqrt t) := by
  have hL : 0 < L := Fact.out
  have hmp := AddCircle.measurePreserving_mk L (-(L / 2))
  rw [← hmp.measure_preimage (measurableSet_Aset t).nullMeasurableSet,
    Measure.restrict_apply ((measurableSet_Aset t).preimage AddCircle.measurable_mk')]
  have hsub : ((↑) : ℝ → AddCircle L) ⁻¹' Aset L t ∩ Set.Ioc (-(L / 2)) (-(L / 2) + L) ⊆
      Set.Icc (-(L * Real.sqrt t / 2)) (L * Real.sqrt t / 2) := by
    rintro r ⟨hA, hI⟩
    have hA' : sfun L r ≤ t := hA
    have hr : |r| ≤ L / 2 := abs_le.2 ⟨hI.1.le, by linarith [hI.2]⟩
    have hj := (jordan_sfun hr).trans hA'
    have hsq : 2 * |r| / L ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hj
    have : |r| ≤ L * Real.sqrt t / 2 := by
      rw [div_le_iff₀ hL] at hsq; linarith
    exact abs_le.1 this
  refine (measure_mono hsub).trans ?_
  rw [Real.volume_Icc]
  apply le_of_eq
  congr 1
  ring

/-! ## §3 `μ_N{y : s(y_a−y_b) ≤ t, s(y_c−y_d) ≤ t} ≤ c_q L² t` -/

/-- `B_q(t) = π_q⁻¹(A_t × A_t)`. -/
def Bset (L : ℝ) [Fact (0 < L)] (q : QPair N) (t : ℝ) : Set (Fin N → AddCircle L) :=
  piHom L q ⁻¹' Set.pi Set.univ fun _ => Aset L t

theorem measurableSet_Bset (q : QPair N) (t : ℝ) : MeasurableSet (Bset L q t) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Aset t).preimage (continuous_piHom q).measurable

theorem mem_Bset {q : QPair N} {t : ℝ} {y : Fin N → AddCircle L}
    (h1 : sT L (y q.1.1.1.1 - y q.1.1.1.2) ≤ t) (h2 : sT L (y q.1.2.1.1 - y q.1.2.1.2) ≤ t) :
    y ∈ Bset L q t := by
  intro k _
  show sT L (piHom L q y k) ≤ t
  rw [piHom_apply]
  split_ifs
  · exact h1
  · exact h2

theorem measure_Bset_le (q : QPair N) {t : ℝ} (ht : 0 ≤ t) :
    (torusPiMeasure L N (Bset L q t)).toReal ≤ (cq L q : ℝ) * (L ^ 2 * t) := by
  have hL : 0 < L := Fact.out
  rw [Bset, measure_preimage_piHom q (MeasurableSet.univ_pi fun _ => measurableSet_Aset t),
    Measure.pi_pi, Fin.prod_univ_two]
  have hA := volume_Aset_le (L := L) t
  have hb : (volume : Measure (AddCircle L)) (Aset L t) * volume (Aset L t) ≤
      ENNReal.ofReal (L ^ 2 * t) := by
    calc _ ≤ ENNReal.ofReal (L * Real.sqrt t) * ENNReal.ofReal (L * Real.sqrt t) :=
          mul_le_mul' hA hA
      _ = ENNReal.ofReal (L ^ 2 * t) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show L * Real.sqrt t * (L * Real.sqrt t) = L ^ 2 * (Real.sqrt t * Real.sqrt t) by ring,
            Real.mul_self_sqrt ht]
  rw [ENNReal.toReal_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc _ ≤ (ENNReal.ofReal (L ^ 2 * t)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    _ = L ^ 2 * t := ENNReal.toReal_ofReal (by positivity)

/-! ## §4 Cutoff profiles -/

/-- `χ(t) = 1 − smoothTransition(t − 1)`: equal to `1` for `t ≤ 1` and `0` for `t ≥ 2`. -/
def chiC (t : ℝ) : ℝ := 1 - Real.smoothTransition (t - 1)

theorem contDiff_chiC : ContDiff ℝ ∞ chiC :=
  contDiff_const.sub ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const))

theorem chiC_nonneg (t : ℝ) : 0 ≤ chiC t := by
  unfold chiC; linarith [Real.smoothTransition.le_one (t - 1)]

theorem chiC_le_one (t : ℝ) : chiC t ≤ 1 := by
  unfold chiC; linarith [Real.smoothTransition.nonneg (t - 1)]

theorem chiC_of_le_one {t : ℝ} (h : t ≤ 1) : chiC t = 1 := by
  unfold chiC; rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; ring

theorem chiC_of_two_le {t : ℝ} (h : 2 ≤ t) : chiC t = 0 := by
  unfold chiC; rw [Real.smoothTransition.one_of_one_le (by linarith)]; ring

theorem mem_of_deriv_chiC_ne {t : ℝ} (h : deriv chiC t ≠ 0) : 1 ≤ t ∧ t ≤ 2 := by
  by_contra hc
  rw [not_and_or, not_le, not_le] at hc
  apply h
  rcases hc with hc | hc
  · have e : chiC =ᶠ[nhds t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds hc] with r hr; exact chiC_of_le_one hr.le
    rw [e.deriv_eq]; simp
  · have e : chiC =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hc] with r hr; exact chiC_of_two_le hr.le
    rw [e.deriv_eq]; simp

theorem exists_bound_deriv_chiC : ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |deriv chiC t| ≤ K := by
  have h1 : ContDiff ℝ 1 chiC := contDiff_chiC.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (h1.continuous_deriv le_rfl).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : deriv chiC t = 0
  · rw [ht, abs_zero]; exact le_max_right _ _
  · have := hK t (mem_of_deriv_chiC_ne ht)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

theorem mem_of_deriv_Psi_ne {t : ℝ} (h : deriv Real.smoothTransition t ≠ 0) : 0 ≤ t ∧ t ≤ 1 := by
  by_contra hc
  rw [not_and_or, not_le, not_le] at hc
  apply h
  rcases hc with hc | hc
  · have e : Real.smoothTransition =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hc] with r hr
      exact Real.smoothTransition.zero_of_nonpos hr.le
    rw [e.deriv_eq]; simp
  · have e : Real.smoothTransition =ᶠ[nhds t] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds hc] with r hr
      exact Real.smoothTransition.one_of_one_le hr.le
    rw [e.deriv_eq]; simp

theorem exists_bound_deriv_Psi : ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |deriv Real.smoothTransition t| ≤ K := by
  have h1 : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff (n := 1)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (h1.continuous_deriv le_rfl).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : deriv Real.smoothTransition t = 0
  · rw [ht, abs_zero]; exact le_max_right _ _
  · have := hK t (mem_of_deriv_Psi_ne ht)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

theorem Psi_le {K : ℝ} (hK : ∀ t, |deriv Real.smoothTransition t| ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    Real.smoothTransition t ≤ K * t := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := Real.smoothTransition) (C := K)
    (fun x _ => ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero) x)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hK x) (Set.mem_univ 0) (Set.mem_univ t)
  rw [Real.smoothTransition.zero, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ht] at h
  exact (le_abs_self _).trans h

/-! ## §5 The cutoffs `η_M` -/

/-- `Q_q(x) = s(x_a − x_b) + s(x_c − x_d)` (vanishes exactly on the lifted `Σ_ab ∩ Σ_cd`). -/
def Qfun (L : ℝ) (q : QPair N) (x : Fin N → ℝ) : ℝ :=
  sfun L (x q.1.1.1.1 - x q.1.1.1.2) + sfun L (x q.1.2.1.1 - x q.1.2.1.2)

/-- Dyadic average `η_{q,M} = M⁻¹ Σ_{n<M} χ(4ⁿ Q_q)`. -/
def etaQ (L : ℝ) (M : ℕ) (q : QPair N) (x : Fin N → ℝ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ n ∈ Finset.range M, chiC (4 ^ n * Qfun L q x)

def etaS (L : ℝ) (M : ℕ) (x : Fin N → ℝ) : ℝ := ∑ q : QPair N, etaQ L M q x

/-- `η_M = Ψ(Σ_q η_{q,M})`, real-valued. -/
def etaR (L : ℝ) (M : ℕ) (x : Fin N → ℝ) : ℝ := Real.smoothTransition (etaS L M x)

/-- **The cutoff `η_M`** (as a complex-valued lattice-periodic function on `ℝ^N`). -/
def eta (L : ℝ) (M : ℕ) (x : Fin N → ℝ) : ℂ := (etaR (N := N) L M x : ℂ)

omit [Fact (0 < L)] in
theorem contDiff_Qfun (q : QPair N) : ContDiff ℝ ∞ (Qfun L q) :=
  (contDiff_sfun.comp ((contDiff_apply ℝ ℝ _).sub (contDiff_apply ℝ ℝ _))).add
    (contDiff_sfun.comp ((contDiff_apply ℝ ℝ _).sub (contDiff_apply ℝ ℝ _)))

omit [Fact (0 < L)] in
theorem contDiff_etaQ (M : ℕ) (q : QPair N) : ContDiff ℝ ∞ (etaQ L M q) :=
  contDiff_const.mul (ContDiff.sum fun _ _ => contDiff_chiC.comp
    (contDiff_const.mul (contDiff_Qfun q)))

omit [Fact (0 < L)] in
theorem contDiff_etaS (M : ℕ) : ContDiff ℝ ∞ (etaS (N := N) L M) :=
  ContDiff.sum fun q _ => contDiff_etaQ M q

omit [Fact (0 < L)] in
theorem contDiff_etaR (M : ℕ) : ContDiff ℝ ∞ (etaR (N := N) L M) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_etaS M)

omit [Fact (0 < L)] in
theorem contDiff_eta (M : ℕ) : ContDiff ℝ ∞ (eta (N := N) L M) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_etaR M)

theorem Qfun_periodic (q : QPair N) (x : Fin N → ℝ) (m : Fin N → ℤ) :
    Qfun L q (fun i => x i + m i * L) = Qfun L q x := by
  have h : ∀ i j : Fin N, sfun L ((x i + m i * L) - (x j + m j * L)) = sfun L (x i - x j) := by
    intro i j
    rw [show (x i + m i * L) - (x j + m j * L) = (x i - x j) + ((m i - m j : ℤ) : ℝ) * L by
      push_cast; ring]
    exact (sfun_periodic.int_mul (m i - m j)) (x i - x j)
  unfold Qfun
  rw [h, h]

theorem eta_isTest (M : ℕ) : IsTorusTest L (eta (N := N) L M) where
  smooth := contDiff_eta M
  periodic := by
    intro x m
    unfold eta etaR etaS etaQ
    simp_rw [Qfun_periodic]

omit [Fact (0 < L)] in
theorem etaQ_nonneg (M : ℕ) (q : QPair N) (x : Fin N → ℝ) : 0 ≤ etaQ L M q x :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => chiC_nonneg _)

omit [Fact (0 < L)] in
theorem etaR_nonneg (M : ℕ) (x : Fin N → ℝ) : 0 ≤ etaR L M x := Real.smoothTransition.nonneg _

omit [Fact (0 < L)] in
theorem etaR_le_one (M : ℕ) (x : Fin N → ℝ) : etaR L M x ≤ 1 := Real.smoothTransition.le_one _

omit [Fact (0 < L)] in
theorem etaS_nonneg (M : ℕ) (x : Fin N → ℝ) : 0 ≤ etaS L M x :=
  Finset.sum_nonneg fun q _ => etaQ_nonneg M q x

omit [Fact (0 < L)] in
/-- `η_{q,M} = 1` where `Q_q < 4^{-M}` (`M ≥ 1`). -/
theorem etaQ_eq_one {M : ℕ} (hM : 1 ≤ M) (q : QPair N) {x : Fin N → ℝ}
    (hx : Qfun L q x < ((4 : ℝ) ^ M)⁻¹) : etaQ L M q x = 1 := by
  have hQ : 0 ≤ Qfun L q x := add_nonneg (sfun_nonneg _) (sfun_nonneg _)
  unfold etaQ
  have h : ∀ n ∈ Finset.range M, chiC (4 ^ n * Qfun L q x) = 1 := by
    intro n hn
    apply chiC_of_le_one
    have h4 : (4 : ℝ) ^ n ≤ 4 ^ M :=
      pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hn).le
    calc (4 : ℝ) ^ n * Qfun L q x ≤ 4 ^ M * Qfun L q x :=
          mul_le_mul_of_nonneg_right h4 hQ
      _ ≤ 4 ^ M * ((4 : ℝ) ^ M)⁻¹ := mul_le_mul_of_nonneg_left hx.le (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast (show M ≠ 0 by omega))

/-- `Q_q` at torus representatives: `s(y_a − y_b) + s(y_c − y_d)` on `𝕋_L`. -/
def Qt (L : ℝ) [Fact (0 < L)] (q : QPair N) (y : Fin N → AddCircle L) : ℝ :=
  sT L (y q.1.1.1.1 - y q.1.1.1.2) + sT L (y q.1.2.1.1 - y q.1.2.1.2)

theorem continuous_Qt (q : QPair N) : Continuous (Qt L q) := by
  have h1 : Continuous fun y : Fin N → AddCircle L => sT L (y q.1.1.1.1 - y q.1.1.1.2) :=
    continuous_sT.comp ((continuous_apply q.1.1.1.1).sub (continuous_apply q.1.1.1.2))
  have h2 : Continuous fun y : Fin N → AddCircle L => sT L (y q.1.2.1.1 - y q.1.2.1.2) :=
    continuous_sT.comp ((continuous_apply q.1.2.1.1).sub (continuous_apply q.1.2.1.2))
  exact h1.add h2

theorem sfun_rep_sub (u v : AddCircle L) : sfun L (rep u - rep v) = sT L (u - v) := by
  rw [← sT_coe, AddCircle.coe_sub, coe_rep, coe_rep]

theorem Qfun_rep (q : QPair N) (y : Fin N → AddCircle L) :
    Qfun L q (fun i => rep (y i)) = Qt L q y := by
  unfold Qfun Qt
  rw [sfun_rep_sub, sfun_rep_sub]

/-- The open neighbourhood `U_M = ⋃_q {Q_q < 4^{-M}}` of `E`. -/
def Unbhd (L : ℝ) [Fact (0 < L)] (N M : ℕ) : Set (Fin N → AddCircle L) :=
  ⋃ q : QPair N, {y | Qt L q y < ((4 : ℝ) ^ M)⁻¹}

theorem isOpen_Unbhd (M : ℕ) : IsOpen (Unbhd L N M) :=
  isOpen_iUnion fun q => isOpen_lt (continuous_Qt q) continuous_const

theorem coincE_subset_Unbhd (M : ℕ) : coincE L N ⊆ Unbhd L N M := by
  intro y hy
  simp only [coincE, Set.mem_iUnion] at hy
  obtain ⟨p, p', hne, h1, h2⟩ := hy
  refine Set.mem_iUnion.2 ⟨⟨(p, p'), hne⟩, ?_⟩
  show Qt L ⟨(p, p'), hne⟩ y < ((4 : ℝ) ^ M)⁻¹
  have h1' : y p.1.1 - y p.1.2 = 0 := sub_eq_zero.2 h1
  have h2' : y p'.1.1 - y p'.1.2 = 0 := sub_eq_zero.2 h2
  have hz : sT L 0 = 0 := by
    rw [← AddCircle.coe_zero, sT_coe, sfun_zero]
  unfold Qt
  simp only
  rw [h1', h2', hz, add_zero]
  positivity

/-- `η_M ≡ 1` on `U_M` (`M ≥ 1`). -/
theorem liftK_eta_eq_one {M : ℕ} (hM : 1 ≤ M) {y : Fin N → AddCircle L} (hy : y ∈ Unbhd L N M) :
    liftK (L := L) (eta (N := N) L M) y = 1 := by
  obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hy
  have hq' : Qfun L q (fun i => rep (y i)) < ((4 : ℝ) ^ M)⁻¹ := by
    rw [Qfun_rep]; exact hq
  have h1 := etaQ_eq_one hM q hq'
  have hS : 1 ≤ etaS L M (fun i => rep (y i)) := by
    rw [← h1]
    exact Finset.single_le_sum (f := fun q => etaQ L M q (fun i => rep (y i)))
      (fun q _ => etaQ_nonneg M q _) (Finset.mem_univ q)
  show ((Real.smoothTransition (etaS L M (fun i => rep (y i))) : ℝ) : ℂ) = 1
  rw [Real.smoothTransition.one_of_one_le hS, Complex.ofReal_one]

/-! ## §6 Pointwise derivative bounds -/

/-- `s'(r) = 2 sin(πr/L) cos(πr/L) (π/L)`. -/
def sder (L : ℝ) (r : ℝ) : ℝ :=
  2 * Real.sin (Real.pi * r / L) * Real.cos (Real.pi * r / L) * (Real.pi / L)

omit [Fact (0 < L)] in
theorem hasDerivAt_sfun (r : ℝ) : HasDerivAt (sfun L) (sder L r) r := by
  have h := ((((hasDerivAt_id r).const_mul Real.pi).div_const L).sin).pow 2
  convert h using 1
  · funext x; simp [sfun, div_eq_mul_inv]
  · simp only [sder, id]
    norm_num
    ring

omit [Fact (0 < L)] in
theorem sder_sq_le (r : ℝ) : sder L r ^ 2 ≤ 4 * (Real.pi / L) ^ 2 * sfun L r := by
  unfold sder sfun
  have hc := Real.cos_sq_le_one (Real.pi * r / L)
  have hs := sq_nonneg (Real.sin (Real.pi * r / L))
  have hp := sq_nonneg (Real.pi / L)
  have e : (2 * Real.sin (Real.pi * r / L) * Real.cos (Real.pi * r / L) * (Real.pi / L)) ^ 2 =
      4 * (Real.pi / L) ^ 2 * Real.sin (Real.pi * r / L) ^ 2 * Real.cos (Real.pi * r / L) ^ 2 := by
    ring
  rw [e]
  have := mul_le_mul_of_nonneg_left hc (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hp) hs)
  linarith

/-- `ℓ_ij(x) = x_i − x_j`. -/
def ell (i j : Fin N) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j

theorem norm_ell_le (i j : Fin N) : ‖ell i j‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
  rw [Real.norm_eq_abs]
  show |x i - x j| ≤ 2 * ‖x‖
  have hi := norm_le_pi_norm x i
  have hj := norm_le_pi_norm x j
  rw [Real.norm_eq_abs] at hi hj
  calc |x i - x j| ≤ |x i| + |x j| := abs_sub _ _
    _ ≤ 2 * ‖x‖ := by linarith

theorem hasFDerivAt_ell (i j : Fin N) (x : Fin N → ℝ) :
    HasFDerivAt (fun x : Fin N → ℝ => x i - x j) (ell i j) x :=
  (hasFDerivAt_apply i x).sub (hasFDerivAt_apply j x)

/-- `DQ_q(x) = s'(x_a−x_b) ℓ_ab + s'(x_c−x_d) ℓ_cd`. -/
def DQ (L : ℝ) (q : QPair N) (x : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  sder L (x q.1.1.1.1 - x q.1.1.1.2) • ell q.1.1.1.1 q.1.1.1.2 +
    sder L (x q.1.2.1.1 - x q.1.2.1.2) • ell q.1.2.1.1 q.1.2.1.2

omit [Fact (0 < L)] in
theorem hasFDerivAt_Qfun (q : QPair N) (x : Fin N → ℝ) : HasFDerivAt (Qfun L q) (DQ L q x) x :=
  ((hasDerivAt_sfun _).comp_hasFDerivAt x (hasFDerivAt_ell _ _ x)).add
    ((hasDerivAt_sfun _).comp_hasFDerivAt x (hasFDerivAt_ell _ _ x))

omit [Fact (0 < L)] in
theorem norm_DQ_sq_le (q : QPair N) (x : Fin N → ℝ) :
    ‖DQ L q x‖ ^ 2 ≤ 32 * (Real.pi / L) ^ 2 * Qfun L q x := by
  set a := sder L (x q.1.1.1.1 - x q.1.1.1.2)
  set b := sder L (x q.1.2.1.1 - x q.1.2.1.2)
  have h1 : ‖DQ L q x‖ ≤ 2 * |a| + 2 * |b| := by
    unfold DQ
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := norm_ell_le q.1.1.1.1 q.1.1.1.2
    have := norm_ell_le q.1.2.1.1 q.1.2.1.2
    nlinarith [abs_nonneg a, abs_nonneg b]
  have ha := sder_sq_le (L := L) (x q.1.1.1.1 - x q.1.1.1.2)
  have hb := sder_sq_le (L := L) (x q.1.2.1.1 - x q.1.2.1.2)
  have h2 : ‖DQ L q x‖ ^ 2 ≤ (2 * |a| + 2 * |b|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (2 * |a| + 2 * |b|) ^ 2 ≤ 8 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  unfold Qfun
  nlinarith

/-- A finite sum with at most one nonzero term: `‖Σ g‖² ≤ Σ ‖g‖²`. -/
theorem norm_sum_sq_le_of_single {E : Type*} [NormedAddCommGroup E] (S : Finset ℕ) (g : ℕ → E)
    (h : ∀ n ∈ S, ∀ m ∈ S, g n ≠ 0 → g m ≠ 0 → n = m) :
    ‖∑ n ∈ S, g n‖ ^ 2 ≤ ∑ n ∈ S, ‖g n‖ ^ 2 := by
  by_cases hex : ∃ n ∈ S, g n ≠ 0
  · obtain ⟨n, hn, hgn⟩ := hex
    rw [Finset.sum_eq_single n (fun m hm hmn => by
      by_contra h'; exact hmn (h m hm n hn h' hgn)) (fun h' => absurd hn h')]
    exact Finset.single_le_sum (f := fun i => ‖g i‖ ^ 2) (fun i _ => sq_nonneg _) hn
  · simp only [not_exists, not_and, not_not] at hex
    rw [Finset.sum_eq_zero hex, norm_zero, sq, mul_zero]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Derivative of `η_{q,M}`. -/
def DetaQ (L : ℝ) (M : ℕ) (q : QPair N) (x : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  (M : ℝ)⁻¹ • ∑ n ∈ Finset.range M, deriv chiC (4 ^ n * Qfun L q x) • ((4 : ℝ) ^ n • DQ L q x)

theorem hasDerivAt_chiC (t : ℝ) : HasDerivAt chiC (deriv chiC t) t :=
  ((contDiff_chiC.differentiable (by simp)) t).hasDerivAt

omit [Fact (0 < L)] in
theorem hasFDerivAt_etaQ (M : ℕ) (q : QPair N) (x : Fin N → ℝ) :
    HasFDerivAt (etaQ L M q) (DetaQ L M q x) x := by
  unfold etaQ DetaQ
  refine HasFDerivAt.const_mul (HasFDerivAt.fun_sum fun n _ => ?_) _
  exact (hasDerivAt_chiC _).comp_hasFDerivAt x ((hasFDerivAt_Qfun q x).const_mul _)

omit [Fact (0 < L)] in
/-- `C₁ = 64 K_χ² (π/L)²`. -/
theorem norm_DetaQ_sq_le {Kc : ℝ} (hKc : ∀ t, |deriv chiC t| ≤ Kc) (M : ℕ) (q : QPair N)
    (x : Fin N → ℝ) :
    ‖DetaQ L M q x‖ ^ 2 ≤ ((M : ℝ)⁻¹) ^ 2 * ∑ n ∈ Finset.range M,
      64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n *
        (if 4 ^ n * Qfun L q x ≤ 2 then 1 else 0) := by
  set g : ℕ → (Fin N → ℝ) →L[ℝ] ℝ :=
    fun n => deriv chiC (4 ^ n * Qfun L q x) • ((4 : ℝ) ^ n • DQ L q x)
  have hQ : 0 ≤ Qfun L q x := add_nonneg (sfun_nonneg _) (sfun_nonneg _)
  have hdisj : ∀ n ∈ Finset.range M, ∀ m ∈ Finset.range M, g n ≠ 0 → g m ≠ 0 → n = m := by
    intro n _ m _ hn hm
    have hn' : deriv chiC (4 ^ n * Qfun L q x) ≠ 0 := fun h => hn (by simp [g, h])
    have hm' : deriv chiC (4 ^ m * Qfun L q x) ≠ 0 := fun h => hm (by simp [g, h])
    obtain ⟨hn1, hn2⟩ := mem_of_deriv_chiC_ne hn'
    obtain ⟨hm1, hm2⟩ := mem_of_deriv_chiC_ne hm'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (4 : ℝ) ^ m ≥ 4 * 4 ^ n := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hlt
      nlinarith
    · have : (4 : ℝ) ^ n ≥ 4 * 4 ^ m := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hlt
      nlinarith
  have hsum := norm_sum_sq_le_of_single _ g hdisj
  have hterm : ∀ n ∈ Finset.range M, ‖g n‖ ^ 2 ≤ 64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n *
      (if 4 ^ n * Qfun L q x ≤ 2 then 1 else 0) := by
    intro n _
    by_cases hd : deriv chiC (4 ^ n * Qfun L q x) = 0
    · have : g n = 0 := by simp [g, hd]
      rw [this, norm_zero]
      have : (0 : ℝ) ≤ 64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n *
          (if 4 ^ n * Qfun L q x ≤ 2 then 1 else 0) := by
        have : (0 : ℝ) ≤ if 4 ^ n * Qfun L q x ≤ 2 then 1 else 0 := by split_ifs <;> norm_num
        positivity
      simpa using this
    · obtain ⟨_, h2⟩ := mem_of_deriv_chiC_ne hd
      rw [ite_eq_left_iff.mpr (fun h => absurd h2 h), mul_one]
      have hgn : ‖g n‖ = |deriv chiC (4 ^ n * Qfun L q x)| * ((4 : ℝ) ^ n * ‖DQ L q x‖) := by
        simp only [g, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 4 ^ n)]
      have hK := hKc (4 ^ n * Qfun L q x)
      have hD := norm_DQ_sq_le (L := L) q x
      have h4 : (0 : ℝ) < 4 ^ n := by positivity
      have hQn : Qfun L q x ≤ 2 / 4 ^ n := by rw [le_div_iff₀ h4]; linarith
      rw [hgn, mul_pow, mul_pow]
      have hKsq : |deriv chiC (4 ^ n * Qfun L q x)| ^ 2 ≤ Kc ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hK 2
      have hD' : ‖DQ L q x‖ ^ 2 ≤ 32 * (Real.pi / L) ^ 2 * (2 / 4 ^ n) :=
        hD.trans (mul_le_mul_of_nonneg_left hQn (by positivity))
      calc |deriv chiC (4 ^ n * Qfun L q x)| ^ 2 * (((4 : ℝ) ^ n) ^ 2 * ‖DQ L q x‖ ^ 2)
          ≤ Kc ^ 2 * (((4 : ℝ) ^ n) ^ 2 * (32 * (Real.pi / L) ^ 2 * (2 / 4 ^ n))) :=
            mul_le_mul hKsq (mul_le_mul_of_nonneg_left hD' (by positivity)) (by positivity)
              (sq_nonneg _)
        _ = 64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n := by
            field_simp
            ring
  unfold DetaQ
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_left (hsum.trans (Finset.sum_le_sum hterm)) (sq_nonneg _)

/-- Derivative of `η_M`. -/
def DetaR (L : ℝ) (M : ℕ) (x : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  deriv Real.smoothTransition (etaS L M x) • ∑ q : QPair N, DetaQ L M q x

omit [Fact (0 < L)] in
theorem hasFDerivAt_etaR (M : ℕ) (x : Fin N → ℝ) : HasFDerivAt (etaR L M) (DetaR L M x) x := by
  have hS : HasFDerivAt (etaS (N := N) L M) (∑ q : QPair N, DetaQ L M q x) x :=
    HasFDerivAt.fun_sum fun q _ => hasFDerivAt_etaQ M q x
  exact (((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero)
    (etaS L M x)).hasDerivAt.comp_hasFDerivAt x hS

omit [Fact (0 < L)] in
theorem norm_DetaR_sq_le {Kp : ℝ} (hKp : ∀ t, |deriv Real.smoothTransition t| ≤ Kp)
    (M : ℕ) (x : Fin N → ℝ) :
    ‖DetaR L M x‖ ^ 2 ≤ Kp ^ 2 * (Fintype.card (QPair N) : ℝ) *
      ∑ q : QPair N, ‖DetaQ L M q x‖ ^ 2 := by
  unfold DetaR
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h1 : ‖∑ q : QPair N, DetaQ L M q x‖ ^ 2 ≤ (∑ q : QPair N, ‖DetaQ L M q x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (QPair N)))
    (f := fun q => ‖DetaQ L M q x‖)
  rw [Finset.card_univ] at h2
  have h3 : (deriv Real.smoothTransition (etaS L M x)) ^ 2 ≤ Kp ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hKp _) 2
  calc (deriv Real.smoothTransition (etaS L M x)) ^ 2 * ‖∑ q : QPair N, DetaQ L M q x‖ ^ 2
      ≤ Kp ^ 2 * ((Fintype.card (QPair N) : ℝ) * ∑ q : QPair N, ‖DetaQ L M q x‖ ^ 2) :=
        mul_le_mul h3 (h1.trans h2) (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

theorem norm_single_le (m : Fin N) : ‖(Pi.single m (1 : ℝ) : Fin N → ℝ)‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    by_cases h : i = m
    · subst h; simp
    · simp [h]

omit [Fact (0 < L)] in
/-- `∂_m η_M(x) = Dη_M(x) e_m`. -/
theorem pderiv_eta (M : ℕ) (m : Fin N) (x : Fin N → ℝ) :
    pderiv m (eta (N := N) L M) x = ((DetaR L M x (Pi.single m 1) : ℝ) : ℂ) := by
  unfold pderiv eta
  have h1 := (hasFDerivAt_etaR (L := L) M (Function.update x m (x m))).comp_hasDerivAt (x m)
    (hasDerivAt_update x m (x m))
  rw [Function.update_eq_self] at h1
  exact h1.ofReal_comp.deriv

omit [Fact (0 < L)] in
theorem norm_pderiv_eta_le (M : ℕ) (m : Fin N) (x : Fin N → ℝ) :
    ‖pderiv m (eta (N := N) L M) x‖ ≤ ‖DetaR L M x‖ := by
  rw [pderiv_eta, Complex.norm_real]
  calc ‖DetaR L M x (Pi.single m 1)‖ ≤ ‖DetaR L M x‖ * ‖(Pi.single m (1 : ℝ) : Fin N → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖DetaR L M x‖ * 1 := mul_le_mul_of_nonneg_left (norm_single_le m) (norm_nonneg _)
    _ = _ := mul_one _

/-! ## §7 The physical `H¹` norm of a smooth test, and `‖η_M‖_{H¹} → 0` -/

theorem norm_sq_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℂ) (hf.toLp f) (hf.toLp f)
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h
  have h2 : ∫ x, ⟪(hf.toLp f : α → ℂ) x, (hf.toLp f : α → ℂ) x⟫_ℂ ∂μ =
      ∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
  rw [h2, integral_complex_ofReal] at h
  have h3 : ((‖hf.toLp f‖ ^ 2 : ℝ) : ℂ) = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]; exact h
  exact Complex.ofReal_injective h3

/-- **Physical `H¹` norm of a smooth test** (frozen `PhysH1` norm, weak partials = classical):
`‖φ‖²_{H¹} = ∫|φ|² + Σ_m ∫|∂_mφ|²` over `𝕋_L^N`. -/
theorem norm_sq_smoothH1 {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    ‖CollisionIdentification.smoothH1 hφ‖ ^ 2 =
      ∫ y, ‖liftK (L := L) φ y‖ ^ 2 ∂(torusPiMeasure L N) +
        ∑ m, ∫ y, ‖liftK (L := L) (pderiv m φ) y‖ ^ 2 ∂(torusPiMeasure L N) := by
  rw [QuantumNLS.ProductWeakDerivatives.PhysH1.norm_sq_eq_weak
    (CollisionIdentification.smoothH1 hφ)
    (fun m => (memLp_liftK (continuous_pderiv hφ m)).toLp (liftK (L := L) (pderiv m φ)))
    (fun m => by
      rw [CollisionIdentification.smoothH1_val]
      exact CollisionIdentification.smooth_hasWeakPartial hφ m),
    CollisionIdentification.smoothH1_val, norm_sq_toLp]
  congr 1
  exact Finset.sum_congr rfl fun m _ => norm_sq_toLp _

theorem sT_nonneg (u : AddCircle L) : 0 ≤ sT L u := by
  rw [← coe_rep u, sT_coe]; exact sfun_nonneg _

/-- Indicator of the dyadic set `B_q(2·4^{-n})`. -/
def ind (L : ℝ) [Fact (0 < L)] (q : QPair N) (n : ℕ) (y : Fin N → AddCircle L) : ℝ :=
  (Bset L q (2 / 4 ^ n)).indicator (fun _ => (1 : ℝ)) y

theorem ind_nonneg (q : QPair N) (n : ℕ) (y : Fin N → AddCircle L) : 0 ≤ ind L q n y :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem integrable_ind (q : QPair N) (n : ℕ) : Integrable (ind L q n) (torusPiMeasure L N) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_Bset q _)

theorem integral_ind_le (q : QPair N) (n : ℕ) :
    ∫ y, ind L q n y ∂(torusPiMeasure L N) ≤ (cq L q : ℝ) * (L ^ 2 * (2 / 4 ^ n)) := by
  unfold ind
  rw [integral_indicator_const _ (measurableSet_Bset q _), smul_eq_mul, mul_one]
  exact measure_Bset_le q (by positivity)

theorem ite_le_ind (q : QPair N) (n : ℕ) (y : Fin N → AddCircle L) :
    (if 4 ^ n * Qfun L q (fun i => rep (y i)) ≤ 2 then (1 : ℝ) else 0) ≤ ind L q n y := by
  split_ifs with h
  · have h4 : (0 : ℝ) < 4 ^ n := by positivity
    have hQ : Qt L q y ≤ 2 / 4 ^ n := by
      rw [← Qfun_rep, le_div_iff₀ h4, mul_comm]; exact h
    have ha := sT_nonneg (L := L) (y q.1.1.1.1 - y q.1.1.1.2)
    have hb := sT_nonneg (L := L) (y q.1.2.1.1 - y q.1.2.1.2)
    unfold Qt at hQ
    have hm := mem_Bset (q := q) (t := 2 / 4 ^ n) (y := y) (by linarith) (by linarith)
    rw [ind, Set.indicator_of_mem hm]
  · exact ind_nonneg q n y

theorem chiC_le_ite (t : ℝ) : chiC t ≤ if t ≤ 2 then 1 else 0 := by
  split_ifs with h
  · exact chiC_le_one t
  · rw [chiC_of_two_le (not_le.1 h).le]

/-- Pointwise bound for `|η_M|²` on the torus. -/
theorem norm_sq_liftK_eta_le {Kp : ℝ} (hKp : ∀ t, |deriv Real.smoothTransition t| ≤ Kp)
    (M : ℕ) (y : Fin N → AddCircle L) :
    ‖liftK (L := L) (eta (N := N) L M) y‖ ^ 2 ≤
      ∑ q : QPair N, ∑ n ∈ Finset.range M, (Kp * (M : ℝ)⁻¹) * ind L q n y := by
  have hKp0 : 0 ≤ Kp := (abs_nonneg _).trans (hKp 0)
  set x : Fin N → ℝ := fun i => rep (y i) with hx
  have e : liftK (L := L) (eta (N := N) L M) y = (etaR L M x : ℂ) := rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (etaR_nonneg M x)]
  have h1 : etaR L M x ^ 2 ≤ etaR L M x := by nlinarith [etaR_nonneg (L := L) M x, etaR_le_one (L := L) M x]
  have h2 : etaR L M x ≤ Kp * etaS L M x := Psi_le hKp (etaS_nonneg M x)
  have h3 : etaS L M x ≤ ∑ q : QPair N, ∑ n ∈ Finset.range M, (M : ℝ)⁻¹ * ind L q n y := by
    unfold etaS
    refine Finset.sum_le_sum fun q _ => ?_
    unfold etaQ
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    exact mul_le_mul_of_nonneg_left ((chiC_le_ite _).trans (ite_le_ind q n y))
      (inv_nonneg.2 (Nat.cast_nonneg _))
  calc etaR L M x ^ 2 ≤ etaR L M x := h1
    _ ≤ Kp * etaS L M x := h2
    _ ≤ Kp * ∑ q : QPair N, ∑ n ∈ Finset.range M, (M : ℝ)⁻¹ * ind L q n y :=
        mul_le_mul_of_nonneg_left h3 hKp0
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring

/-- Pointwise bound for `|∂_m η_M|²` on the torus. -/
theorem norm_sq_liftK_pderiv_eta_le {Kc Kp : ℝ} (hKc : ∀ t, |deriv chiC t| ≤ Kc)
    (hKp : ∀ t, |deriv Real.smoothTransition t| ≤ Kp) (M : ℕ) (m : Fin N)
    (y : Fin N → AddCircle L) :
    ‖liftK (L := L) (pderiv m (eta (N := N) L M)) y‖ ^ 2 ≤
      ∑ q : QPair N, ∑ n ∈ Finset.range M,
        (Kp ^ 2 * (Fintype.card (QPair N) : ℝ) * ((M : ℝ)⁻¹) ^ 2 *
          (64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n)) * ind L q n y := by
  set x : Fin N → ℝ := fun i => rep (y i) with hx
  have e : liftK (L := L) (pderiv m (eta (N := N) L M)) y = pderiv m (eta (N := N) L M) x := rfl
  rw [e]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_pderiv_eta_le (L := L) M m x) 2
  have h2 := norm_DetaR_sq_le (L := L) hKp M x
  have h3 : ∀ q : QPair N, ‖DetaQ L M q x‖ ^ 2 ≤ ∑ n ∈ Finset.range M,
      (((M : ℝ)⁻¹) ^ 2 * (64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n)) * ind L q n y := by
    intro q
    refine (norm_DetaQ_sq_le hKc M q x).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have hi := ite_le_ind q n y
    have hpos : 0 ≤ ((M : ℝ)⁻¹) ^ 2 * (64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n) := by
      positivity
    calc ((M : ℝ)⁻¹) ^ 2 * (64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n *
          (if 4 ^ n * Qfun L q x ≤ 2 then 1 else 0))
        = (((M : ℝ)⁻¹) ^ 2 * (64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n)) *
          (if 4 ^ n * Qfun L q x ≤ 2 then 1 else 0) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hi hpos
  calc ‖pderiv m (eta (N := N) L M) x‖ ^ 2 ≤ ‖DetaR L M x‖ ^ 2 := h1
    _ ≤ Kp ^ 2 * (Fintype.card (QPair N) : ℝ) * ∑ q : QPair N, ‖DetaQ L M q x‖ ^ 2 := h2
    _ ≤ Kp ^ 2 * (Fintype.card (QPair N) : ℝ) * ∑ q : QPair N, ∑ n ∈ Finset.range M,
          (((M : ℝ)⁻¹) ^ 2 * (64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n)) * ind L q n y :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => h3 q) (by positivity)
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring

theorem integrable_weighted (a : ℕ → ℝ) (M : ℕ) :
    Integrable (fun y => ∑ q : QPair N, ∑ n ∈ Finset.range M, a n * ind L q n y)
      (torusPiMeasure L N) :=
  integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun n _ =>
    (integrable_ind q n).const_mul (a n)

theorem integral_weighted_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (M : ℕ) :
    ∫ y, ∑ q : QPair N, ∑ n ∈ Finset.range M, a n * ind L q n y ∂(torusPiMeasure L N) ≤
      ∑ q : QPair N, (cq L q : ℝ) * ∑ n ∈ Finset.range M, a n * (L ^ 2 * (2 / 4 ^ n)) := by
  rw [integral_finsetSum _ fun q _ => integrable_finsetSum _ fun n _ =>
    (integrable_ind q n).const_mul (a n)]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [integral_finsetSum _ fun n _ => (integrable_ind q n).const_mul (a n), Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [integral_const_mul]
  calc a n * ∫ y, ind L q n y ∂(torusPiMeasure L N)
      ≤ a n * ((cq L q : ℝ) * (L ^ 2 * (2 / 4 ^ n))) :=
        mul_le_mul_of_nonneg_left (integral_ind_le q n) (ha n)
    _ = _ := by ring

theorem sum_geom_le (M : ℕ) : ∑ n ∈ Finset.range M, (2 : ℝ) / 4 ^ n ≤ 4 := by
  have h : ∀ n ∈ Finset.range M, (2 : ℝ) / 4 ^ n ≤ 2 * (1 / 2) ^ n := by
    intro n _
    rw [div_le_iff₀ (by positivity), one_div, inv_pow, mul_assoc,
      show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
    rw [← mul_assoc ((2 : ℝ) ^ n)⁻¹, inv_mul_cancel₀ (by positivity), one_mul]
    nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n)]
  calc _ ≤ ∑ n ∈ Finset.range M, 2 * (1 / (2 : ℝ)) ^ n := Finset.sum_le_sum h
    _ = 2 * ∑ n ∈ Finset.range M, (1 / (2 : ℝ)) ^ n := by rw [Finset.mul_sum]
    _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le M) (by norm_num)
    _ = 4 := by norm_num

/-- Fixed derivative bounds for the profiles. -/
def Kc : ℝ := exists_bound_deriv_chiC.choose
def Kp : ℝ := exists_bound_deriv_Psi.choose

theorem Kc_nonneg : 0 ≤ Kc := exists_bound_deriv_chiC.choose_spec.1
theorem Kp_nonneg : 0 ≤ Kp := exists_bound_deriv_Psi.choose_spec.1
theorem hKc : ∀ t, |deriv chiC t| ≤ Kc := exists_bound_deriv_chiC.choose_spec.2
theorem hKp : ∀ t, |deriv Real.smoothTransition t| ≤ Kp := exists_bound_deriv_Psi.choose_spec.2

/-- The constant `D` in `‖η_M‖²_{H¹} ≤ D/M`. -/
def Dconst (L : ℝ) [Fact (0 < L)] (N : ℕ) : ℝ :=
  (Kp * 4 * L ^ 2 + (N : ℝ) * (Kp ^ 2 * (Fintype.card (QPair N) : ℝ) *
    (64 * Kc ^ 2 * (Real.pi / L) ^ 2) * L ^ 2 * 2)) * ∑ q : QPair N, (cq L q : ℝ)

theorem inv_sq_mul_self (M : ℕ) : ((M : ℝ)⁻¹) ^ 2 * M = (M : ℝ)⁻¹ := by
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; simp
  · have : (M : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

/-- **`‖η_M‖²_{H¹} ≤ D / M`** in the physical `PhysH1` norm. -/
theorem norm_sq_smoothH1_eta_le (M : ℕ) :
    ‖CollisionIdentification.smoothH1 (eta_isTest (L := L) (N := N) M)‖ ^ 2 ≤
      Dconst L N * (M : ℝ)⁻¹ := by
  rw [norm_sq_smoothH1]
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ q : QPair N, (cq L q : ℝ) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun q _ => NNReal.coe_nonneg _
  have hMinv : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  -- value part
  have hV : ∫ y, ‖liftK (L := L) (eta (N := N) L M) y‖ ^ 2 ∂(torusPiMeasure L N) ≤
      Kp * 4 * L ^ 2 * S * (M : ℝ)⁻¹ := by
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _)
      (integrable_weighted (fun _ => Kp * (M : ℝ)⁻¹) M)
      (Filter.Eventually.of_forall fun y => norm_sq_liftK_eta_le hKp M y)).trans ?_
    refine (integral_weighted_le (fun _ => Kp * (M : ℝ)⁻¹) (fun _ => mul_nonneg Kp_nonneg hMinv)
      M).trans ?_
    have hq : ∀ q : QPair N, (cq L q : ℝ) * ∑ n ∈ Finset.range M,
        Kp * (M : ℝ)⁻¹ * (L ^ 2 * (2 / 4 ^ n)) ≤ (cq L q : ℝ) * (Kp * 4 * L ^ 2 * (M : ℝ)⁻¹) := by
      intro q
      refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      have := sum_geom_le M
      have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
      calc Kp * (M : ℝ)⁻¹ * (L ^ 2 * ∑ n ∈ Finset.range M, (2 : ℝ) / 4 ^ n)
          ≤ Kp * (M : ℝ)⁻¹ * (L ^ 2 * 4) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hL2)
              (mul_nonneg Kp_nonneg hMinv)
        _ = _ := by ring
    calc _ ≤ ∑ q : QPair N, (cq L q : ℝ) * (Kp * 4 * L ^ 2 * (M : ℝ)⁻¹) :=
          Finset.sum_le_sum fun q _ => hq q
      _ = _ := by rw [← Finset.sum_mul, ← hS]; ring
  -- derivative part
  have hD : ∀ m : Fin N, ∫ y, ‖liftK (L := L) (pderiv m (eta (N := N) L M)) y‖ ^ 2
      ∂(torusPiMeasure L N) ≤ Kp ^ 2 * (Fintype.card (QPair N) : ℝ) *
        (64 * Kc ^ 2 * (Real.pi / L) ^ 2) * L ^ 2 * 2 * S * (M : ℝ)⁻¹ := by
    intro m
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Kp ^ 2 * (Fintype.card (QPair N) : ℝ) * ((M : ℝ)⁻¹) ^ 2 *
      (64 * Kc ^ 2 * (Real.pi / L) ^ 2) := ⟨_, rfl⟩
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    have hw : ∀ n, Kp ^ 2 * (Fintype.card (QPair N) : ℝ) * ((M : ℝ)⁻¹) ^ 2 *
        (64 * Kc ^ 2 * (Real.pi / L) ^ 2 * (4 : ℝ) ^ n) = B * 4 ^ n := fun n => by rw [hB]; ring
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _)
      (integrable_weighted (fun n => B * 4 ^ n) M)
      (Filter.Eventually.of_forall fun y => by
        have := norm_sq_liftK_pderiv_eta_le hKc hKp M m y
        simp only [hw] at this
        exact this)).trans ?_
    refine (integral_weighted_le (fun n => B * 4 ^ n) (fun n => mul_nonneg hB0 (by positivity))
      M).trans ?_
    have hterm : ∀ n ∈ Finset.range M, B * (4 : ℝ) ^ n * (L ^ 2 * (2 / 4 ^ n)) = B * L ^ 2 * 2 := by
      intro n _; field_simp
    have hsum : ∑ n ∈ Finset.range M, B * (4 : ℝ) ^ n * (L ^ 2 * (2 / 4 ^ n)) =
        B * L ^ 2 * 2 * M := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have hq : ∀ q : QPair N, (cq L q : ℝ) * ∑ n ∈ Finset.range M,
        B * 4 ^ n * (L ^ 2 * (2 / 4 ^ n)) = (cq L q : ℝ) * (B * L ^ 2 * 2 * M) := by
      intro q; rw [hsum]
    simp only [hsum]
    rw [← Finset.sum_mul, ← hS, hB]
    have hM := inv_sq_mul_self M
    apply le_of_eq
    calc S * (Kp ^ 2 * (Fintype.card (QPair N) : ℝ) * ((M : ℝ)⁻¹) ^ 2 *
          (64 * Kc ^ 2 * (Real.pi / L) ^ 2) * L ^ 2 * 2 * M)
        = Kp ^ 2 * (Fintype.card (QPair N) : ℝ) * (64 * Kc ^ 2 * (Real.pi / L) ^ 2) *
            L ^ 2 * 2 * S * (((M : ℝ)⁻¹) ^ 2 * M) := by ring
      _ = _ := by rw [hM]
  have hDsum := Finset.sum_le_sum fun m (_ : m ∈ Finset.univ) => hD m
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hDsum
  have key := add_le_add hV hDsum
  have e : Dconst L N * (M : ℝ)⁻¹ = Kp * 4 * L ^ 2 * S * (M : ℝ)⁻¹ +
      (N : ℝ) * (Kp ^ 2 * (Fintype.card (QPair N) : ℝ) * (64 * Kc ^ 2 * (Real.pi / L) ^ 2) *
        L ^ 2 * 2 * S * (M : ℝ)⁻¹) := by
    rw [hS]; unfold Dconst; ring
  rw [e]
  exact key

/-- **`‖η_M‖_{H¹} → 0`.** -/
theorem tendsto_norm_smoothH1_eta :
    Filter.Tendsto (fun M : ℕ => ‖CollisionIdentification.smoothH1 (eta_isTest (L := L) (N := N) M)‖)
      Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun M : ℕ => Real.sqrt (Dconst L N * (M : ℝ)⁻¹)) Filter.atTop
      (nhds 0) := by
    have h := ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (Dconst L N)).sqrt
    simpa using h
  refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_) hlim
  rw [← Real.sqrt_sq (norm_nonneg (CollisionIdentification.smoothH1
    (eta_isTest (L := L) (N := N) M)))]
  exact Real.sqrt_le_sqrt (norm_sq_smoothH1_eta_le M)

/-! ## §8 Consequence: no `H^{-1}` distribution supported on `E` -/

theorem integrable_norm_sq_liftK {Φ : (Fin N → ℝ) → ℂ} (hΦ : Continuous Φ) :
    Integrable (fun y => ‖liftK (L := L) Φ y‖ ^ 2) (torusPiMeasure L N) := by
  have h : MemLp (liftK (L := L) Φ) ((2 : ℕ) : ℝ≥0∞) (torusPiMeasure L N) := by
    norm_num; exact memLp_liftK hΦ
  exact h.integrable_norm_pow two_ne_zero

omit [Fact (0 < L)] in
theorem isTest_mul {f g : (Fin N → ℝ) → ℂ} (hf : IsTorusTest L f) (hg : IsTorusTest L g) :
    IsTorusTest L (fun x => f x * g x) where
  smooth := hf.smooth.mul hg.smooth
  periodic := fun x m => by simp only; rw [hf.periodic, hg.periodic]

omit [Fact (0 < L)] in
theorem isTest_one_sub_mul {f g : (Fin N → ℝ) → ℂ} (hf : IsTorusTest L f) (hg : IsTorusTest L g) :
    IsTorusTest L (fun x => (1 - f x) * g x) where
  smooth := (contDiff_const.sub hf.smooth).mul hg.smooth
  periodic := fun x m => by simp only; rw [hf.periodic, hg.periodic]

omit [Fact (0 < L)] in
/-- Product rule for the coordinate partial derivative. -/
theorem pderiv_mul {f g : (Fin N → ℝ) → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (m : Fin N) (x : Fin N → ℝ) :
    pderiv m (fun x => f x * g x) x = pderiv m f x * g x + f x * pderiv m g x := by
  have hf1 : HasDerivAt (fun t => f (Function.update x m t)) (fderiv ℝ f x (Pi.single m 1)) (x m) := by
    have h := (hf (Function.update x m (x m))).hasFDerivAt.comp_hasDerivAt (x m)
      (hasDerivAt_update x m (x m))
    rw [Function.update_eq_self] at h
    exact h
  have hg1 : HasDerivAt (fun t => g (Function.update x m t)) (fderiv ℝ g x (Pi.single m 1)) (x m) := by
    have h := (hg (Function.update x m (x m))).hasFDerivAt.comp_hasDerivAt (x m)
      (hasDerivAt_update x m (x m))
    rw [Function.update_eq_self] at h
    exact h
  unfold pderiv
  have h := (hf1.mul hg1).deriv
  show deriv (fun t => f (Function.update x m t) * g (Function.update x m t)) (x m) = _
  rw [show (fun t => f (Function.update x m t) * g (Function.update x m t)) =
      (fun t => f (Function.update x m t)) * (fun t => g (Function.update x m t)) from rfl, h,
    hf1.deriv, hg1.deriv]
  simp only [Function.update_eq_self]

/-- `φ ↦ smoothH1 φ` is additive. -/
theorem smoothH1_add {φ f g : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (hf : IsTorusTest L f)
    (hg : IsTorusTest L g) (h : ∀ x, φ x = f x + g x) :
    CollisionIdentification.smoothH1 hφ =
      CollisionIdentification.smoothH1 hf + CollisionIdentification.smoothH1 hg := by
  apply PhysH1.val_injective (L := L) (k := N)
  rw [show (CollisionIdentification.smoothH1 hf + CollisionIdentification.smoothH1 hg).val =
      (CollisionIdentification.smoothH1 hf).val + (CollisionIdentification.smoothH1 hg).val from
    map_add (PhysH1.valCLM (L := L) (k := N)) _ _]
  rw [CollisionIdentification.smoothH1_val, CollisionIdentification.smoothH1_val,
    CollisionIdentification.smoothH1_val]
  refine Lp.ext ?_
  filter_upwards [(memLp_liftK hφ.smooth.continuous).coeFn_toLp (μ := torusPiMeasure L N),
    (memLp_liftK hf.smooth.continuous).coeFn_toLp (μ := torusPiMeasure L N),
    (memLp_liftK hg.smooth.continuous).coeFn_toLp (μ := torusPiMeasure L N),
    Lp.coeFn_add ((memLp_liftK (L := L) hf.smooth.continuous).toLp (liftK (L := L) f))
      ((memLp_liftK (L := L) hg.smooth.continuous).toLp (liftK (L := L) g))] with y h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3]
  exact h _

/-- **Multiplication by a fixed smooth test is bounded on `H¹`:** `‖ηφ‖²_{H¹} ≤ C_φ ‖η‖²_{H¹}`. -/
theorem exists_mul_bound {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {η : (Fin N → ℝ) → ℂ} (hη : IsTorusTest L η),
      ‖CollisionIdentification.smoothH1 (isTest_mul hη hφ)‖ ^ 2 ≤
        C * ‖CollisionIdentification.smoothH1 hη‖ ^ 2 := by
  obtain ⟨B, hB⟩ := exists_bound_liftK (L := L) hφ.smooth.continuous
  choose C' hC' using fun m : Fin N => exists_bound_liftK (L := L) (continuous_pderiv hφ m)
  set B' : ℝ := ∑ m, |C' m|
  have hB' : ∀ m y, ‖liftK (L := L) (pderiv m φ) y‖ ≤ B' := fun m y =>
    (hC' m y).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun m => |C' m|) (fun _ _ => abs_nonneg _) (Finset.mem_univ m)))
  refine ⟨B ^ 2 + 2 * (N : ℝ) * B' ^ 2 + 2 * B ^ 2, by positivity, fun {η} hη => ?_⟩
  rw [norm_sq_smoothH1, norm_sq_smoothH1]
  have hBsq : ∀ y, ‖liftK (L := L) φ y‖ ^ 2 ≤ B ^ 2 := fun y =>
    pow_le_pow_left₀ (norm_nonneg _) (hB y) 2
  have hB'sq : ∀ m y, ‖liftK (L := L) (pderiv m φ) y‖ ^ 2 ≤ B' ^ 2 := fun m y =>
    pow_le_pow_left₀ (norm_nonneg _) (hB' m y) 2
  set V := ∫ y, ‖liftK (L := L) η y‖ ^ 2 ∂(torusPiMeasure L N)
  have hV0 : 0 ≤ V := integral_nonneg fun y => sq_nonneg _
  have hD0 : ∀ m : Fin N, 0 ≤ ∫ y, ‖liftK (L := L) (pderiv m η) y‖ ^ 2 ∂(torusPiMeasure L N) :=
    fun m => integral_nonneg fun y => sq_nonneg _
  have hIη := integrable_norm_sq_liftK (L := L) hη.smooth.continuous
  have hval : ∫ y, ‖liftK (L := L) (fun x => η x * φ x) y‖ ^ 2 ∂(torusPiMeasure L N) ≤ B ^ 2 * V := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (hIη.const_mul _) (Filter.Eventually.of_forall fun y => ?_)
    show ‖liftK (L := L) η y * liftK (L := L) φ y‖ ^ 2 ≤ B ^ 2 * ‖liftK (L := L) η y‖ ^ 2
    rw [norm_mul, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hBsq y) (sq_nonneg _)
  have hder : ∀ m : Fin N,
      ∫ y, ‖liftK (L := L) (pderiv m (fun x => η x * φ x)) y‖ ^ 2 ∂(torusPiMeasure L N) ≤
        2 * B ^ 2 * ∫ y, ‖liftK (L := L) (pderiv m η) y‖ ^ 2 ∂(torusPiMeasure L N) +
          2 * B' ^ 2 * V := by
    intro m
    have hIm := integrable_norm_sq_liftK (L := L) (continuous_pderiv hη m)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hIm.const_mul _)
      (hIη.const_mul _)]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      ((hIm.const_mul _).add (hIη.const_mul _)) (Filter.Eventually.of_forall fun y => ?_)
    have e : liftK (L := L) (pderiv m (fun x => η x * φ x)) y =
        liftK (L := L) (pderiv m η) y * liftK (L := L) φ y +
          liftK (L := L) η y * liftK (L := L) (pderiv m φ) y := by
      unfold liftK
      exact pderiv_mul (hη.smooth.differentiable (by simp)) (hφ.smooth.differentiable (by simp)) m _
    simp only
    rw [e]
    have h1 := norm_add_le (liftK (L := L) (pderiv m η) y * liftK (L := L) φ y)
      (liftK (L := L) η y * liftK (L := L) (pderiv m φ) y)
    rw [norm_mul, norm_mul] at h1
    have ha := hBsq y
    have hb := hB'sq m y
    set a := ‖liftK (L := L) (pderiv m η) y‖
    set b := ‖liftK (L := L) η y‖
    set c := ‖liftK (L := L) φ y‖
    set d := ‖liftK (L := L) (pderiv m φ) y‖
    have hsq : ‖liftK (L := L) (pderiv m η) y * liftK (L := L) φ y +
        liftK (L := L) η y * liftK (L := L) (pderiv m φ) y‖ ^ 2 ≤ (a * c + b * d) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2 : (a * c + b * d) ^ 2 ≤ 2 * (a ^ 2 * c ^ 2) + 2 * (b ^ 2 * d ^ 2) := by
      nlinarith [sq_nonneg (a * c - b * d)]
    have h3 : a ^ 2 * c ^ 2 ≤ a ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left ha (sq_nonneg _)
    have h4 : b ^ 2 * d ^ 2 ≤ b ^ 2 * B' ^ 2 := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    nlinarith
  have hsumD := Finset.sum_le_sum fun m (_ : m ∈ Finset.univ) => hder m
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsumD
  set DD := ∑ m : Fin N, ∫ y, ‖liftK (L := L) (pderiv m η) y‖ ^ 2 ∂(torusPiMeasure L N)
  have hDD0 : 0 ≤ DD := Finset.sum_nonneg fun m _ => hD0 m
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg _
  have hB'2 : 0 ≤ B' ^ 2 := sq_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc _ ≤ B ^ 2 * V + (2 * B ^ 2 * DD + (N : ℝ) * (2 * B' ^ 2 * V)) := add_le_add hval hsumD
    _ ≤ (B ^ 2 + 2 * (N : ℝ) * B' ^ 2 + 2 * B ^ 2) * (V + DD) := by
        nlinarith [mul_nonneg hB2 hV0, mul_nonneg hB2 hDD0, mul_nonneg (mul_nonneg hN hB'2) hDD0]

/-- **"Supported on `E`"**, stated literally for a continuous functional `R` on the physical `H¹`
(an `H^{-1}` distribution): `R` vanishes on every smooth test whose support is disjoint from `E`. -/
def SupportedOnE (R : PhysH1 L N →L[ℂ] ℂ) : Prop :=
  ∀ (φ : (Fin N → ℝ) → ℂ) (hφ : IsTorusTest L φ),
    Disjoint (tsupport (liftK (L := L) φ)) (coincE L N) →
      R (CollisionIdentification.smoothH1 hφ) = 0

/-- **R-08EE7BE5, part 1 (capacity cutoffs).** There are smooth lattice-periodic `η_M` with
`0 ≤ η_M ≤ 1`, `η_M ≡ 1` on an open neighbourhood of `E` (`M ≥ 1`), and `‖η_M‖_{H¹} → 0` in the
physical `PhysH1` norm. -/
theorem exists_capacity_cutoffs :
    ∃ (η : ℕ → (Fin N → ℝ) → ℂ) (hη : ∀ M, IsTorusTest L (η M)),
      (∀ M x, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ η M x = r) ∧
      (∀ M, 1 ≤ M → ∃ U : Set (Fin N → AddCircle L), IsOpen U ∧ coincE L N ⊆ U ∧
        ∀ y ∈ U, liftK (L := L) (η M) y = 1) ∧
      Filter.Tendsto (fun M => ‖CollisionIdentification.smoothH1 (hη M)‖) Filter.atTop (nhds 0) :=
  ⟨fun M => eta L M, fun M => eta_isTest M,
    fun M x => ⟨etaR L M x, etaR_nonneg M x, etaR_le_one M x, rfl⟩,
    fun M hM => ⟨Unbhd L N M, isOpen_Unbhd M, coincE_subset_Unbhd M,
      fun _ hy => liftK_eta_eq_one hM hy⟩,
    tendsto_norm_smoothH1_eta⟩

/-- A supported-on-`E` functional vanishes on every smooth test. -/
theorem apply_smoothH1_eq_zero {R : PhysH1 L N →L[ℂ] ℂ} (hR : SupportedOnE R)
    {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    R (CollisionIdentification.smoothH1 hφ) = 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_mul_bound hφ
  have hbound : ∀ M, 1 ≤ M → ‖R (CollisionIdentification.smoothH1 hφ)‖ ≤
      ‖R‖ * (Real.sqrt C * ‖CollisionIdentification.smoothH1 (eta_isTest (L := L) (N := N) M)‖) := by
    intro M hM
    have hη := eta_isTest (L := L) (N := N) M
    have hsplit := smoothH1_add hφ (isTest_mul hη hφ) (isTest_one_sub_mul hη hφ)
      (fun x => by ring)
    have hzero : R (CollisionIdentification.smoothH1 (isTest_one_sub_mul hη hφ)) = 0 := by
      apply hR
      have hsupp : Function.support (liftK (L := L) (fun x => (1 - eta L M x) * φ x)) ⊆
          (Unbhd L N M)ᶜ := by
        intro y hy hyU
        apply hy
        show (1 - liftK (L := L) (eta L M) y) * liftK (L := L) φ y = 0
        rw [liftK_eta_eq_one hM hyU, sub_self, zero_mul]
      have hts : tsupport (liftK (L := L) (fun x => (1 - eta L M x) * φ x)) ⊆ (Unbhd L N M)ᶜ :=
        closure_minimal hsupp (isOpen_Unbhd M).isClosed_compl
      exact Set.disjoint_of_subset_left hts
        (Set.disjoint_compl_left_iff_subset.2 (coincE_subset_Unbhd M))
    rw [hsplit, map_add, hzero, add_zero]
    refine (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have h := hC hη
    calc ‖CollisionIdentification.smoothH1 (isTest_mul hη hφ)‖
        = Real.sqrt (‖CollisionIdentification.smoothH1 (isTest_mul hη hφ)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (C * ‖CollisionIdentification.smoothH1 hη‖ ^ 2) := Real.sqrt_le_sqrt h
      _ = Real.sqrt C * ‖CollisionIdentification.smoothH1 hη‖ := by
          rw [Real.sqrt_mul hC0, Real.sqrt_sq (norm_nonneg _)]
  have hlim : Filter.Tendsto (fun M : ℕ => ‖R‖ * (Real.sqrt C *
      ‖CollisionIdentification.smoothH1 (eta_isTest (L := L) (N := N) M)‖)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_norm_smoothH1_eta (L := L) (N := N)).const_mul (Real.sqrt C)
      |>.const_mul ‖R‖
  have hle : ‖R (CollisionIdentification.smoothH1 hφ)‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun M hM => hbound M hM⟩)
  exact norm_le_zero_iff.1 hle

/-- **R-08EE7BE5, part 2.** A continuous linear functional on the physical `H¹(𝕋_L^N)` (an
`H^{-1}` distribution) supported on `E` is zero. -/
theorem eq_zero_of_supportedOnE {R : PhysH1 L N →L[ℂ] ℂ} (hR : SupportedOnE R) : R = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hlim := QuantumNLS.ContactDistribution.trigElem_cube_tendsto (L := L) x
  have htrig : ∀ r : ℕ, QuantumNLS.CollisionTrace.trigElem (L := L)
      (QuantumNLS.ContactOperator.cube N r) (QuantumNLS.CollisionTrace.coeffFun x) =
      CollisionIdentification.smoothH1 (QuantumNLS.ContactDistribution.trigTest_isTest (L := L)
        (QuantumNLS.ContactOperator.cube N r) (QuantumNLS.CollisionTrace.coeffFun x)) := by
    intro r
    apply PhysH1.val_injective (L := L) (k := N)
    rw [CollisionIdentification.smoothH1_val]
    exact (QuantumNLS.ContactDistribution.smoothClass_trigTest _ _).symm
  have h1 := (R.continuous.tendsto x).comp hlim
  have h2 : Filter.Tendsto (fun r : ℕ => R (QuantumNLS.CollisionTrace.trigElem (L := L)
      (QuantumNLS.ContactOperator.cube N r) (QuantumNLS.CollisionTrace.coeffFun x)))
      Filter.atTop (nhds 0) := by
    simp_rw [htrig, apply_smoothH1_eq_zero hR]
    exact tendsto_const_nhds
  simpa using tendsto_nhds_unique h1 h2

end QuantumNLS.CollisionCapacity

#print axioms QuantumNLS.CollisionCapacity.measure_preimage_piHom
#print axioms QuantumNLS.CollisionCapacity.measure_Bset_le
#print axioms QuantumNLS.CollisionCapacity.norm_sq_smoothH1
#print axioms QuantumNLS.CollisionCapacity.norm_sq_smoothH1_eta_le
#print axioms QuantumNLS.CollisionCapacity.tendsto_norm_smoothH1_eta
#print axioms QuantumNLS.CollisionCapacity.exists_capacity_cutoffs
#print axioms QuantumNLS.CollisionCapacity.exists_mul_bound
#print axioms QuantumNLS.CollisionCapacity.apply_smoothH1_eq_zero
#print axioms QuantumNLS.CollisionCapacity.eq_zero_of_supportedOnE
