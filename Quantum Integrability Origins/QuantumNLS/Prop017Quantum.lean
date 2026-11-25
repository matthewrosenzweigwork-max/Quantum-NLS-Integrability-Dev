import QuantumNLS.Prop017Bias
import QuantumNLS.PROP017UniformN

/-!
# PROP-017 physical assembly, step 2: the quantum hypotheses `Q7A:eq:tail` and `Q7A:eq:ms` for the actual Born law

Source: `source-text/chapters/propagation/window_reconstruction.tex:21-31` (model hypothesis 1).

Physical objects (all from accepted modules): the Born law `P_{N,u} = bornMeasure (physBasis L hκ N) u` of the actual physical Bethe
basis on the label space `MArr N`, and the measurable root vector `q_N(m) = arrRoots L (κ/N) m` (DEF-006 roots at coupling `κ/N`);
`μ` is the quantum-derived limiting rapidity measure `μ_{κ,u}` of R-09E1EAE9 (`IsLimitingRapidityMeasure`).

* `ms_actual` (**`Q7A:eq:ms`**): `E|G_N(x+iy) − G(x+iy)|² ≤ Csharp/(N y²)` for `y ≥ η₀ = max(4κ, L⁻¹ log 16)`, `N ≥ 1`
  (R-09E1EAE9 `concentration_sharp`, with `G = Gfull μ = g` by `cauchy_limiting_measure`).
* Stieltjes kernels `kern a t = a²/(t² + a²)` and `phi p t = Π_{k=1}^p t²/(t² + k²)`; `phi_inSpan`: `phi p` is a fixed linear combination
  of `1` and the kernels `kern k`, `1 ≤ k ≤ p` (partial fractions); `phi_le` (`phi ≤ t^{2p}`), `phi_ge` (`phi ≥ c_p > 0` for `|t| > 1`);
  `kern_im`: `kern a q = −a Im (ia − q)⁻¹`.
* `tail_actual` (**`Q7A:eq:tail`**): if `μ` has all even moments, then for every `p ≥ 1`, `R ≥ η₀`, `N ≥ 1`,
  `E[N⁻¹ #{j : |q_j| > R}] ≤ C_p R^{−2p} + D_p/(N R)` with constants `C_p = c_p⁻¹ ∫ x^{2p} dμ`, `D_p = c_p⁻¹ (Σ_k |c_{p,k}|/k) Cg κ`
  independent of `N` and `R`. Route: `1_{|t|>1} ≤ c_p⁻¹ phi_p(t)`; the Born mean of the kernel average is linear in the Born mean of
  `G_N(ikR)`, whose bias is `O(κ/(N (kR)²))` (`Prop017Bias.born_mean_G`); `∫ phi_p(q/R) dμ ≤ R^{−2p} ∫ q^{2p} dμ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop017Quantum

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.RootMeasureComplex (HighHalf)
open QuantumNLS.BetheCoefficientTransform (bornLaw)
open QuantumNLS.RootMeasureConcentration (gStar)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp concentration_sharp)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis empiricalProb IsLimitingRapidityMeasure)
open QuantumNLS.CauchyUniqueness (cauchyTransform)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (tailFraction)
open QuantumNLS.Prop017Bias (Cg born_mean_G)

/-! ## 1. The actual root vector -/

/-- The actual root vector on the label space: `q_N(m) = arrRoots L (κ/N) m`. -/
abbrev qAct (L κ : ℝ) (N : ℕ) (m : MArr N) : Fin N → ℝ := arrRoots L (κ / N) m

lemma measurable_qAct (L κ : ℝ) (N : ℕ) : Measurable (qAct L κ N) := measurable_of_countable _

/-- `η₀ = max(4κ, L⁻¹ log 16)`. -/
def eta0 (L κ : ℝ) : ℝ := max (4 * κ) (Real.log 16 / L)

lemma highHalf_of {L κ : ℝ} (hL : 0 < L) {z : ℂ} (hz : eta0 L κ ≤ z.im) : HighHalf L κ z := by
  refine ⟨le_trans (le_max_left _ _) hz, ?_⟩
  have := le_trans (le_max_right _ _) hz
  rw [div_le_iff₀ hL] at this; linarith

lemma eta0_pos {L κ : ℝ} (hκ : 0 < κ) : 0 < eta0 L κ := lt_of_lt_of_le (by linarith) (le_max_left _ _)

/-! ## 2. `Q7A:eq:ms` -/

section MS

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

lemma GN_eq (N : ℕ) (q : Fin N → ℝ) (z : ℂ) : GN q z = QuantumNLS.RootMeasureComplex.GN N q z := by
  unfold GN QuantumNLS.RootMeasureComplex.GN; simp [one_div]

lemma Gfull_eq (μ : Measure ℝ) (z : ℂ) : Gfull μ z = cauchyTransform μ z := by
  unfold Gfull cauchyTransform; simp [one_div]

/-- **`Q7A:eq:ms` for the actual Born law.** -/
theorem ms_actual (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {N : ℕ} (hN : 0 < N) (x y : ℝ)
    (hy : eta0 L κ ≤ y) :
    ∫ m, ‖Gfull (μ : Measure ℝ) ((x : ℂ) + (y : ℂ) * Complex.I) -
        GN (qAct L κ N m) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂(bornMeasure (physBasis L hκ N) u hu) ≤
      Csharp / ((N : ℝ) * y ^ 2) := by
  have hL : 0 < L := Fact.out
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hzdef
  have hzim : z.im = y := by simp [hzdef]
  have hz : HighHalf L κ z := highHalf_of hL (by rw [hzim]; exact hy)
  have hη : 0 < z.im := by rw [hzim]; linarith [eta0_pos (L := L) hκ]
  have h := concentration_sharp hκ hN u hu hz
  rw [hzim] at h
  refine le_trans (le_of_eq ?_) h
  refine integral_congr_ae (Eventually.of_forall fun m => ?_)
  show ‖Gfull (μ : Measure ℝ) z - GN (qAct L κ N m) z‖ ^ 2 = _
  beta_reduce
  rw [Gfull_eq, QuantumNLS.RootMeasureExistence.cauchy_limiting_measure hκ u hu hμ hz,
    QuantumNLS.RootMeasureExistence.cauchy_empirical hN m hη, GN_eq, norm_sub_rev]

end MS

/-! ## 3. Stieltjes kernels -/

/-- `kern a t = a²/(t² + a²)`. -/
def kern (a t : ℝ) : ℝ := a ^ 2 / (t ^ 2 + a ^ 2)

/-- `phi p t = Π_{k=1}^p (1 − kern k t) = Π_{k=1}^p t²/(t² + k²)`. -/
def phi (p : ℕ) (t : ℝ) : ℝ := ∏ k ∈ Finset.Icc 1 p, (1 - kern (k : ℝ) t)

lemma one_sub_kern {a : ℝ} (ha : 0 < a) (t : ℝ) : 1 - kern a t = t ^ 2 / (t ^ 2 + a ^ 2) := by
  unfold kern
  have : 0 < t ^ 2 + a ^ 2 := by positivity
  field_simp; ring

lemma kern_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (t : ℝ) :
    kern a t * kern b t = b ^ 2 / (b ^ 2 - a ^ 2) * kern a t - a ^ 2 / (b ^ 2 - a ^ 2) * kern b t := by
  have h3 : b ^ 2 - a ^ 2 ≠ 0 := by
    intro h
    apply hab
    have : (b - a) * (b + a) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith
  unfold kern
  have h1 : 0 < t ^ 2 + a ^ 2 := by positivity
  have h2 : 0 < t ^ 2 + b ^ 2 := by positivity
  field_simp
  ring

/-- `f` is a fixed combination of `1` and the kernels `kern k`, `1 ≤ k ≤ p`. -/
def InSpan (p : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ c0 : ℝ, ∃ c : ℕ → ℝ, ∀ t, f t = c0 + ∑ k ∈ Finset.Icc 1 p, c k * kern (k : ℝ) t

/-- **Partial fractions**: `phi p` is a fixed combination of `1` and the kernels. -/
theorem phi_inSpan (p : ℕ) : InSpan p (phi p) := by
  induction p with
  | zero => exact ⟨1, fun _ => 0, fun t => by simp [phi]⟩
  | succ p ih =>
    obtain ⟨c0, c, hc⟩ := ih
    set b : ℝ := ((p + 1 : ℕ) : ℝ) with hb
    have hb0 : 0 < b := by positivity
    set α : ℕ → ℝ := fun k => b ^ 2 / (b ^ 2 - (k : ℝ) ^ 2) with hα
    set β : ℕ → ℝ := fun k => (k : ℝ) ^ 2 / (b ^ 2 - (k : ℝ) ^ 2) with hβ
    refine ⟨c0, Function.update (fun k => c k * (1 - α k)) (p + 1)
      (-c0 + ∑ k ∈ Finset.Icc 1 p, c k * β k), fun t => ?_⟩
    have hphi : phi (p + 1) t = phi p t * (1 - kern b t) := by
      unfold phi; rw [Finset.prod_Icc_succ_top (by omega)]
    rw [hphi, hc t, Finset.sum_Icc_succ_top (by omega), Function.update_self]
    have hupd : ∑ k ∈ Finset.Icc 1 p, Function.update (fun k => c k * (1 - α k)) (p + 1)
        (-c0 + ∑ k ∈ Finset.Icc 1 p, c k * β k) k * kern (k : ℝ) t =
        ∑ k ∈ Finset.Icc 1 p, c k * (1 - α k) * kern (k : ℝ) t := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have : k ≠ p + 1 := by have := (Finset.mem_Icc.1 hk).2; omega
      rw [Function.update_of_ne this]
    rw [hupd]
    set S1 := ∑ k ∈ Finset.Icc 1 p, c k * kern (k : ℝ) t with hS1
    have e1 : S1 * kern b t = ∑ k ∈ Finset.Icc 1 p, c k * α k * kern (k : ℝ) t -
        (∑ k ∈ Finset.Icc 1 p, c k * β k) * kern b t := by
      rw [hS1, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 := (Finset.mem_Icc.1 hk).1
      have hk2 := (Finset.mem_Icc.1 hk).2
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hkb : (k : ℝ) ≠ b := by
        rw [hb]; intro h; have : k = p + 1 := by exact_mod_cast h
        omega
      rw [mul_assoc, kern_mul hkpos hb0 hkb t]
      simp only [hα, hβ]; ring
    have e2 : ∑ k ∈ Finset.Icc 1 p, c k * (1 - α k) * kern (k : ℝ) t =
        S1 - ∑ k ∈ Finset.Icc 1 p, c k * α k * kern (k : ℝ) t := by
      rw [hS1, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e2]
    linear_combination (-1 : ℝ) * e1

/-- The partial-fraction coefficients of `phi p` (fixed by choice). -/
def c0 (p : ℕ) : ℝ := Classical.choose (phi_inSpan p)
def cc (p : ℕ) : ℕ → ℝ := Classical.choose (Classical.choose_spec (phi_inSpan p))
lemma phi_eq (p : ℕ) (t : ℝ) : phi p t = c0 p + ∑ k ∈ Finset.Icc 1 p, cc p k * kern (k : ℝ) t :=
  Classical.choose_spec (Classical.choose_spec (phi_inSpan p)) t

lemma kern_nonneg {a : ℝ} (t : ℝ) : 0 ≤ kern a t := by unfold kern; positivity

lemma factor_mem {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    0 ≤ 1 - kern (k : ℝ) t ∧ 1 - kern (k : ℝ) t ≤ t ^ 2 := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [one_sub_kern (by linarith) t]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have h1 : 1 ≤ t ^ 2 + (k : ℝ) ^ 2 := by nlinarith [sq_nonneg t]
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg t)]

lemma prod_mono {s : Finset ℕ} {f g : ℕ → ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (h1 a (Finset.mem_insert_self a s))
      (ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi)) (fun i hi => h1 i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      ((h0 a (Finset.mem_insert_self a s)).trans (h1 a (Finset.mem_insert_self a s)))

lemma phi_nonneg (p : ℕ) (t : ℝ) : 0 ≤ phi p t :=
  Finset.prod_nonneg fun _ hk => (factor_mem (Finset.mem_Icc.1 hk).1 t).1

/-- `phi p t ≤ t^{2p}`. -/
lemma phi_le (p : ℕ) (t : ℝ) : phi p t ≤ t ^ (2 * p) := by
  unfold phi
  calc ∏ k ∈ Finset.Icc 1 p, (1 - kern (k : ℝ) t) ≤ ∏ _k ∈ Finset.Icc 1 p, t ^ 2 :=
        prod_mono (fun k hk => (factor_mem (Finset.mem_Icc.1 hk).1 t).1)
          (fun k hk => (factor_mem (Finset.mem_Icc.1 hk).1 t).2)
    _ = t ^ (2 * p) := by rw [Finset.prod_const, Nat.card_Icc, ← pow_mul, Nat.add_sub_cancel]

/-- `c_p = Π_{k=1}^p (1 + k²)⁻¹`. -/
def cp (p : ℕ) : ℝ := ∏ k ∈ Finset.Icc 1 p, (1 + (k : ℝ) ^ 2)⁻¹

lemma cp_pos (p : ℕ) : 0 < cp p := Finset.prod_pos fun k _ => by positivity

/-- `phi p t ≥ c_p` for `|t| > 1`. -/
lemma phi_ge (p : ℕ) {t : ℝ} (ht : 1 < |t|) : cp p ≤ phi p t := by
  unfold cp phi
  refine prod_mono (fun k _ => by positivity) fun k hk => ?_
  have hk1 := (Finset.mem_Icc.1 hk).1
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  rw [one_sub_kern (by linarith) t]
  have ht2 : 1 ≤ t ^ 2 := by
    have := sq_abs t; nlinarith [abs_nonneg t]
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (k : ℝ)]

/-- The kernel as an imaginary part of a Cauchy kernel: `kern a q = −a Im (ia − q)⁻¹`. -/
lemma kern_im {a : ℝ} (ha : 0 < a) (q : ℝ) :
    kern a q = -a * ((((a : ℂ) * Complex.I - (q : ℂ))⁻¹).im) := by
  rw [Complex.inv_im]
  have h1 : ((a : ℂ) * Complex.I - (q : ℂ)).im = a := by simp
  have h2 : Complex.normSq ((a : ℂ) * Complex.I - (q : ℂ)) = q ^ 2 + a ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [h1, h2]
  unfold kern
  have : 0 < q ^ 2 + a ^ 2 := by positivity
  field_simp

lemma kern_scale {k R : ℝ} (hk : 0 < k) (hR : 0 < R) (q : ℝ) :
    kern k (q / R) = kern (k * R) q := by
  unfold kern
  have : 0 < q ^ 2 + (k * R) ^ 2 := by positivity
  field_simp

/-! ## 4. `Q7A:eq:tail` -/

section Tail

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The constant `C_p = c_p⁻¹ ∫ x^{2p} dμ`. -/
def Ctail (μ : Measure ℝ) (p : ℕ) : ℝ := (cp p)⁻¹ * ∫ x, x ^ (2 * p) ∂μ

/-- The constant `D_p = c_p⁻¹ (Σ_k |c_{p,k}|/k) Cg κ`. -/
def Dtail (κ : ℝ) (p : ℕ) : ℝ := (cp p)⁻¹ * ((∑ k ∈ Finset.Icc 1 p, |cc p k| / k) * (Cg * κ))

/-- The pointwise kernel bound for one configuration. -/
lemma tail_pt {N : ℕ} (q : Fin N → ℝ) {R : ℝ} (hR : 0 < R) (p : ℕ) :
    (1 / (N : ℝ)) * ∑ j : Fin N, (if R < |q j| then (1 : ℝ) else 0) ≤
      (cp p)⁻¹ * ((1 / (N : ℝ)) * ∑ j : Fin N, phi p (q j / R)) := by
  rw [← mul_assoc, mul_comm (cp p)⁻¹, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with h
  · rw [le_inv_mul_iff₀ (cp_pos p), mul_one]
    refine phi_ge p ?_
    rw [abs_div, abs_of_pos hR, lt_div_iff₀ hR, one_mul]; exact h
  · exact mul_nonneg (inv_nonneg.2 (cp_pos p).le) (phi_nonneg p _)

/-- The kernel average of a configuration through its Cauchy transform. -/
lemma avg_kern {N : ℕ} (q : Fin N → ℝ) {a : ℝ} (ha : 0 < a) :
    (1 / (N : ℝ)) * ∑ j : Fin N, kern a (q j) =
      -a * (QuantumNLS.RootMeasureComplex.GN N q ((a : ℂ) * Complex.I)).im := by
  unfold QuantumNLS.RootMeasureComplex.GN
  rw [show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul, Complex.im_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [kern_im ha]; ring

/-- The kernel average of `phi p`. -/
lemma avg_phi {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) {R : ℝ} (hR : 0 < R) (p : ℕ) :
    (1 / (N : ℝ)) * ∑ j : Fin N, phi p (q j / R) = c0 p + ∑ k ∈ Finset.Icc 1 p, cc p k *
      (-((k : ℝ) * R) * (QuantumNLS.RootMeasureComplex.GN N q ((((k : ℝ) * R : ℝ) : ℂ) * Complex.I)).im) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∀ j, phi p (q j / R) = c0 p + ∑ k ∈ Finset.Icc 1 p, cc p k * kern (k : ℝ) (q j / R) :=
    fun j => phi_eq p _
  simp_rw [h1]
  rw [Finset.sum_add_distrib, mul_add]
  congr 1
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 / (N : ℝ)) (cc p k), mul_assoc]
    congr 1
    simp_rw [kern_scale hk0 hR]
    exact avg_kern q (by positivity)

/-- The kernel integral of `μ` through its Cauchy transform. -/
lemma int_kern (μ : Measure ℝ) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 < a) :
    ∫ q, kern a q ∂μ = -a * (cauchyTransform μ ((a : ℂ) * Complex.I)).im := by
  have hz : ((a : ℂ) * Complex.I).im ≠ 0 := by simp [ha.ne']
  have hint := QuantumNLS.EmpiricalRapidity.integrable_cauchyIntegrand μ _ hz
  have e : (cauchyTransform μ ((a : ℂ) * Complex.I)).im =
      ∫ q, ((((a : ℂ) * Complex.I - (q : ℂ))⁻¹)).im ∂μ := by
    unfold cauchyTransform
    exact (Complex.imCLM.integral_comp_comm hint).symm
  rw [e, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  exact kern_im ha q

lemma integrable_kern (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    Integrable (fun q => kern a q) μ := by
  refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun q => ?_)
  · unfold kern
    rcases eq_or_ne a 0 with h | h
    · subst h; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
      exact aestronglyMeasurable_const
    · exact (Continuous.div continuous_const (by fun_prop) (fun q => by positivity)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (kern_nonneg q)]
    unfold kern
    rcases eq_or_ne a 0 with h | h
    · subst h; simp
    · rw [div_le_one (by positivity)]; nlinarith [sq_nonneg q]

/-- **`Q7A:eq:tail` for the actual Born law**, assuming the even moments of `μ`. -/
theorem tail_actual (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ)
    (hmom : ∀ p : ℕ, Integrable (fun x : ℝ => x ^ (2 * p)) (μ : Measure ℝ))
    {N : ℕ} (hN : 0 < N) (p : ℕ) (R : ℝ) (hR : eta0 L κ ≤ R) :
    ∫ m, tailFraction (qAct L κ N) R m ∂(bornMeasure (physBasis L hκ N) u hu) ≤
      Ctail (μ : Measure ℝ) p * (1 / R ^ (2 * p)) + Dtail κ p / ((N : ℝ) * R) := by
  have hL : 0 < L := Fact.out
  have hRpos : 0 < R := lt_of_lt_of_le (eta0_pos hκ) hR
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [QuantumNLS.RootMeasureExistence.physBasis_eq hκ (by omega : 1 ≤ N)]
  set Ψ := QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ with hΨ
  set P := bornMeasure Ψ u hu with hP
  set pr : MArr N → ℝ := bornLaw Ψ u with hpr
  have hp0 : ∀ m, 0 ≤ pr m := fun m => QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _
  have hp1 : HasSum pr 1 := QuantumNLS.Prop017Bias.bornLaw_hasSum_one' hκ hN u hu
  -- the integral as a Born sum
  have hmu : ∀ m : MArr N, P.real {m} = pr m := by
    intro m
    rw [measureReal_def, QuantumNLS.EmpiricalRapidity.bornMeasure_singleton,
      ENNReal.toReal_ofReal (hp0 m)]
  have htf : ∀ m, tailFraction (qAct L κ N) R m =
      (1 / (N : ℝ)) * ∑ j : Fin N, (if R < |qAct L κ N m j| then (1 : ℝ) else 0) := by
    intro m; unfold tailFraction
    congr 1
  have htb : ∀ m, |tailFraction (qAct L κ N) R m| ≤ 1 := by
    intro m
    rw [htf m, abs_of_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num))]
    calc (1 / (N : ℝ)) * ∑ j : Fin N, (if R < |qAct L κ N m j| then (1 : ℝ) else 0)
        ≤ (1 / (N : ℝ)) * ∑ _j : Fin N, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => by split_ifs <;> norm_num) (by positivity)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_div,
            inv_mul_cancel₀ hNr.ne']
  have hint : Integrable (fun m => tailFraction (qAct L κ N) R m) P :=
    Integrable.of_bound (C := 1) Measurable.of_discrete.aestronglyMeasurable
      (Eventually.of_forall fun m => by rw [Real.norm_eq_abs]; exact htb m)
  rw [integral_countable hint]
  simp_rw [hmu, smul_eq_mul]
  -- the kernel average
  set Φ : MArr N → ℝ := fun m => (1 / (N : ℝ)) * ∑ j : Fin N, phi p (qAct L κ N m j / R) with hΦ
  have hΦeq : ∀ m, Φ m = c0 p + ∑ k ∈ Finset.Icc 1 p, cc p k *
      (-((k : ℝ) * R) * (QuantumNLS.RootMeasureComplex.GN N (qAct L κ N m)
        ((((k : ℝ) * R : ℝ) : ℂ) * Complex.I)).im) := fun m => avg_phi hN _ hRpos p
  -- Born means of the Cauchy transforms at `ikR`
  have hzk : ∀ k ∈ Finset.Icc 1 p, HighHalf L κ ((((k : ℝ) * R : ℝ) : ℂ) * Complex.I) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    refine highHalf_of hL ?_
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
      mul_zero, mul_one]
    nlinarith
  have hEG : ∀ k, ∃ EG : ℂ, k ∈ Finset.Icc 1 p → HasSum (fun m : MArr N => (pr m : ℂ) *
      QuantumNLS.RootMeasureComplex.GN N (qAct L κ N m) ((((k : ℝ) * R : ℝ) : ℂ) * Complex.I)) EG ∧
      ‖EG - gStar L κ hκ u hu ((((k : ℝ) * R : ℝ) : ℂ) * Complex.I)‖ ≤
        Cg * κ / (N * ((((k : ℝ) * R : ℝ) : ℂ) * Complex.I).im ^ 2) := by
    intro k
    by_cases hk : k ∈ Finset.Icc 1 p
    · obtain ⟨EG, h1, h2⟩ := born_mean_G hκ hN u hu (hzk k hk)
      exact ⟨EG, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose EG hEGs using hEG
  have hΦsum : HasSum (fun m => pr m * Φ m) (c0 p + ∑ k ∈ Finset.Icc 1 p, cc p k *
      (-((k : ℝ) * R) * (EG k).im)) := by
    have h1 := hp1.mul_right (c0 p)
    have h2 := hasSum_sum (s := Finset.Icc 1 p) fun k hk =>
      ((Complex.hasSum_im (hEGs k hk).1).mul_left (cc p k * (-((k : ℝ) * R))))
    have h3 := h1.add h2
    rw [one_mul] at h3
    have e : ∑ k ∈ Finset.Icc 1 p, cc p k * (-((k : ℝ) * R)) * (EG k).im =
        ∑ k ∈ Finset.Icc 1 p, cc p k * (-((k : ℝ) * R) * (EG k).im) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e] at h3
    refine h3.congr_fun fun m => ?_
    rw [hΦeq m]
    simp only [Complex.im_ofReal_mul]
    rw [mul_add, Finset.mul_sum]
    exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun k _ => by ring)
  -- the μ-side
  have hμint : ∫ q, phi p (q / R) ∂(μ : Measure ℝ) = c0 p + ∑ k ∈ Finset.Icc 1 p, cc p k *
      (-((k : ℝ) * R) * (gStar L κ hκ u hu ((((k : ℝ) * R : ℝ) : ℂ) * Complex.I)).im) := by
    have hφ : (fun q => phi p (q / R)) = fun q => c0 p + ∑ k ∈ Finset.Icc 1 p, cc p k * kern ((k : ℝ) * R) q := by
      funext q
      rw [phi_eq p]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
      rw [kern_scale hk0 hRpos]
    rw [hφ, integral_add (integrable_const _) (integrable_finsetSum _ fun k _ =>
      (integrable_kern _ _).const_mul _), integral_finsetSum _ (fun k _ => (integrable_kern _ _).const_mul _)]
    have hc : ∫ _q, c0 p ∂(μ : Measure ℝ) = c0 p := by simp
    rw [hc]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    rw [integral_const_mul, int_kern _ (mul_pos hk0 hRpos),
      QuantumNLS.RootMeasureExistence.cauchy_limiting_measure hκ u hu hμ (hzk k hk)]
  have hμle : ∫ q, phi p (q / R) ∂(μ : Measure ℝ) ≤ (∫ x, x ^ (2 * p) ∂(μ : Measure ℝ)) * (1 / R ^ (2 * p)) := by
    rw [← integral_mul_const]
    refine integral_mono_of_nonneg (Eventually.of_forall fun q => phi_nonneg p _)
      ((hmom p).mul_const _) (Eventually.of_forall fun q => ?_)
    refine (phi_le p _).trans (le_of_eq ?_)
    rw [div_pow, div_eq_mul_one_div]
  -- the comparison
  have hCg0 : 0 ≤ Cg * κ := by
    have h1 := QuantumNLS.Prop017Bias.Cb_nonneg
    have h2 : 0 ≤ Csharp := by
      unfold Csharp
      have := QuantumNLS.RootMeasureConcentrationSharp.Kc_nonneg
      linarith
    have h3 : 0 ≤ Cg := by unfold Cg; nlinarith
    exact mul_nonneg h3 hκ.le
  have hdiff : c0 p + ∑ k ∈ Finset.Icc 1 p, cc p k * (-((k : ℝ) * R) * (EG k).im) ≤
      ∫ q, phi p (q / R) ∂(μ : Measure ℝ) +
        (∑ k ∈ Finset.Icc 1 p, |cc p k| / k) * (Cg * κ) / ((N : ℝ) * R) := by
    rw [hμint, add_assoc]
    refine add_le_add le_rfl ?_
    rw [← sub_le_iff_le_add', ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    have hk0 : (0 : ℝ) < k := by linarith
    have hb := (hEGs k hk).2
    have him : ((((k : ℝ) * R : ℝ) : ℂ) * Complex.I).im = (k : ℝ) * R := by simp
    rw [him] at hb
    set gk := gStar L κ hκ u hu ((((k : ℝ) * R : ℝ) : ℂ) * Complex.I) with hgk
    have e : cc p k * (-((k : ℝ) * R) * (EG k).im) - cc p k * (-((k : ℝ) * R) * gk.im) =
        -(cc p k * ((k : ℝ) * R)) * (EG k - gk).im := by
      rw [Complex.sub_im]; ring
    rw [e]
    have hkR : 0 < (k : ℝ) * R := mul_pos hk0 hRpos
    have habs : |-(cc p k * ((k : ℝ) * R)) * (EG k - gk).im| =
        |cc p k| * ((k : ℝ) * R) * |(EG k - gk).im| := by
      rw [abs_mul, abs_neg, abs_mul, abs_of_pos hkR]
    calc -(cc p k * ((k : ℝ) * R)) * (EG k - gk).im
        ≤ |-(cc p k * ((k : ℝ) * R)) * (EG k - gk).im| := le_abs_self _
      _ = |cc p k| * ((k : ℝ) * R) * |(EG k - gk).im| := habs
      _ ≤ |cc p k| * ((k : ℝ) * R) * ‖EG k - gk‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (mul_nonneg (abs_nonneg _) hkR.le)
      _ ≤ |cc p k| * ((k : ℝ) * R) * (Cg * κ / (N * ((k : ℝ) * R) ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) hkR.le)
      _ = |cc p k| / k * (Cg * κ) / ((N : ℝ) * R) := by
          have := hNr.ne'; have := hRpos.ne'; have := hk0.ne'
          field_simp
  -- assemble
  have hsumle : ∑' m, pr m * tailFraction (qAct L κ N) R m ≤ (cp p)⁻¹ * ∑' m, pr m * Φ m := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun m => ?_) ?_ ?_
    · rw [htf m]
      calc pr m * ((1 / (N : ℝ)) * ∑ j : Fin N, (if R < |qAct L κ N m j| then (1 : ℝ) else 0))
          ≤ pr m * ((cp p)⁻¹ * Φ m) := mul_le_mul_of_nonneg_left (tail_pt _ hRpos p) (hp0 m)
        _ = (cp p)⁻¹ * (pr m * Φ m) := by ring
    · refine Summable.of_norm_bounded hp1.summable fun m => ?_
      rw [norm_mul, Real.norm_of_nonneg (hp0 m), Real.norm_eq_abs]
      exact mul_le_of_le_one_right (hp0 m) (htb m)
    · exact hΦsum.summable.mul_left _
  rw [hΦsum.tsum_eq] at hsumle
  refine hsumle.trans ?_
  have hcpi : 0 ≤ (cp p)⁻¹ := inv_nonneg.2 (cp_pos p).le
  calc (cp p)⁻¹ * (c0 p + ∑ k ∈ Finset.Icc 1 p, cc p k * (-((k : ℝ) * R) * (EG k).im))
      ≤ (cp p)⁻¹ * ((∫ x, x ^ (2 * p) ∂(μ : Measure ℝ)) * (1 / R ^ (2 * p)) +
          (∑ k ∈ Finset.Icc 1 p, |cc p k| / k) * (Cg * κ) / ((N : ℝ) * R)) :=
        mul_le_mul_of_nonneg_left (hdiff.trans (by linarith [hμle])) hcpi
    _ = _ := by unfold Ctail Dtail; ring

end Tail

end QuantumNLS.Prop017Quantum

#print axioms QuantumNLS.Prop017Quantum.ms_actual
#print axioms QuantumNLS.Prop017Quantum.phi_inSpan
#print axioms QuantumNLS.Prop017Quantum.tail_actual
