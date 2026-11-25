import QuantumNLS.DuhamelL4Limit

/-!
# EXT-003, Route Y stage (iv): the local `L⁴` contraction for the cubic Duhamel equation

The quoted input (`ROOT_L2_extension.tex`, lines 3-18): *for each bound `R` on the initial `L²` norm
there are `τ_R > 0`, `B_R < ∞`, `A_R < ∞` such that the cubic Duhamel equation has a unique local
solution in the `L⁴` space-time class with norm at most `B_R`, and its solution map is
`A_R`-Lipschitz from the initial `L²` ball into that class*, for any `L > 0` and coefficient `2κ`.

Route Y deviates from Bourgain's `X^{0,b}` proof (Bourgain 1993, §4): the linear inputs are the
elementary free estimate (LS1/LS2), the duality Duhamel map (DD1), the short-time gain `T^{1/16}`
(SG1) and the step-function Christ–Kiselev retarded estimate (DL4a/DL4b), all imported read-only.

Here:
* the Hölder estimate `‖|u|²u − |v|²v‖_{4/3} ≤ (‖u‖₄² + ‖u‖₄‖v‖₄ + ‖v‖₄²)‖u − v‖₄`;
* linearity of the Duhamel maps `V` and `Vst` in the forcing;
* the literal Duhamel predicate `u(t) = U(t−a)f + c ∫_a^t U(t−s)(|u|²u)(s) ds` (a.e. `t`, as `L²`
  slices; the integral is DD1's duality integral, which agrees with the ordinary integral whenever
  that is defined, DDL1), and its equivalence with the fixed-point equation in `L⁴(J × 𝕋_L)`;
* the contraction on the ball of radius `B_R = 2 C_L R`, on every interval `J = (α, β]` of length
  at most `τ_R`, giving existence, uniqueness in the ball and the Lipschitz bound with
  `A_R = 2 C_L`; also the continuous `L²` representative and its stability bound
  `(1 + 3 |c| C_L B_R² A_R) ‖f − g‖₂` (`= 1 + 6κ C_L B_R² A_R` for `c = −2iκ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.LocalWellPosedness QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.ShortTimeGain QuantumNLS.DuhamelL4
  QuantumNLS.DuhamelL4Limit

namespace QuantumNLS.LocalL4Contraction

attribute [local irreducible] QuantumNLS.L4StrichartzL2.evol

/-! ## 1. The cubic nonlinearity and Hölder's inequality -/

instance holder442 : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp)]
  simp; norm_num⟩

instance holder2443 : ENNReal.HolderTriple 2 4 (4 / 3) := ⟨by
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp)]
  simp [ENNReal.toReal_div]; norm_num⟩

section Cubic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Hölder for three factors: `‖a b d‖_{4/3} ≤ ‖a‖₄ ‖b‖₄ ‖d‖₄`. -/
lemma holder3 {a b d : X → ℝ} (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hd : AEStronglyMeasurable d μ) :
    eLpNorm (fun x => a x * b x * d x) (4 / 3) μ ≤ eLpNorm a 4 μ * eLpNorm b 4 μ * eLpNorm d 4 μ := by
  have e1 : (fun x => a x * b x * d x) = (a * b) • d := by funext x; simp [smul_eq_mul]
  have e2 : a * b = a • b := by funext x; simp [smul_eq_mul]
  rw [e1]
  refine (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 4) (ha.mul hb) hd).trans ?_
  gcongr
  rw [e2]
  exact eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) ha hb

/-- Pointwise: `||z|²z − |w|²w| ≤ (|z|² + |z||w| + |w|²)|z − w|`. -/
lemma cub_pt (z w : ℂ) :
    ‖((‖z‖ ^ 2 : ℝ) : ℂ) * z - ((‖w‖ ^ 2 : ℝ) : ℂ) * w‖ ≤
      (‖z‖ * ‖z‖ + ‖z‖ * ‖w‖ + ‖w‖ * ‖w‖) * ‖z - w‖ := by
  have e : ((‖z‖ ^ 2 : ℝ) : ℂ) * z - ((‖w‖ ^ 2 : ℝ) : ℂ) * w =
      ((‖z‖ ^ 2 : ℝ) : ℂ) * (z - w) + ((‖z‖ ^ 2 - ‖w‖ ^ 2 : ℝ) : ℂ) * w := by
    push_cast; ring
  have hd : |‖z‖ - ‖w‖| ≤ ‖z - w‖ := abs_norm_sub_norm_le z w
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have h2 : |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ (‖z‖ + ‖w‖) * ‖z - w‖ := by
    rw [show ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ + ‖w‖) * (‖z‖ - ‖w‖) by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖z‖ ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_right h2 hw, norm_nonneg (z - w)]

lemma cub_pt0 (z : ℂ) : ‖((‖z‖ ^ 2 : ℝ) : ℂ) * z‖ = ‖z‖ * ‖z‖ * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring

/-- The cubic nonlinearity `|u|²u`. -/
def cubF (u : X → ℂ) : X → ℂ := fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ) * u x

lemma continuous_cubic : Continuous fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ) * z := by fun_prop

lemma aesm_cubF {u : X → ℂ} (hu : AEStronglyMeasurable u μ) : AEStronglyMeasurable (cubF u) μ :=
  continuous_cubic.comp_aestronglyMeasurable hu

lemma eLpNorm_cubF_le {u : X → ℂ} (hu : AEStronglyMeasurable u μ) :
    eLpNorm (cubF u) (4 / 3) μ ≤ eLpNorm u 4 μ * eLpNorm u 4 μ * eLpNorm u 4 μ := by
  have hn : AEStronglyMeasurable (fun x => ‖u x‖) μ := hu.norm
  refine (eLpNorm_mono_real (aesm_cubF hu) (g := fun x => ‖u x‖ * ‖u x‖ * ‖u x‖)
    fun x => (cub_pt0 (u x)).le).trans ?_
  refine (holder3 hn hn hn).trans ?_
  rw [eLpNorm_norm u hu]

lemma eLpNorm_cubF_sub_le {u v : X → ℂ} (hu : AEStronglyMeasurable u μ)
    (hv : AEStronglyMeasurable v μ) :
    eLpNorm (cubF u - cubF v) (4 / 3) μ ≤
      (eLpNorm u 4 μ * eLpNorm u 4 μ + eLpNorm u 4 μ * eLpNorm v 4 μ +
        eLpNorm v 4 μ * eLpNorm v 4 μ) * eLpNorm (u - v) 4 μ := by
  have na : AEStronglyMeasurable (fun x => ‖u x‖) μ := hu.norm
  have nb : AEStronglyMeasurable (fun x => ‖v x‖) μ := hv.norm
  have nd : AEStronglyMeasurable (fun x => ‖(u - v) x‖) μ := (hu.sub hv).norm
  have h43 : (1 : ℝ≥0∞) ≤ 4 / 3 := Fact.out
  refine (eLpNorm_mono_real ((aesm_cubF hu).sub (aesm_cubF hv))
    (g := (fun x => ‖u x‖ * ‖u x‖ * ‖(u - v) x‖ + ‖u x‖ * ‖v x‖ * ‖(u - v) x‖) +
      fun x => ‖v x‖ * ‖v x‖ * ‖(u - v) x‖) fun x => ?_).trans ?_
  · simp only [Pi.sub_apply, Pi.add_apply, cubF]
    refine (cub_pt (u x) (v x)).trans (le_of_eq ?_)
    ring
  refine (eLpNorm_add_le h43).trans ?_
  refine (add_le_add_left (eLpNorm_add_le (f := fun x => ‖u x‖ * ‖u x‖ * ‖(u - v) x‖) h43) _).trans ?_
  have h1 := holder3 (μ := μ) na na nd
  have h2 := holder3 (μ := μ) na nb nd
  have h3 := holder3 (μ := μ) nb nb nd
  rw [eLpNorm_norm u hu, eLpNorm_norm (u - v) (hu.sub hv)] at h1 h2
  rw [eLpNorm_norm v hv, eLpNorm_norm (u - v) (hu.sub hv)] at h3
  rw [eLpNorm_norm v hv] at h2
  calc _ ≤ _ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

lemma memLp_cubF (u : Lp ℂ 4 μ) : MemLp (cubF (u : X → ℂ)) (4 / 3) μ := by
  have hu := Lp.memLp u
  have ht : eLpNorm (u : X → ℂ) 4 μ < ⊤ := lt_top_iff_ne_top.2 hu.ne
  exact (eLpNorm_cubF_le hu.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ht ht) ht)

/-- `|u|²u ∈ L^{4/3}` for `u ∈ L⁴`. -/
def cub (u : Lp ℂ 4 μ) : Lp ℂ (4 / 3) μ := (memLp_cubF u).toLp _

lemma coeFn_cub (u : Lp ℂ 4 μ) : (cub u : X → ℂ) =ᵐ[μ] cubF (u : X → ℂ) :=
  (memLp_cubF u).coeFn_toLp

/-- `‖|u|²u‖_{4/3} ≤ ‖u‖₄³`. -/
theorem norm_cub_le (u : Lp ℂ 4 μ) : ‖cub u‖ ≤ ‖u‖ * ‖u‖ * ‖u‖ := by
  have hu := Lp.memLp u
  rw [cub, Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hu.ne hu.ne) hu.ne)
    (eLpNorm_cubF_le hu.aestronglyMeasurable)

/-- **The nonlinear Hölder estimate** (`ROOT_L2_extension.tex`, proof of `thm:root-L2-flow`):
`‖|u|²u − |v|²v‖_{4/3} ≤ (‖u‖₄² + ‖u‖₄‖v‖₄ + ‖v‖₄²)‖u − v‖₄`. -/
theorem norm_cub_sub_le (u v : Lp ℂ 4 μ) :
    ‖cub u - cub v‖ ≤ (‖u‖ * ‖u‖ + ‖u‖ * ‖v‖ + ‖v‖ * ‖v‖) * ‖u - v‖ := by
  have hu := Lp.memLp u
  have hv := Lp.memLp v
  have e1 : eLpNorm (cub u - cub v : Lp ℂ (4 / 3) μ) (4 / 3) μ =
      eLpNorm (cubF (u : X → ℂ) - cubF (v : X → ℂ)) (4 / 3) μ := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (cub u) (cub v), coeFn_cub u, coeFn_cub v] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply]
  have e2 : eLpNorm (u - v : Lp ℂ 4 μ) 4 μ = eLpNorm ((u : X → ℂ) - (v : X → ℂ)) 4 μ :=
    eLpNorm_congr_ae (Lp.coeFn_sub u v)
  have hd : eLpNorm ((u : X → ℂ) - (v : X → ℂ)) 4 μ ≠ ⊤ := (hu.sub hv).ne
  have hU := hu.ne
  have hV := hv.ne
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def, Lp.norm_def, e1, e2]
  have hle := eLpNorm_cubF_sub_le hu.aestronglyMeasurable hv.aestronglyMeasurable
  have hfin : (eLpNorm u 4 μ * eLpNorm u 4 μ + eLpNorm u 4 μ * eLpNorm v 4 μ +
      eLpNorm v 4 μ * eLpNorm v 4 μ) * eLpNorm ((u : X → ℂ) - (v : X → ℂ)) 4 μ ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ hd
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hU hU,
      ENNReal.mul_ne_top hU hV⟩, ENNReal.mul_ne_top hV hV⟩
  refine (ENNReal.toReal_mono hfin hle).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hU hU,
      ENNReal.mul_ne_top hU hV⟩) (ENNReal.mul_ne_top hV hV),
    ENNReal.toReal_add (ENNReal.mul_ne_top hU hU) (ENNReal.mul_ne_top hU hV),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]

end Cubic

#print axioms norm_cub_le
#print axioms norm_cub_sub_le

variable {L : ℝ} [Fact (0 < L)]

/-! ## 2. Equality in `L⁴(J × 𝕋_L)` from equality of slices -/

theorem Lp_eq_of_slices {α β : ℝ} (f g : Lp ℂ 4 (μJ (L := L) α β))
    (h : ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
      (fun x => f (t, x)) =ᵐ[volume] fun x => g (t, x)) : f = g := by
  have hfm := Lp.aestronglyMeasurable f
  have hgm := Lp.aestronglyMeasurable g
  have hf := hfm.ae_eq_mk
  have hg := hgm.ae_eq_mk
  have hS : MeasurableSet {p : ℝ × AddCircle L | hfm.mk f p = hgm.mk g p} :=
    hfm.stronglyMeasurable_mk.measurableSet_eq_fun hgm.stronglyMeasurable_mk
  have hmk : ∀ᵐ p ∂(μJ (L := L) α β), p ∈ {p : ℝ × AddCircle L | hfm.mk f p = hgm.mk g p} := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hS).2 ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hf, Measure.ae_ae_of_ae_prod hg, h] with t h1 h2 h3
    filter_upwards [h1, h2, h3] with x e1 e2 e3
    show hfm.mk f (t, x) = hgm.mk g (t, x)
    rw [← e1, ← e2]
    exact e3
  refine Lp.ext ?_
  filter_upwards [hf, hg, hmk] with p e1 e2 e3
  rw [e1, e2]
  exact e3

/-! ## 3. Linearity of the Duhamel maps in the forcing -/

section Linear

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L)

lemma rep_congr {G₁ G₂ : ℝ × AddCircle L → ℂ} (h1 : MemLp G₁ (4 / 3) (μJ α β))
    (h2 : MemLp G₂ (4 / 3) (μJ α β)) (h : G₁ =ᵐ[μJ α β] G₂) :
    rep hαβ hlen h1 = rep hαβ hlen h2 := by
  refine ext_inner_left ℂ fun x => ?_
  rw [inner_rep, inner_rep]
  exact integral_congr_ae (h.mono fun p hp => by simp only [hp])

lemma Rt_sub (F₁ F₂ : Lp ℂ (4 / 3) (μJ (L := L) α β)) (t : ℝ) :
    Rt hαβ hlen (F₁ - F₂) t = Rt hαβ hlen F₁ t - Rt hαβ hlen F₂ t := by
  rw [Rt, Rt, Rt, ← rep_sub]
  refine rep_congr hαβ hlen _ _ ?_
  filter_upwards [Lp.coeFn_sub F₁ F₂] with p hp
  simp only [Fcut, Pi.sub_apply, Set.indicator_apply]
  split_ifs
  · rw [hp, Pi.sub_apply]
  · simp

/-- `V` is additive in the forcing: `V[F₁ − F₂] = V[F₁] − V[F₂]`. -/
theorem V_sub (F₁ F₂ : Lp ℂ (4 / 3) (μJ (L := L) α β)) (a t : ℝ) :
    V hαβ hlen (F₁ - F₂) a t = V hαβ hlen F₁ a t - V hαβ hlen F₂ a t := by
  rw [V, V, V, Sop, Sop, Sop, Rt_sub, Rt_sub, ← evol_sub]
  congr 1
  abel

variable (h1 : β - α ≤ 1)
include h1

/-- `Vst` is additive in the forcing. -/
theorem Vst_sub (F₁ F₂ : Lp ℂ (4 / 3) (μJ (L := L) α β)) (a : ℝ) :
    Vst hαβ hlen (F₁ - F₂) a = Vst hαβ hlen F₁ a - Vst hαβ hlen F₂ a := by
  refine Lp_eq_of_slices _ _ ?_
  filter_upwards [Vst_slice hαβ hlen h1 (F₁ - F₂) a, Vst_slice hαβ hlen h1 F₁ a,
    Vst_slice hαβ hlen h1 F₂ a,
    Measure.ae_ae_of_ae_prod (Lp.coeFn_sub (Vst hαβ hlen F₁ a) (Vst hαβ hlen F₂ a))]
    with t e0 e1 e2 e3
  filter_upwards [e0, e1, e2, e3, Lp.coeFn_sub (V hαβ hlen F₁ a t) (V hαβ hlen F₂ a t)]
    with x x0 x1 x2 x3 x4
  rw [x0, x3, Pi.sub_apply, x1, x2, V_sub, x4, Pi.sub_apply]

end Linear

#print axioms Lp_eq_of_slices
#print axioms V_sub
#print axioms Vst_sub

/-! ## 4. The Duhamel equation -/

section Duhamel

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L)

/-- **The cubic Duhamel equation** with coefficient `c` and data `f` at time `a`, on `J = (α, β]`:
for a.e. `t ∈ J`, the slice `u(t, ·) ∈ L²` equals `U(t − a) f + c ∫_a^t U(t − s)(|u|²u)(s) ds`
(the integral is DD1's duality Duhamel map `V`, `lem:root-L4-duality`). For the equation
`i ∂_t u = −∂_x² u + 2κ|u|²u` the coefficient is `c = −2iκ`. -/
def IsDuhamel (c : ℂ) (a : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
    (fun x => u (t, x)) =ᵐ[volume] (evol f (t - a) + c • V hαβ hlen (cub u) a t : HL L)

/-- The Duhamel map on `L⁴(J × 𝕋_L)`: `Φ(u) = U(· − a)f + c Vst[|u|²u]`. -/
def Phi (c : ℂ) (a : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) : Lp ℂ 4 (μJ (L := L) α β) :=
  freeL4 α β (evol f (-a)) + c • Vst hαβ hlen (cub u) a

variable (h1 : β - α ≤ 1)
include h1

lemma Phi_slice (c : ℂ) (a : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
      (fun x => Phi hαβ hlen c a f u (t, x)) =ᵐ[volume]
        (evol f (t - a) + c • V hαβ hlen (cub u) a t : HL L) := by
  filter_upwards [freeL4_slice hαβ hlen (evol f (-a)), Vst_slice hαβ hlen h1 (cub u) a,
    Measure.ae_ae_of_ae_prod (Lp.coeFn_add (freeL4 α β (evol f (-a)))
      (c • Vst hαβ hlen (cub u) a)),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c (Vst hαβ hlen (cub u) a))] with t e1 e2 e3 e4
  filter_upwards [e1, e2, e3, e4, Lp.coeFn_add (evol f (t - a)) (c • V hαβ hlen (cub u) a t),
    Lp.coeFn_smul c (V hαβ hlen (cub u) a t)] with x x1 x2 x3 x4 x5 x6
  show Phi hαβ hlen c a f u (t, x) = _
  rw [Phi, x3, Pi.add_apply, x1, x4, Pi.smul_apply, x2, x5, Pi.add_apply, x6, Pi.smul_apply,
    evol_evol, sub_eq_add_neg]

/-- The Duhamel equation is the fixed-point equation `u = Φ(u)` in `L⁴(J × 𝕋_L)`. -/
theorem isDuhamel_iff (c : ℂ) (a : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) :
    IsDuhamel hαβ hlen c a f u ↔ u = Phi hαβ hlen c a f u := by
  constructor
  · intro h
    refine Lp_eq_of_slices _ _ ?_
    filter_upwards [h, Phi_slice hαβ hlen h1 c a f u] with t e1 e2
    exact e1.trans e2.symm
  · intro h
    filter_upwards [Phi_slice hαβ hlen h1 c a f u] with t e
    refine EventuallyEq.trans (Eventually.of_forall fun x => ?_) e
    exact congrArg (fun w : Lp ℂ 4 (μJ (L := L) α β) => (w : ℝ × AddCircle L → ℂ) (t, x)) h

end Duhamel

#print axioms isDuhamel_iff

/-! ## 5. The linear constants -/

/-- `c₀ = (32 K C_L⁴)^{1/4} + K^{1/4} C_L`, so that `‖Vst F‖ ≤ c₀ (β−α)^{1/16} ‖F‖_{4/3}`. -/
def c0 (L : ℝ) [Fact (0 < L)] : ℝ :=
  (32 * Kg L * CL L ^ 4) ^ (4⁻¹ : ℝ) + Kg L ^ (4⁻¹ : ℝ) * CL L

lemma c0_nonneg : 0 ≤ c0 L := by
  have hK := Kg_nonneg (L := L)
  have hC := CL_nonneg (L := L)
  unfold c0
  positivity

theorem norm_Vst_le' {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (h1 : β - α ≤ 1) (hlt : α < β)
    (F : Lp ℂ (4 / 3) (μJ (L := L) α β)) (a : ℝ) :
    ‖Vst hαβ hlen F a‖ ≤ c0 L * (β - α) ^ (16⁻¹ : ℝ) * ‖F‖ := by
  refine (norm_Vst_le hαβ hlen h1 F hlt a).trans (le_of_eq ?_)
  have hK := Kg_nonneg (L := L)
  have hC := CL_nonneg (L := L)
  have hT : 0 ≤ β - α := by linarith
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hT, show (4⁻¹ : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (norm_nonneg _) (by norm_num)]
  unfold c0
  norm_num
  ring

#print axioms norm_Vst_le'

/-! ## 6. The Duhamel map: bounds -/

section Bounds

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (h1 : β - α ≤ 1) (hlt : α < β)
include h1 hlt

lemma norm_Phi_le (c : ℂ) (a : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) :
    ‖Phi hαβ hlen c a f u‖ ≤
      CL L * ‖f‖ + ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ)) * (‖u‖ * ‖u‖ * ‖u‖) := by
  have hc0 : 0 ≤ c0 L * (β - α) ^ (16⁻¹ : ℝ) :=
    mul_nonneg c0_nonneg (Real.rpow_nonneg (by linarith) _)
  calc ‖Phi hαβ hlen c a f u‖
      ≤ ‖freeL4 α β (evol f (-a))‖ + ‖c‖ * ‖Vst hαβ hlen (cub u) a‖ := by
        rw [Phi]; exact (norm_add_le _ _).trans (le_of_eq (by rw [norm_smul]))
    _ ≤ CL L * ‖f‖ + ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ) * ‖cub u‖) := by
        gcongr
        · exact (norm_freeL4_le hαβ hlen _).trans (le_of_eq (by rw [norm_evol]))
        · exact norm_Vst_le' hαβ hlen h1 hlt _ a
    _ ≤ CL L * ‖f‖ + ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ) * (‖u‖ * ‖u‖ * ‖u‖)) := by
        gcongr
        exact norm_cub_le u
    _ = _ := by ring

lemma norm_Phi_sub_le (c : ℂ) (a : ℝ) (f g : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)) :
    ‖Phi hαβ hlen c a f u - Phi hαβ hlen c a g v‖ ≤
      CL L * ‖f - g‖ + ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ)) *
        ((‖u‖ * ‖u‖ + ‖u‖ * ‖v‖ + ‖v‖ * ‖v‖) * ‖u - v‖) := by
  have hc0 : 0 ≤ c0 L * (β - α) ^ (16⁻¹ : ℝ) :=
    mul_nonneg c0_nonneg (Real.rpow_nonneg (by linarith) _)
  have e : Phi hαβ hlen c a f u - Phi hαβ hlen c a g v =
      freeL4 α β (evol (f - g) (-a)) + c • Vst hαβ hlen (cub u - cub v) a := by
    rw [Phi, Phi, Vst_sub hαβ hlen h1, evol_sub, freeL4_sub hαβ hlen, smul_sub]
    abel
  calc ‖Phi hαβ hlen c a f u - Phi hαβ hlen c a g v‖
      ≤ ‖freeL4 α β (evol (f - g) (-a))‖ + ‖c‖ * ‖Vst hαβ hlen (cub u - cub v) a‖ := by
        rw [e]; exact (norm_add_le _ _).trans (le_of_eq (by rw [norm_smul]))
    _ ≤ CL L * ‖f - g‖ + ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ) * ‖cub u - cub v‖) := by
        gcongr
        · exact (norm_freeL4_le hαβ hlen _).trans (le_of_eq (by rw [norm_evol]))
        · exact norm_Vst_le' hαβ hlen h1 hlt _ a
    _ ≤ CL L * ‖f - g‖ + ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ) *
          ((‖u‖ * ‖u‖ + ‖u‖ * ‖v‖ + ‖v‖ * ‖v‖) * ‖u - v‖)) := by
        gcongr
        exact norm_cub_sub_le u v
    _ = _ := by ring

end Bounds

#print axioms norm_Phi_le
#print axioms norm_Phi_sub_le

/-! ## 7. The continuous `L²` representative -/

section Curve

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L)

/-- The right-hand side of the Duhamel equation as a curve in `L²`:
`t ↦ U(t − a) f + c ∫_a^t U(t − s)(|u|²u)(s) ds`. -/
def Dcurve (c : ℂ) (a : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) (t : ℝ) : HL L :=
  evol f (t - a) + c • V hαβ hlen (cub u) a t

lemma isDuhamel_iff_curve (c : ℂ) (a : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) :
    IsDuhamel hαβ hlen c a f u ↔ ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
      (fun x => u (t, x)) =ᵐ[volume] (Dcurve hαβ hlen c a f u t : AddCircle L → ℂ) := Iff.rfl

/-- `C(ℝ; L²)`: the curve is continuous. -/
theorem continuous_Dcurve (c : ℂ) (a : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) :
    Continuous (Dcurve hαβ hlen c a f u) :=
  ((continuous_evol f).comp (continuous_id.sub continuous_const)).add
    ((continuous_V hαβ hlen (cub u) a).const_smul c)

lemma norm_Dcurve_le (c : ℂ) (a : ℝ) (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) (t : ℝ) :
    ‖Dcurve hαβ hlen c a f u t‖ ≤ ‖f‖ + ‖c‖ * CL L * (‖u‖ * ‖u‖ * ‖u‖) := by
  have hC := CL_nonneg (L := L)
  calc ‖Dcurve hαβ hlen c a f u t‖ ≤ ‖evol f (t - a)‖ + ‖c‖ * ‖V hαβ hlen (cub u) a t‖ :=
        (norm_add_le _ _).trans (le_of_eq (by rw [norm_smul]))
    _ ≤ ‖f‖ + ‖c‖ * (CL L * (‖u‖ * ‖u‖ * ‖u‖)) := by
        rw [norm_evol]
        gcongr
        exact (norm_V_le hαβ hlen _ a t).trans (mul_le_mul_of_nonneg_left (norm_cub_le u) hC)
    _ = _ := by ring

lemma norm_Dcurve_sub_le (c : ℂ) (a : ℝ) (f g : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β))
    (t : ℝ) :
    ‖Dcurve hαβ hlen c a f u t - Dcurve hαβ hlen c a g v t‖ ≤
      ‖f - g‖ + ‖c‖ * CL L * ((‖u‖ * ‖u‖ + ‖u‖ * ‖v‖ + ‖v‖ * ‖v‖) * ‖u - v‖) := by
  have hC := CL_nonneg (L := L)
  have e : Dcurve hαβ hlen c a f u t - Dcurve hαβ hlen c a g v t =
      evol (f - g) (t - a) + c • V hαβ hlen (cub u - cub v) a t := by
    rw [Dcurve, Dcurve, V_sub, evol_sub, smul_sub]
    abel
  rw [e]
  calc ‖evol (f - g) (t - a) + c • V hαβ hlen (cub u - cub v) a t‖
      ≤ ‖evol (f - g) (t - a)‖ + ‖c‖ * ‖V hαβ hlen (cub u - cub v) a t‖ :=
        (norm_add_le _ _).trans (le_of_eq (by rw [norm_smul]))
    _ ≤ ‖f - g‖ + ‖c‖ * (CL L * ((‖u‖ * ‖u‖ + ‖u‖ * ‖v‖ + ‖v‖ * ‖v‖) * ‖u - v‖)) := by
        rw [norm_evol]
        gcongr
        exact (norm_V_le hαβ hlen _ a t).trans
          (mul_le_mul_of_nonneg_left (norm_cub_sub_le u v) hC)
    _ = _ := by ring

end Curve

#print axioms continuous_Dcurve
#print axioms norm_Dcurve_sub_le

/-! ## 8. The constants `τ_R`, `B_R`, `A_R` and the contraction -/

/-- `B_R = 2 C_L R`. -/
def Bc (L : ℝ) [Fact (0 < L)] (R : ℝ) : ℝ := 2 * CL L * R

/-- `A_R = 2 C_L`. -/
def Ac (L : ℝ) [Fact (0 < L)] : ℝ := 2 * CL L

/-- `M = 6 |c| c₀ B_R²`. -/
def Mc (L : ℝ) [Fact (0 < L)] (c : ℂ) (R : ℝ) : ℝ := 6 * ‖c‖ * c0 L * Bc L R ^ 2

/-- `τ_R = min(1, T_L, (1 + M)^{-16})`; it depends only on `L`, `c` and `R`. -/
def tauc (L : ℝ) [Fact (0 < L)] (c : ℂ) (R : ℝ) : ℝ :=
  min (min 1 (TL L)) ((1 + Mc L c R)⁻¹ ^ (16 : ℕ))

lemma Mc_nonneg (c : ℂ) (R : ℝ) : 0 ≤ Mc L c R := by
  have := c0_nonneg (L := L)
  unfold Mc
  positivity

lemma tauc_pos (c : ℂ) (R : ℝ) : 0 < tauc L c R := by
  have hM := Mc_nonneg (L := L) c R
  have hT := TL_pos (L := L)
  unfold tauc
  refine lt_min (lt_min one_pos hT) (pow_pos (inv_pos.2 (by linarith)) _)

lemma tauc_le_one (c : ℂ) (R : ℝ) : tauc L c R ≤ 1 :=
  (min_le_left _ _).trans (min_le_left _ _)

lemma tauc_le_TL (c : ℂ) (R : ℝ) : tauc L c R ≤ TL L :=
  (min_le_left _ _).trans (min_le_right _ _)

lemma key_small (c : ℂ) (R : ℝ) {T : ℝ} (hT0 : 0 < T) (hT : T ≤ tauc L c R) :
    ‖c‖ * (c0 L * T ^ (16⁻¹ : ℝ)) * (6 * Bc L R ^ 2) ≤ 1 := by
  have hM := Mc_nonneg (L := L) c R
  have hs : T ^ (16⁻¹ : ℝ) ≤ (1 + Mc L c R)⁻¹ := by
    calc T ^ (16⁻¹ : ℝ) ≤ ((1 + Mc L c R)⁻¹ ^ (16 : ℕ)) ^ (16⁻¹ : ℝ) :=
          Real.rpow_le_rpow hT0.le (hT.trans (min_le_right _ _)) (by norm_num)
      _ = (1 + Mc L c R)⁻¹ := by
          rw [show (16⁻¹ : ℝ) = ((16 : ℕ) : ℝ)⁻¹ by norm_num,
            Real.pow_rpow_inv_natCast (inv_nonneg.2 (by linarith)) (by norm_num)]
  calc ‖c‖ * (c0 L * T ^ (16⁻¹ : ℝ)) * (6 * Bc L R ^ 2) = Mc L c R * T ^ (16⁻¹ : ℝ) := by
        unfold Mc; ring
    _ ≤ Mc L c R * (1 + Mc L c R)⁻¹ := mul_le_mul_of_nonneg_left hs hM
    _ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by linarith)]
        linarith

/-- **EXT-003, the local `L⁴` input** (`ROOT_L2_extension.tex`, lines 7-11), for the cubic Duhamel
equation with any coefficient `c`: for each bound `R` on the initial `L²` norm there are
`τ_R > 0`, `B_R < ∞`, `A_R < ∞` (depending only on `L`, `c`, `R`) such that on every interval
`J = (α, β]` of length at most `τ_R` and for every data time `a`:
1. every datum `f` with `‖f‖₂ ≤ R` has a solution `u ∈ L⁴(J × 𝕋_L)` with `‖u‖₄ ≤ B_R`;
2. it is unique among solutions with `‖u‖₄ ≤ B_R`;
3. the solution map is `A_R`-Lipschitz from the initial `L²` ball into `L⁴(J × 𝕋_L)`;
4. the continuous `L²` representatives (`continuous_Dcurve`) satisfy
   `sup_t ‖u(t) − v(t)‖₂ ≤ (1 + 3 |c| C_L B_R² A_R) ‖f − g‖₂`;
5. and `sup_t ‖u(t)‖₂ ≤ R + |c| C_L B_R³`.
Also `τ_R ≤ min(1, T_L)`. -/
theorem local_L4_contraction (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ τ B A : ℝ, 0 < τ ∧ τ ≤ 1 ∧ τ ≤ TL L ∧ 0 ≤ B ∧ 0 ≤ A ∧
      ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L), α < β → β ≤ α + τ → ∀ a : ℝ,
        (∀ f : HL L, ‖f‖ ≤ R →
          ∃ u : Lp ℂ 4 (μJ (L := L) α β), ‖u‖ ≤ B ∧ IsDuhamel hαβ hlen c a f u) ∧
        (∀ (f : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖u‖ ≤ B → ‖v‖ ≤ B →
          IsDuhamel hαβ hlen c a f u → IsDuhamel hαβ hlen c a f v → u = v) ∧
        (∀ (f g : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖g‖ ≤ R → ‖u‖ ≤ B →
          ‖v‖ ≤ B → IsDuhamel hαβ hlen c a f u → IsDuhamel hαβ hlen c a g v →
            ‖u - v‖ ≤ A * ‖f - g‖) ∧
        (∀ (f g : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖g‖ ≤ R → ‖u‖ ≤ B →
          ‖v‖ ≤ B → IsDuhamel hαβ hlen c a f u → IsDuhamel hαβ hlen c a g v → ∀ t : ℝ,
            ‖Dcurve hαβ hlen c a f u t - Dcurve hαβ hlen c a g v t‖ ≤
              (1 + 3 * ‖c‖ * CL L * B ^ 2 * A) * ‖f - g‖) ∧
        (∀ (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖u‖ ≤ B → ∀ t : ℝ,
          ‖Dcurve hαβ hlen c a f u t‖ ≤ R + ‖c‖ * CL L * B ^ 3) := by
  have hC := CL_nonneg (L := L)
  have hB0 : 0 ≤ Bc L R := by unfold Bc; positivity
  have hA0 : 0 ≤ Ac L := by unfold Ac; positivity
  refine ⟨tauc L c R, Bc L R, Ac L, tauc_pos c R, tauc_le_one c R, tauc_le_TL c R, hB0, hA0,
    fun α β hαβ hlen hlt hβ a => ?_⟩
  have h1 : β - α ≤ 1 := by linarith [tauc_le_one (L := L) c R]
  have hT0 : 0 < β - α := by linarith
  have hq := key_small (L := L) c R hT0 (by linarith)
  set q := ‖c‖ * (c0 L * (β - α) ^ (16⁻¹ : ℝ)) with hq_def
  have hq0 : 0 ≤ q := mul_nonneg (norm_nonneg _)
    (mul_nonneg c0_nonneg (Real.rpow_nonneg hT0.le _))
  set B := Bc L R with hB_def
  set A := Ac L with hA_def
  have h3 : ∀ u v : Lp ℂ 4 (μJ (L := L) α β), ‖u‖ ≤ B → ‖v‖ ≤ B →
      ‖u‖ * ‖u‖ + ‖u‖ * ‖v‖ + ‖v‖ * ‖v‖ ≤ 3 * B ^ 2 := by
    intro u v hu hv
    have e1 : ‖u‖ * ‖u‖ ≤ B * B := mul_le_mul hu hu (norm_nonneg _) hB0
    have e2 : ‖u‖ * ‖v‖ ≤ B * B := mul_le_mul hu hv (norm_nonneg _) hB0
    have e3 : ‖v‖ * ‖v‖ ≤ B * B := mul_le_mul hv hv (norm_nonneg _) hB0
    nlinarith
  -- the contraction estimate
  have hL : ∀ (f g : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖u‖ ≤ B → ‖v‖ ≤ B →
      ‖Phi hαβ hlen c a f u - Phi hαβ hlen c a g v‖ ≤ CL L * ‖f - g‖ + 1 / 2 * ‖u - v‖ := by
    intro f g u v hu hv
    have e := norm_Phi_sub_le hαβ hlen h1 hlt c a f g u v
    rw [← hq_def] at e
    have hs := h3 u v hu hv
    have hd := norm_nonneg (u - v)
    have : q * ((‖u‖ * ‖u‖ + ‖u‖ * ‖v‖ + ‖v‖ * ‖v‖) * ‖u - v‖) ≤ 1 / 2 * ‖u - v‖ := by
      calc q * ((‖u‖ * ‖u‖ + ‖u‖ * ‖v‖ + ‖v‖ * ‖v‖) * ‖u - v‖) ≤ q * ((3 * B ^ 2) * ‖u - v‖) := by
            gcongr
        _ = (q * (6 * B ^ 2)) * ‖u - v‖ / 2 := by ring
        _ ≤ 1 * ‖u - v‖ / 2 := by gcongr
        _ = 1 / 2 * ‖u - v‖ := by ring
    linarith
  -- the ball is mapped to itself
  have hM : ∀ (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖u‖ ≤ B →
      ‖Phi hαβ hlen c a f u‖ ≤ B := by
    intro f u hf hu
    have e := norm_Phi_le hαβ hlen h1 hlt c a f u
    rw [← hq_def] at e
    have e1 : CL L * ‖f‖ ≤ B / 2 := by
      rw [hB_def, Bc]
      calc CL L * ‖f‖ ≤ CL L * R := mul_le_mul_of_nonneg_left hf hC
        _ = 2 * CL L * R / 2 := by ring
    have e2 : q * (‖u‖ * ‖u‖ * ‖u‖) ≤ B / 2 := by
      calc q * (‖u‖ * ‖u‖ * ‖u‖) ≤ q * (B * B * B) := by gcongr
        _ = (q * (6 * B ^ 2)) * B / 6 := by ring
        _ ≤ 1 * B / 6 := by gcongr
        _ ≤ B / 2 := by linarith
    linarith
  -- Lipschitz dependence of solutions
  have hLip : ∀ (f g : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖u‖ ≤ B → ‖v‖ ≤ B →
      IsDuhamel hαβ hlen c a f u → IsDuhamel hαβ hlen c a g v → ‖u - v‖ ≤ A * ‖f - g‖ := by
    intro f g u v hu hv hdu hdv
    have eu := (isDuhamel_iff hαβ hlen h1 c a f u).1 hdu
    have ev := (isDuhamel_iff hαβ hlen h1 c a g v).1 hdv
    have e := hL f g u v hu hv
    rw [← eu, ← ev] at e
    rw [hA_def, Ac]
    linarith
  refine ⟨fun f hf => ?_, fun f u v hf hu hv hdu hdv => ?_,
    fun f g u v _ _ hu hv hdu hdv => hLip f g u v hu hv hdu hdv,
    fun f g u v _ _ hu hv hdu hdv t => ?_, fun f u hf hu t => ?_⟩
  · -- existence: Banach's fixed point theorem on the closed ball of radius `B`
    let S := Metric.closedBall (0 : Lp ℂ 4 (μJ (L := L) α β)) B
    have hmaps : ∀ u ∈ S, Phi hαβ hlen c a f u ∈ S := fun u hu => by
      rw [mem_closedBall_zero_iff] at hu ⊢
      exact hM f u hf hu
    have : CompleteSpace S := Metric.isClosed_closedBall.isComplete.completeSpace_coe
    have : Nonempty S := ⟨⟨0, Metric.mem_closedBall_self hB0⟩⟩
    let g : S → S := fun u => ⟨Phi hαβ hlen c a f u.1, hmaps u.1 u.2⟩
    have hg : ContractingWith (1 / 2 : NNReal) g := by
      refine ⟨by norm_num,
        LipschitzWith.of_dist_le_mul fun x y => ?_⟩
      rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
      have e := hL f f x.1 y.1 (mem_closedBall_zero_iff.1 x.2) (mem_closedBall_zero_iff.1 y.2)
      rw [sub_self, norm_zero, mul_zero, zero_add] at e
      refine e.trans (le_of_eq ?_)
      push_cast
      ring
    have hfix : g (ContractingWith.fixedPoint g hg) = ContractingWith.fixedPoint g hg :=
      ContractingWith.fixedPoint_isFixedPt hg
    refine ⟨(ContractingWith.fixedPoint g hg).1,
      mem_closedBall_zero_iff.1 (ContractingWith.fixedPoint g hg).2,
      (isDuhamel_iff hαβ hlen h1 c a f _).2 ?_⟩
    exact (congrArg Subtype.val hfix).symm
  · -- uniqueness in the ball
    have e := hLip f f u v hu hv hdu hdv
    rw [sub_self, norm_zero, mul_zero] at e
    exact sub_eq_zero.1 (norm_le_zero_iff.1 e)
  · -- `C_t L²` stability
    have e := norm_Dcurve_sub_le hαβ hlen c a f g u v t
    have hs := h3 u v hu hv
    have hd := hLip f g u v hu hv hdu hdv
    have hc := norm_nonneg c
    calc ‖Dcurve hαβ hlen c a f u t - Dcurve hαβ hlen c a g v t‖
        ≤ ‖f - g‖ + ‖c‖ * CL L * ((‖u‖ * ‖u‖ + ‖u‖ * ‖v‖ + ‖v‖ * ‖v‖) * ‖u - v‖) := e
      _ ≤ ‖f - g‖ + ‖c‖ * CL L * ((3 * B ^ 2) * (A * ‖f - g‖)) := by
          gcongr
      _ = (1 + 3 * ‖c‖ * CL L * B ^ 2 * A) * ‖f - g‖ := by ring
  · -- `C_t L²` bound
    have e := norm_Dcurve_le hαβ hlen c a f u t
    have hc := norm_nonneg c
    calc ‖Dcurve hαβ hlen c a f u t‖ ≤ ‖f‖ + ‖c‖ * CL L * (‖u‖ * ‖u‖ * ‖u‖) := e
      _ ≤ R + ‖c‖ * CL L * (B * B * B) := by gcongr
      _ = R + ‖c‖ * CL L * B ^ 3 := by ring

#print axioms local_L4_contraction

/-! ## 9. The cubic NLS `i ∂_t u = −∂_x² u + 2κ|u|²u` -/

/-- The Duhamel coefficient of `i ∂_t u = −∂_x² u + 2κ|u|²u`: `∂_t u = i∂_x² u − 2iκ|u|²u`, so
`u(t) = U(t − a)u(a) − 2iκ ∫_a^t U(t − s)(|u|²u)(s) ds`, i.e. `c = −2iκ`. -/
def cNLS (κ : ℝ) : ℂ := -(2 * (κ : ℂ) * Complex.I)

lemma norm_cNLS (κ : ℝ) : ‖cNLS κ‖ = 2 * |κ| := by
  rw [cNLS, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  norm_num

/-- **EXT-003, the quoted local `L⁴` input, for coefficient `2κ`** (`ROOT_L2_extension.tex`,
lines 7-15; Route Y, elementary proof). For each `R ≥ 0` there are `τ_R > 0`, `B_R < ∞`, `A_R < ∞`
such that on every interval `J = (α, β]` with `0 < β − α ≤ τ_R` (`τ_R ≤ min(1, T_L)`) and for every
data time `a`, the cubic Duhamel equation `u(t) = U(t−a)f − 2iκ ∫_a^t U(t−s)(|u|²u)(s) ds` has, for
each `‖f‖₂ ≤ R`, a solution in `L⁴(J × 𝕋_L)` of norm at most `B_R`, unique among such; the solution
map is `A_R`-Lipschitz from the `L²` ball into `L⁴(J × 𝕋_L)`; the continuous `L²` representatives
satisfy the stability bound `(1 + 6|κ| C_L B_R² A_R)‖f − g‖₂` (`eq:root-L2-local-stability`) and
`sup_t ‖u(t)‖₂ ≤ R + 2|κ| C_L B_R³`. -/
theorem ext003_local_input (κ R : ℝ) (hR : 0 ≤ R) :
    ∃ τ B A : ℝ, 0 < τ ∧ τ ≤ 1 ∧ τ ≤ TL L ∧ 0 ≤ B ∧ 0 ≤ A ∧
      ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L), α < β → β ≤ α + τ → ∀ a : ℝ,
        (∀ f : HL L, ‖f‖ ≤ R →
          ∃ u : Lp ℂ 4 (μJ (L := L) α β), ‖u‖ ≤ B ∧ IsDuhamel hαβ hlen (cNLS κ) a f u) ∧
        (∀ (f : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖u‖ ≤ B → ‖v‖ ≤ B →
          IsDuhamel hαβ hlen (cNLS κ) a f u → IsDuhamel hαβ hlen (cNLS κ) a f v → u = v) ∧
        (∀ (f g : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖g‖ ≤ R → ‖u‖ ≤ B →
          ‖v‖ ≤ B → IsDuhamel hαβ hlen (cNLS κ) a f u → IsDuhamel hαβ hlen (cNLS κ) a g v →
            ‖u - v‖ ≤ A * ‖f - g‖) ∧
        (∀ (f g : HL L) (u v : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖g‖ ≤ R → ‖u‖ ≤ B →
          ‖v‖ ≤ B → IsDuhamel hαβ hlen (cNLS κ) a f u → IsDuhamel hαβ hlen (cNLS κ) a g v →
            ∀ t : ℝ, ‖Dcurve hαβ hlen (cNLS κ) a f u t - Dcurve hαβ hlen (cNLS κ) a g v t‖ ≤
              (1 + 6 * |κ| * CL L * B ^ 2 * A) * ‖f - g‖) ∧
        (∀ (f : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)), ‖f‖ ≤ R → ‖u‖ ≤ B → ∀ t : ℝ,
          ‖Dcurve hαβ hlen (cNLS κ) a f u t‖ ≤ R + 2 * |κ| * CL L * B ^ 3) := by
  obtain ⟨τ, B, A, hτ, hτ1, hτL, hB, hA, H⟩ := local_L4_contraction (L := L) (cNLS κ) R hR
  refine ⟨τ, B, A, hτ, hτ1, hτL, hB, hA, fun α β hαβ hlen hlt hβ a => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5⟩ := H α β hαβ hlen hlt hβ a
  refine ⟨c1, c2, c3, fun f g u v hf hg hu hv hdu hdv t => ?_, fun f u hf hu t => ?_⟩
  · refine (c4 f g u v hf hg hu hv hdu hdv t).trans (le_of_eq ?_)
    rw [norm_cNLS]
    ring
  · refine (c5 f u hf hu t).trans (le_of_eq ?_)
    rw [norm_cNLS]

#print axioms ext003_local_input

end QuantumNLS.LocalL4Contraction
