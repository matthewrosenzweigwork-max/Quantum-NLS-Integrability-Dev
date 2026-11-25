import QuantumNLS.Ext025B8SimpleCalculus
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Normed.Operator.Extend
import QuantumNLS.Ext025B4ContinuousForms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B8BorelCalculus
open BetheChargeResolution Ext025B6PVM Ext025B8SimpleCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

/-- Null changes of a simple symbol do not change its integral at x. -/
theorem simple_ae (x : E) (f g : SimpleFunc ℝ ℂ)
    (h : (f : ℝ → ℂ) =ᵐ[scalarMeasure P x] g) : simple P f x = simple P g x := by
  have hz : ENNReal.ofReal (‖simple P (f-g) x‖^2) = 0 := by
    rw [simple_square]
    calc
      _ = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂scalarMeasure P x := lintegral_congr_ae (by
        filter_upwards [h] with t ht
        simp only [SimpleFunc.sub_apply,ht,sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0),ENNReal.ofReal_zero])
      _ = 0 := lintegral_zero
  have he : simple P (f-g) x = 0 := by
    have hh := ENNReal.ofReal_eq_zero.mp hz
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (simple P (f-g) x)])
  simpa only [simple_sub,sub_apply,sub_eq_zero] using he

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module Lp.simpleFunc.normedSpace

/-- The cyclic integral initially defined on dense L2 simple functions. -/
def cyclicSimple (x : E) : Lp.simpleFunc ℂ 2 (scalarMeasure P x) →ₗ[ℂ] E where
  toFun f := simple P (Lp.simpleFunc.toSimpleFunc f) x
  map_add' f g := by
    have he := simple_ae P x (Lp.simpleFunc.toSimpleFunc (f+g))
      (Lp.simpleFunc.toSimpleFunc f+Lp.simpleFunc.toSimpleFunc g) (Lp.simpleFunc.add_toSimpleFunc f g)
    change simple P (Lp.simpleFunc.toSimpleFunc (f+g)) x = _
    rw [he,simple_add]
    rfl
  map_smul' c f := by
    have he := simple_ae P x (Lp.simpleFunc.toSimpleFunc (c • f))
      (c • Lp.simpleFunc.toSimpleFunc f) (Lp.simpleFunc.smul_toSimpleFunc c f)
    change simple P (Lp.simpleFunc.toSimpleFunc (c • f)) x = c • simple P (Lp.simpleFunc.toSimpleFunc f) x
    rw [he,simple_smul,smul_apply]



/-- Exact cyclic norm, before completing the simple functions. -/
theorem cyclicSimple_norm (x : E) (f : Lp.simpleFunc ℂ 2 (scalarMeasure P x)) :
    ‖cyclicSimple P x f‖ = ‖(f : Lp ℂ 2 (scalarMeasure P x))‖ := by
  have hs := simple_square P (Lp.simpleFunc.toSimpleFunc f) x
  have hr := congrArg ENNReal.toReal hs
  rw [ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  have hi : (∫ t, ‖Lp.simpleFunc.toSimpleFunc f t‖^2 ∂scalarMeasure P x) =
      (∫⁻ t, ENNReal.ofReal (‖Lp.simpleFunc.toSimpleFunc f t‖^2) ∂scalarMeasure P x).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
      ((Lp.simpleFunc.toSimpleFunc f).aestronglyMeasurable.norm.pow 2)
  have hn := Ext025B4ContinuousForms.norm_sq_integral (f : Lp ℂ 2 (scalarMeasure P x))
  have he : (∫ t, ‖Lp.simpleFunc.toSimpleFunc f t‖^2 ∂scalarMeasure P x) =
      ∫ t, ‖(f : Lp ℂ 2 (scalarMeasure P x)) t‖^2 ∂scalarMeasure P x :=
    integral_congr_ae (by filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun f] with t ht; rw [ht])
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact hr.trans (hi.symm.trans (he.trans hn.symm))

/-- The cyclic L2 isometry for an arbitrary PVM is constructed by completion.
This is not an assumed unitary representation of the entire Hilbert space. -/
def cyclic (x : E) : Lp ℂ 2 (scalarMeasure P x) →ₗᵢ[ℂ] E :=
  (cyclicSimple P x).extendOfIsometry
    (e := (Lp.simpleFunc.coeToLp ℝ ℂ ℂ).toLinearMap)
    (Lp.simpleFunc.denseRange (by norm_num)) (cyclicSimple_norm P x)

theorem cyclic_simple (x : E) (f : SimpleFunc ℝ ℂ)
    (hf : MemLp f 2 (scalarMeasure P x)) :
    cyclic P x (hf.toLp f) = simple P f x := by
  have he := LinearMap.extendOfIsometry_eq (cyclicSimple P x)
    (e := (Lp.simpleFunc.coeToLp ℝ ℂ ℂ).toLinearMap)
    (show DenseRange ((Lp.simpleFunc.coeToLp ℝ ℂ ℂ (μ := scalarMeasure P x) (p := 2)).toLinearMap) from
      Lp.simpleFunc.denseRange (by norm_num))
    (fun g => cyclicSimple_norm P x g) (f.toLp hf)
  change cyclic P x (hf.toLp f) = simple P (Lp.simpleFunc.toSimpleFunc (f.toLp hf)) x at he
  exact he.trans (simple_ae P x _ f (Lp.simpleFunc.toSimpleFunc_toLp f hf))


/-- Exact scalar square-integrability criterion for vector integration. -/
theorem square_domain_iff (f : ℝ → ℂ) (hf : Measurable f) (x : E) :
    MemLp f 2 (scalarMeasure P x) ↔
      (∫⁻ t, ENNReal.ofReal (‖f t‖^2) ∂scalarMeasure P x) ≠ ⊤ :=
  (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).trans
    (lintegral_ofReal_ne_top_iff_integrable
      (hf.aestronglyMeasurable.norm.pow 2) (.of_forall fun _ => sq_nonneg _)).symm

/-- Borel vector integration on its exact square-integrable domain. -/
def vectorIntegral (f : ℝ → ℂ) (x : E) (hf : MemLp f 2 (scalarMeasure P x)) : E :=
  cyclic P x (hf.toLp f)

/-- The spectral integral's squared norm is the scalar square integral. -/
theorem vectorIntegral_square (f : ℝ → ℂ) (x : E) (hf : MemLp f 2 (scalarMeasure P x)) :
    ‖vectorIntegral P f x hf‖^2 = ∫ t, ‖f t‖^2 ∂scalarMeasure P x := by
  rw [vectorIntegral,(cyclic P x).norm_map,Ext025B4ContinuousForms.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]

/-- The same norm identity in extended nonnegative form. -/
theorem vectorIntegral_esquare (f : ℝ → ℂ) (x : E) (hf : MemLp f 2 (scalarMeasure P x)) :
    ENNReal.ofReal (‖vectorIntegral P f x hf‖^2) =
      ∫⁻ t, ENNReal.ofReal (‖f t‖^2) ∂scalarMeasure P x := by
  rw [vectorIntegral_square]
  exact ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf) (.of_forall fun _ => sq_nonneg _)

/-- One common, vector-independent approximation of a Borel symbol. -/
def approx (f : ℝ → ℂ) (hf : Measurable f) (n : ℕ) : SimpleFunc ℝ ℂ :=
  SimpleFunc.approxOn f hf (Set.range f ∪ {0}) 0 (by simp) n

theorem approx_bound (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) (n : ℕ) (t : ℝ) : ‖approx f hf n t‖ ≤ C := by
  have h := SimpleFunc.approxOn_mem hf (s := Set.range f ∪ {0}) (by simp : (0 : ℂ) ∈ Set.range f ∪ {0}) n t
  change approx f hf n t ∈ Set.range f ∪ {0} at h
  rcases h with ⟨u,hu⟩ | h
  · rw [← hu]; exact hb u
  · simpa only [Set.mem_singleton_iff.mp h,norm_zero] using hC

/-- The construction agrees with strong limits of its literal simple integrals. -/
theorem approx_integral (f : ℝ → ℂ) (hf : Measurable f) (x : E)
    (hmem : MemLp f 2 (scalarMeasure P x)) :
    Tendsto (fun n => simple P (approx f hf n) x) atTop
      (𝓝 (vectorIntegral P f x hmem)) := by
  have h := SimpleFunc.tendsto_approxOn_range_Lp (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf hmem
  have hc := (cyclic P x).continuous.continuousAt.tendsto.comp h
  simpa only [Function.comp_def,cyclic_simple,vectorIntegral,approx] using hc

/-- Construct the bounded Borel multiplier on the original Hilbert space. -/
def bounded (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) : E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun x => vectorIntegral P f x (MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb))
      map_add' := by
        intro x y
        have hx := approx_integral P f hf x (MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb))
        have hy := approx_integral P f hf y (MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb))
        exact tendsto_nhds_unique (approx_integral P f hf (x+y)
          (MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb)))
          (by simpa only [map_add] using hx.add hy)
      map_smul' := by
        intro c x
        have hx := approx_integral P f hf x (MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb))
        exact tendsto_nhds_unique (approx_integral P f hf (c • x)
          (MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb)))
          (by simpa only [map_smul,RingHom.id_apply] using hx.const_smul c) }
    C (fun x => by
      have hx := (approx_integral P f hf x
        (MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb))).norm
      apply le_of_tendsto hx
      exact .of_forall fun n => (simple P (approx f hf n)).le_of_opNorm_le
        (simple_bound P (approx f hf n) C hC (approx_bound f hf C hC hb n)) x)

/-- Sharp operator-norm bound for the constructed integral. -/
theorem bounded_norm (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) : ‖bounded P f hf C hC hb‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem bounded_apply (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) (x : E) :
    bounded P f hf C hC hb x = vectorIntegral P f x
      (MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb)) := rfl

theorem bounded_simple (f : SimpleFunc ℝ ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) : bounded P f f.measurable C hC hb = simple P f := by
  ext x
  exact cyclic_simple P x f _

theorem bounded_add (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ t, ‖f t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ D) :
    bounded P (f+g) (hf.add hg) (C+D) (add_nonneg hC hD)
      (fun t => (norm_add_le _ _).trans (add_le_add (hb t) (hc t))) =
      bounded P f hf C hC hb + bounded P g hg D hD hc := by
  ext x
  let hfm : MemLp f 2 (scalarMeasure P x) := MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb)
  let hgm : MemLp g 2 (scalarMeasure P x) := MemLp.of_bound hg.aestronglyMeasurable D (.of_forall hc)
  change cyclic P x ((hfm.add hgm).toLp (f+g)) = cyclic P x (hfm.toLp f)+cyclic P x (hgm.toLp g)
  rw [MemLp.toLp_add,map_add]

theorem bounded_smul (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) (c : ℂ) :
    bounded P (c • f) (measurable_const.smul hf) (‖c‖*C) (mul_nonneg (norm_nonneg _) hC)
      (fun t => by rw [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)) =
      c • bounded P f hf C hC hb := by
  ext x
  let hfm : MemLp f 2 (scalarMeasure P x) := MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb)
  change cyclic P x ((hfm.const_smul c).toLp (c • f)) = c • cyclic P x (hfm.toLp f)
  rw [MemLp.toLp_const_smul,map_smul]

theorem bounded_one : bounded P (fun _ => 1) measurable_const 1 zero_le_one (fun _ => by simp) = 1 := by
  have he := bounded_simple P (SimpleFunc.const ℝ 1) 1 zero_le_one (fun _ => by simp)
  exact he.trans (by simpa only [one_smul] using simple_const P 1)


/-- The exact square-error identity on the actual PVM scalar measure. -/
theorem bounded_error_square (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ t, ‖f t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ D) (x : E) :
    ‖bounded P f hf C hC hb x-bounded P g hg D hD hc x‖^2 =
      ∫ t, ‖f t-g t‖^2 ∂scalarMeasure P x := by
  let hfm : MemLp f 2 (scalarMeasure P x) := MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb)
  let hgm : MemLp g 2 (scalarMeasure P x) := MemLp.of_bound hg.aestronglyMeasurable D (.of_forall hc)
  have he : bounded P f hf C hC hb x-bounded P g hg D hD hc x =
      vectorIntegral P (f-g) x (hfm.sub hgm) := by
    change cyclic P x (hfm.toLp f)-cyclic P x (hgm.toLp g) = cyclic P x ((hfm.sub hgm).toLp (f-g))
    rw [MemLp.toLp_sub,map_sub]
  rw [he,vectorIntegral_square]
  rfl

/-- Bounded Borel pointwise convergence gives strong convergence for every
arbitrary PVM; the finite scalar measure supplies the constant majorant. -/
theorem bounded_strong {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
    (f : J → ℝ → ℂ) (g : ℝ → ℂ) (hf : ∀ j, Measurable (f j)) (hg : Measurable g)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ j t, ‖f j t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ C)
    (hl : ∀ t, Tendsto (fun j => f j t) l (𝓝 (g t))) (x : E) :
    Tendsto (fun j => bounded P (f j) (hf j) C hC (hb j) x) l
      (𝓝 (bounded P g hg C hC hc x)) := by
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := scalarMeasure P x) (l := l) (fun _ : ℝ => (2*C)^2)
    (F := fun j t => ‖f j t-g t‖^2) (f := fun _ => (0 : ℝ))
    (.of_forall fun j => ((hf j).sub hg).aestronglyMeasurable.norm.pow 2)
    (.of_forall fun j => .of_forall fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by linarith [hb j t,hc t]))
    (integrable_const _) (.of_forall fun t => by simpa using ((hl t).sub_const (g t)).norm.pow 2)
  have hs : Tendsto (fun j => ‖bounded P (f j) (hf j) C hC (hb j) x-
      bounded P g hg C hC hc x‖^2) l (𝓝 0) := by
    simpa only [bounded_error_square,integral_zero] using ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hs

end QuantumNLS.Ext025B8BorelCalculus

#print axioms QuantumNLS.Ext025B8BorelCalculus.simple_ae
#print axioms QuantumNLS.Ext025B8BorelCalculus.cyclicSimple
#print axioms QuantumNLS.Ext025B8BorelCalculus.cyclicSimple_norm
#print axioms QuantumNLS.Ext025B8BorelCalculus.cyclic
#print axioms QuantumNLS.Ext025B8BorelCalculus.cyclic_simple
#print axioms QuantumNLS.Ext025B8BorelCalculus.vectorIntegral
#print axioms QuantumNLS.Ext025B8BorelCalculus.square_domain_iff
#print axioms QuantumNLS.Ext025B8BorelCalculus.vectorIntegral_square
#print axioms QuantumNLS.Ext025B8BorelCalculus.vectorIntegral_esquare
#print axioms QuantumNLS.Ext025B8BorelCalculus.approx
#print axioms QuantumNLS.Ext025B8BorelCalculus.approx_bound
#print axioms QuantumNLS.Ext025B8BorelCalculus.approx_integral
#print axioms QuantumNLS.Ext025B8BorelCalculus.bounded
#print axioms QuantumNLS.Ext025B8BorelCalculus.bounded_norm
#print axioms QuantumNLS.Ext025B8BorelCalculus.bounded_apply
#print axioms QuantumNLS.Ext025B8BorelCalculus.bounded_simple
#print axioms QuantumNLS.Ext025B8BorelCalculus.bounded_add
#print axioms QuantumNLS.Ext025B8BorelCalculus.bounded_smul
#print axioms QuantumNLS.Ext025B8BorelCalculus.bounded_one
#print axioms QuantumNLS.Ext025B8BorelCalculus.bounded_error_square
#print axioms QuantumNLS.Ext025B8BorelCalculus.bounded_strong

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B8BorelCalculus." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Ext025B8BorelCalculus audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
