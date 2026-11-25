import QuantumNLS.Ext025AAnalysis
import QuantumNLS.Ext025A5RealAnalytic
import QuantumNLS.HolomorphicStageD3
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# EXT-025 layer A: contract theorem for FIN-EXT025-GP-03

Exact source text (FINAL_EXTERNAL_THEOREM_INSTANCES.json, sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782, instance
`FIN-EXT025-GP-03`, "Banach inverse and implicit functions, with an explicit analytic upgrade"):

* Hypotheses.  (1) "For the differentiable theorem, the map is continuously Frechet
  differentiable on an open subset of real or complex Banach spaces and the relevant
  derivative is a bounded linear isomorphism at the base point."  (2) "For the analytic
  version, the real map admits a holomorphic complexification on a neighborhood. The
  inverse of its real derivative complexifies to a bounded inverse. The relevant field or
  contour variables lie in a smaller common neighborhood."
* Conclusion.  "There is a unique local differentiable inverse or implicit solution. With
  the stated complexification and uniform local bounds, that solution is holomorphic and its
  real restriction is real analytic."
* Application wrapper (descriptive, not a hypothesis): complex C^1 inverse theorem; Cauchy
  formula on complex lines gives the power series; for an implicit equation apply the
  inverse theorem to `(parameter,unknown) ↦ (parameter,equation)`.

Lean reading (one theorem `contract_GP03`, five conjuncts).
* (A) C^1 inverse over `RCLike 𝕜`, `E` Banach: `ContDiffOn 𝕜 1 f U` on an open `U ∋ a`, the
  derivative at `a` an isomorphism `i : E ≃L[𝕜] F`.  Conclusion: a local inverse `g`, C^1 at
  `f a`, derivative `i.symm`, two-sided local inverse, and uniqueness both among left inverses
  and among continuous right inverses.
* (B) C^1 implicit function over `RCLike 𝕜`: the partial derivative in the unknown
  `(fderiv f u ∘L inr)` is a bounded isomorphism; conclusion: a C^1 solution
  `ψ`, derivative formula, graph characterization on a neighbourhood and uniqueness among
  continuous solutions.
* (C) Analytic inverse.  "Holomorphic" is complex Frechet differentiability on an open
  neighbourhood (`DifferentiableOn ℂ`), the weakest reading; the Banach-domain bridge
  holomorphic ⇒ norm-convergent power series is the frozen `HolomorphicStageD3`.  A holomorphic
  complexification is the abstract datum: complex Banach spaces `EC`, `FC` with real-linear
  continuous embeddings `ιE`, `ιF`, a real part `reF` with `reF ∘ ιF = id`, and
  `f̃ : EC → FC` holomorphic near `ιE a` extending the real map `f₀` (`f̃ (ιE x) = ιF (f₀ x)`
  near `a`).  The real derivative `T : ER ≃L[ℝ] FR` of `f₀` at `a` is an isomorphism and the
  derivative of `f̃` at `ιE a` is a bounded complex isomorphism `i : EC ≃L[ℂ] FC` ("the
  inverse of the real derivative complexifies to a bounded inverse").  Conclusion: the
  complex local inverse `G` is holomorphic (differentiable on an open neighbourhood and
  analytic at the base point), the real inverse `g` is real analytic, both unique among left
  inverses, and `ιE ∘ g = G ∘ ιF` near the base point (`g` is the real restriction of `G`).
* (D) Holomorphic implicit function in complex Banach spaces: `f` holomorphic on an open set,
  partial derivative invertible; the solution `ψ` is holomorphic and unique.
* (E) Real-analytic implicit function from a holomorphic complexification of the pair
  `(parameter, unknown)`: the real solution `ψ₀` is real analytic, equals the restriction
  of the complex solution `ψ̃`, and is unique.

Nothing is assumed beyond the printed hypotheses (the abstract complexification datum is
the printed "holomorphic complexification"); no admitted interface; no held identifier.
Banach spaces on which `HolomorphicStageD3` is used are taken in one universe `Type u`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace QuantumNLS.Ext025L

universe u u1 u2 u3 u4

/-- (A): C^1 inverse function theorem with uniqueness. -/
def GP03_A : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (E : Type u1) (F : Type u2) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (U : Set E), IsOpen U → ContDiffOn 𝕜 1 f U → ∀ (a : E), a ∈ U →
    ∀ (i : E ≃L[𝕜] F), HasFDerivAt f (i : E →L[𝕜] F) a →
    ∃ g : F → E, ContDiffAt 𝕜 1 g (f a) ∧ HasFDerivAt g (i.symm : F →L[𝕜] E) (f a) ∧
      g (f a) = a ∧ (∀ᶠ x in 𝓝 a, g (f x) = x) ∧ (∀ᶠ y in 𝓝 (f a), f (g y) = y) ∧
      (∀ g' : F → E, (∀ᶠ x in 𝓝 a, g' (f x) = x) → ∀ᶠ y in 𝓝 (f a), g' y = g y) ∧
      (∀ g' : F → E, ContinuousAt g' (f a) → g' (f a) = a →
        (∀ᶠ y in 𝓝 (f a), f (g' y) = y) → ∀ᶠ y in 𝓝 (f a), g' y = g y)

theorem gp03_partA : GP03_A.{u1, u2} := by
  intro 𝕜 _ E F _ _ _ _ _ f U hU hf a ha i hd
  have hfa : ContDiffAt 𝕜 1 f a := hf.contDiffAt (hU.mem_nhds ha)
  have hs : HasStrictFDerivAt f (i : E →L[𝕜] F) a :=
    hfa.hasStrictFDerivAt' hd (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  refine ⟨hs.localInverse f i a, hfa.to_localInverse hd (by norm_num),
    hs.to_localInverse.hasFDerivAt, hfa.localInverse_apply_image hd (by norm_num),
    hs.eventually_left_inverse, hs.eventually_right_inverse,
    fun g' hg' => hs.localInverse_unique hg', ?_⟩
  intro g' hc h0 hr
  have ht : Tendsto g' (𝓝 (f a)) (𝓝 a) := by
    have := hc.tendsto
    rwa [h0] at this
  filter_upwards [ht.eventually hs.eventually_left_inverse, hr] with y h1 h2
  rw [h2] at h1
  exact h1.symm

/-- (B): C^1 implicit function theorem with uniqueness. -/
def GP03_B : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (P : Type u1) (E : Type u2) (F : Type u3)
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (f : P × E → F) (U : Set (P × E)), IsOpen U → ContDiffOn 𝕜 1 f U →
    ∀ (u : P × E), u ∈ U →
    (fderiv 𝕜 f u ∘L ContinuousLinearMap.inr 𝕜 P E).IsInvertible →
    ∃ ψ : P → E, ContDiffAt 𝕜 1 ψ u.1 ∧ ψ u.1 = u.2 ∧
      HasFDerivAt ψ (-(fderiv 𝕜 f u ∘L ContinuousLinearMap.inr 𝕜 P E).inverse ∘L
        (fderiv 𝕜 f u ∘L ContinuousLinearMap.inl 𝕜 P E)) u.1 ∧
      (∀ᶠ p in 𝓝 u.1, f (p, ψ p) = f u) ∧
      (∀ᶠ v in 𝓝 u, f v = f u ↔ ψ v.1 = v.2) ∧
      (∀ ψ' : P → E, ContinuousAt ψ' u.1 → ψ' u.1 = u.2 →
        (∀ᶠ p in 𝓝 u.1, f (p, ψ' p) = f u) → ∀ᶠ p in 𝓝 u.1, ψ' p = ψ p)

theorem gp03_partB : GP03_B.{u1, u2, u3} := by
  intro 𝕜 _ P E F _ _ _ _ _ _ _ _ _ f U hU hf u hu hinv
  have cdf : ContDiffAt 𝕜 1 f u := hf.contDiffAt (hU.mem_nhds hu)
  have pn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  refine ⟨cdf.implicitFunction pn hinv, cdf.contDiffAt_implicitFunction pn hinv,
    cdf.implicitFunction_apply_self pn hinv,
    (cdf.hasStrictFDerivAt_implicitFunction pn hinv).hasFDerivAt,
    cdf.eventually_apply_implicitFunction pn hinv,
    cdf.eventually_apply_eq_iff_implicitFunction pn hinv, ?_⟩
  intro ψ' hc h0 hr
  have ht : Tendsto (fun p => (p, ψ' p)) (𝓝 u.1) (𝓝 u) := by
    have := (continuousAt_id.prodMk hc).tendsto
    simpa [h0] using this
  filter_upwards [ht.eventually (cdf.eventually_apply_eq_iff_implicitFunction pn hinv), hr]
    with p h1 h2
  exact (h1.mp h2).symm

/-- (C): analytic inverse with an abstract holomorphic complexification. -/
def GP03_C : Prop :=
  ∀ (ER : Type u1) (FR : Type u2) (EC FC : Type u)
    [NormedAddCommGroup ER] [NormedSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [NormedSpace ℝ FR]
    [NormedAddCommGroup EC] [NormedSpace ℂ EC] [CompleteSpace EC]
    [NormedAddCommGroup FC] [NormedSpace ℂ FC] [CompleteSpace FC]
    (ιE : ER →L[ℝ] EC) (ιF : FR →L[ℝ] FC) (reF : FC →L[ℝ] FR), (∀ v, reF (ιF v) = v) →
    ∀ (f₀ : ER → FR) (a : ER) (T : ER ≃L[ℝ] FR), HasFDerivAt f₀ (T : ER →L[ℝ] FR) a →
    ∀ (f' : EC → FC) (V : Set EC), IsOpen V → ιE a ∈ V → DifferentiableOn ℂ f' V →
    (∀ᶠ x in 𝓝 a, f' (ιE x) = ιF (f₀ x)) →
    ∀ (i : EC ≃L[ℂ] FC), HasFDerivAt f' (i : EC →L[ℂ] FC) (ιE a) →
    ∃ (G : FC → EC) (g : FR → ER) (W : Set FC),
      IsOpen W ∧ ιF (f₀ a) ∈ W ∧ DifferentiableOn ℂ G W ∧ AnalyticAt ℂ G (ιF (f₀ a)) ∧
      G (ιF (f₀ a)) = ιE a ∧ HasFDerivAt G (i.symm : FC →L[ℂ] EC) (ιF (f₀ a)) ∧
      (∀ᶠ x in 𝓝 (ιE a), G (f' x) = x) ∧ (∀ᶠ y in 𝓝 (ιF (f₀ a)), f' (G y) = y) ∧
      (∀ G' : FC → EC, (∀ᶠ x in 𝓝 (ιE a), G' (f' x) = x) →
        ∀ᶠ y in 𝓝 (ιF (f₀ a)), G' y = G y) ∧
      AnalyticAt ℝ g (f₀ a) ∧ g (f₀ a) = a ∧ HasFDerivAt g (T.symm : FR →L[ℝ] ER) (f₀ a) ∧
      (∀ᶠ x in 𝓝 a, g (f₀ x) = x) ∧ (∀ᶠ y in 𝓝 (f₀ a), f₀ (g y) = y) ∧
      (∀ g' : FR → ER, (∀ᶠ x in 𝓝 a, g' (f₀ x) = x) → ∀ᶠ y in 𝓝 (f₀ a), g' y = g y) ∧
      (∀ᶠ y in 𝓝 (f₀ a), ιE (g y) = G (ιF y))

theorem gp03_partC : GP03_C.{u1, u2, u} := by
  intro ER FR EC FC _ _ _ _ _ _ _ _ _ _ _ ιE ιF reF hre f₀ a T hT f' V hV haV hf' hext i hi
  have hbase : f' (ιE a) = ιF (f₀ a) := hext.self_of_nhds
  have hA : AnalyticAt ℂ f' (ιE a) :=
    HolomorphicStageD3.analyticAt_of_differentiableOn hV hf' haV
  have hs : HasStrictFDerivAt f' (i : EC →L[ℂ] FC) (ιE a) := by
    have := hA.hasStrictFDerivAt
    rwa [hi.fderiv] at this
  -- real part
  have h1 : AnalyticAt ℝ (fun x => reF (f' (ιE x))) a :=
    (reF.analyticAt _).comp (f := fun x => f' (ιE x))
      ((hA.restrictScalars (𝕜 := ℝ)).comp (f := ιE) (ιE.analyticAt a))
  have haf₀ : AnalyticAt ℝ f₀ a := by
    refine h1.congr ?_
    filter_upwards [hext] with x hx
    rw [hx, hre]
  obtain ⟨g, hgan, hg0, hgl, hgr⟩ := Ext025A.gp03_analytic_inverse (𝕜 := ℝ) T haf₀ hT
  have hs₀ : HasStrictFDerivAt f₀ (T : ER →L[ℝ] FR) a := by
    have := haf₀.hasStrictFDerivAt
    rwa [hT.fderiv] at this
  have hgeq : ∀ᶠ y in 𝓝 (f₀ a), g y = hs₀.localInverse f₀ T a y := hs₀.localInverse_unique hgl
  have hgc : Tendsto g (𝓝 (f₀ a)) (𝓝 a) := by
    have := hgan.continuousAt.tendsto
    rwa [hg0] at this
  have hιc : Tendsto (fun y => ιE (g y)) (𝓝 (f₀ a)) (𝓝 (ιE a)) :=
    (ιE.continuous.tendsto a).comp hgc
  -- complex part
  let G : FC → EC := hs.localInverse f' i (ιE a)
  have hGan : AnalyticAt ℂ G (f' (ιE a)) := Ext025A5.analytic_canonical_inverse i hA hs
  obtain ⟨W, hW, hWo, hWm⟩ := eventually_nhds_iff.mp hGan.eventually_analyticAt
  have hrel : ∀ᶠ y in 𝓝 (f₀ a), ιE (g y) = G (ιF y) := by
    filter_upwards [hgc.eventually hext, hgr, hιc.eventually hs.eventually_left_inverse]
      with y h2 h3 h4
    have h4' : G (f' (ιE (g y))) = ιE (g y) := h4
    rw [← h4', h2, h3]
  refine ⟨G, g, W, hWo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hgan, hg0, ?_, hgl, hgr, ?_, hrel⟩
  · rw [← hbase]; exact hWm
  · exact fun y hy => (hW y hy).differentiableAt.differentiableWithinAt
  · rw [← hbase]; exact hGan
  · rw [← hbase]; exact hs.localInverse_apply_image
  · rw [← hbase]; exact hs.to_localInverse.hasFDerivAt
  · exact hs.eventually_left_inverse
  · rw [← hbase]; exact hs.eventually_right_inverse
  · intro G' hG'
    rw [← hbase]
    exact hs.localInverse_unique hG'
  · exact (hs₀.to_localInverse.hasFDerivAt).congr_of_eventuallyEq hgeq
  · intro g' hg'
    filter_upwards [hs₀.localInverse_unique hg', hgeq] with y h5 h6
    rw [h5, h6]

/-- (D): holomorphic implicit function theorem in complex Banach spaces. -/
def GP03_D : Prop :=
  ∀ (P E F : Type u) [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : P × E → F) (U : Set (P × E)), IsOpen U → DifferentiableOn ℂ f U →
    ∀ (u : P × E), u ∈ U →
    (fderiv ℂ f u ∘L ContinuousLinearMap.inr ℂ P E).IsInvertible →
    ∃ (ψ : P → E) (W : Set P), IsOpen W ∧ u.1 ∈ W ∧ DifferentiableOn ℂ ψ W ∧
      AnalyticAt ℂ ψ u.1 ∧ ψ u.1 = u.2 ∧
      HasFDerivAt ψ (-(fderiv ℂ f u ∘L ContinuousLinearMap.inr ℂ P E).inverse ∘L
        (fderiv ℂ f u ∘L ContinuousLinearMap.inl ℂ P E)) u.1 ∧
      (∀ᶠ p in 𝓝 u.1, f (p, ψ p) = f u) ∧
      (∀ᶠ v in 𝓝 u, f v = f u ↔ ψ v.1 = v.2) ∧
      (∀ ψ' : P → E, ContinuousAt ψ' u.1 → ψ' u.1 = u.2 →
        (∀ᶠ p in 𝓝 u.1, f (p, ψ' p) = f u) → ∀ᶠ p in 𝓝 u.1, ψ' p = ψ p)

theorem gp03_partD : GP03_D.{u} := by
  intro P E F _ _ _ _ _ _ _ _ _ f U hU hf u hu hinv
  have hA : AnalyticAt ℂ f u := HolomorphicStageD3.analyticAt_of_differentiableOn hU hf hu
  have cdf : ContDiffAt ℂ ω f u := hA.contDiffAt
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hψ : ContDiffAt ℂ ω (cdf.implicitFunction pn hinv) u.1 :=
    cdf.contDiffAt_implicitFunction pn hinv
  have hψa : AnalyticAt ℂ (cdf.implicitFunction pn hinv) u.1 := hψ.analyticAt
  obtain ⟨W, hW, hWo, hWm⟩ := eventually_nhds_iff.mp hψa.eventually_analyticAt
  refine ⟨cdf.implicitFunction pn hinv, W, hWo, hWm,
    fun y hy => (hW y hy).differentiableAt.differentiableWithinAt, hψa,
    cdf.implicitFunction_apply_self pn hinv,
    (cdf.hasStrictFDerivAt_implicitFunction pn hinv).hasFDerivAt,
    cdf.eventually_apply_implicitFunction pn hinv,
    cdf.eventually_apply_eq_iff_implicitFunction pn hinv, ?_⟩
  intro ψ' hc h0 hr
  have ht : Tendsto (fun p => (p, ψ' p)) (𝓝 u.1) (𝓝 u) := by
    have := (continuousAt_id.prodMk hc).tendsto
    simpa [h0] using this
  filter_upwards [ht.eventually (cdf.eventually_apply_eq_iff_implicitFunction pn hinv), hr]
    with p h1 h2
  exact (h1.mp h2).symm

/-- (E): real-analytic implicit solution with a holomorphic complexification. -/
def GP03_E : Prop :=
  ∀ (P₀ : Type u1) (E₀ : Type u2) (F₀ : Type u3) (PC EC FC : Type u)
    [NormedAddCommGroup P₀] [NormedSpace ℝ P₀] [CompleteSpace P₀]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [CompleteSpace F₀]
    [NormedAddCommGroup PC] [NormedSpace ℂ PC] [CompleteSpace PC]
    [NormedAddCommGroup EC] [NormedSpace ℂ EC] [CompleteSpace EC]
    [NormedAddCommGroup FC] [NormedSpace ℂ FC] [CompleteSpace FC]
    (ιP : P₀ →L[ℝ] PC) (ιE : E₀ →L[ℝ] EC) (ιF : F₀ →L[ℝ] FC) (reF : FC →L[ℝ] F₀),
    (∀ v, reF (ιF v) = v) →
    ∀ (f₀ : P₀ × E₀ → F₀) (u₀ : P₀ × E₀) (f' : PC × EC → FC) (V : Set (PC × EC)),
    IsOpen V → (ιP u₀.1, ιE u₀.2) ∈ V → DifferentiableOn ℂ f' V →
    (∀ᶠ v in 𝓝 u₀, f' (ιP v.1, ιE v.2) = ιF (f₀ v)) →
    (fderiv ℂ f' (ιP u₀.1, ιE u₀.2) ∘L ContinuousLinearMap.inr ℂ PC EC).IsInvertible →
    (fderiv ℝ f₀ u₀ ∘L ContinuousLinearMap.inr ℝ P₀ E₀).IsInvertible →
    ∃ (ψ₀ : P₀ → E₀) (ψ' : PC → EC),
      AnalyticAt ℝ ψ₀ u₀.1 ∧ ψ₀ u₀.1 = u₀.2 ∧ (∀ᶠ p in 𝓝 u₀.1, f₀ (p, ψ₀ p) = f₀ u₀) ∧
      (∀ᶠ v in 𝓝 u₀, f₀ v = f₀ u₀ ↔ ψ₀ v.1 = v.2) ∧
      (∀ χ : P₀ → E₀, ContinuousAt χ u₀.1 → χ u₀.1 = u₀.2 →
        (∀ᶠ p in 𝓝 u₀.1, f₀ (p, χ p) = f₀ u₀) → ∀ᶠ p in 𝓝 u₀.1, χ p = ψ₀ p) ∧
      AnalyticAt ℂ ψ' (ιP u₀.1) ∧ ψ' (ιP u₀.1) = ιE u₀.2 ∧
      (∀ᶠ p in 𝓝 u₀.1, ιE (ψ₀ p) = ψ' (ιP p))

theorem gp03_partE : GP03_E.{u1, u2, u3, u} := by
  intro P₀ E₀ F₀ PC EC FC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ιP ιE ιF reF hre f₀ u₀ f' V hV hu hf'
    hext hinvC hinvR
  set ũ : PC × EC := (ιP u₀.1, ιE u₀.2) with hũ
  have hbase : f' ũ = ιF (f₀ u₀) := hext.self_of_nhds
  have hAC : AnalyticAt ℂ f' ũ := HolomorphicStageD3.analyticAt_of_differentiableOn hV hf' hu
  have h1 : AnalyticAt ℝ (fun v : P₀ × E₀ => reF (f' (ιP v.1, ιE v.2))) u₀ :=
    (reF.analyticAt _).comp (f := fun v : P₀ × E₀ => f' (ιP v.1, ιE v.2))
      ((hAC.restrictScalars (𝕜 := ℝ)).comp (f := fun v : P₀ × E₀ => (ιP v.1, ιE v.2))
        ((ιP.prodMap ιE).analyticAt u₀))
  have haR : AnalyticAt ℝ f₀ u₀ := by
    refine h1.congr ?_
    filter_upwards [hext] with v hv
    rw [hv, hre]
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have cdfR : ContDiffAt ℝ ω f₀ u₀ := haR.contDiffAt
  have cdfC : ContDiffAt ℂ ω f' ũ := hAC.contDiffAt
  have hψR : ContDiffAt ℝ ω (cdfR.implicitFunction pn hinvR) u₀.1 :=
    cdfR.contDiffAt_implicitFunction pn hinvR
  have hψC : ContDiffAt ℂ ω (cdfC.implicitFunction pn hinvC) ũ.1 :=
    cdfC.contDiffAt_implicitFunction pn hinvC
  set ψ₀ := cdfR.implicitFunction pn hinvR with hψ₀
  set ψC := cdfC.implicitFunction pn hinvC with hψCdef
  have h0 : ψ₀ u₀.1 = u₀.2 := cdfR.implicitFunction_apply_self pn hinvR
  have hreal : ∀ᶠ p in 𝓝 u₀.1, f₀ (p, ψ₀ p) = f₀ u₀ :=
    cdfR.eventually_apply_implicitFunction pn hinvR
  have hiffR := cdfR.eventually_apply_eq_iff_implicitFunction pn hinvR
  have htend : Tendsto (fun p => (p, ψ₀ p)) (𝓝 u₀.1) (𝓝 u₀) := by
    have := (continuousAt_id.prodMk hψR.continuousAt).tendsto
    simpa [h0] using this
  have htend' : Tendsto (fun p => (ιP p, ιE (ψ₀ p))) (𝓝 u₀.1) (𝓝 ũ) := by
    have h2 : Tendsto (fun p => (ιP p, ιE (ψ₀ p))) (𝓝 u₀.1) (𝓝 (ιP u₀.1, ιE (ψ₀ u₀.1))) :=
      ((ιP.continuous.tendsto _).prodMk_nhds
        ((ιE.continuous.tendsto _).comp hψR.continuousAt.tendsto))
    simpa [h0, hũ] using h2
  have hrel : ∀ᶠ p in 𝓝 u₀.1, ιE (ψ₀ p) = ψC (ιP p) := by
    filter_upwards [htend.eventually hext, hreal,
      htend'.eventually (cdfC.eventually_apply_eq_iff_implicitFunction pn hinvC)]
      with p h2 h3 h4
    have h5 : f' (ιP p, ιE (ψ₀ p)) = f' ũ := by
      rw [h2, hbase]
      simp only [h3]
    exact (h4.mp h5).symm
  refine ⟨ψ₀, ψC, hψR.analyticAt, h0, hreal, hiffR, ?_, hψC.analyticAt,
    cdfC.implicitFunction_apply_self pn hinvC, hrel⟩
  intro χ hc hχ0 hr
  have ht : Tendsto (fun p => (p, χ p)) (𝓝 u₀.1) (𝓝 u₀) := by
    have := (continuousAt_id.prodMk hc).tendsto
    simpa [hχ0] using this
  filter_upwards [ht.eventually hiffR, hr] with p h1 h2
  exact (h1.mp h2).symm

/-- FIN-EXT025-GP-03 as a Lean theorem (all clauses). -/
theorem contract_GP03 :
    GP03_A.{u1, u2} ∧ GP03_B.{u1, u2, u3} ∧ GP03_C.{u1, u2, u} ∧ GP03_D.{u} ∧
      GP03_E.{u1, u2, u3, u} :=
  ⟨gp03_partA, gp03_partB, gp03_partC, gp03_partD, gp03_partE⟩

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_GP03
