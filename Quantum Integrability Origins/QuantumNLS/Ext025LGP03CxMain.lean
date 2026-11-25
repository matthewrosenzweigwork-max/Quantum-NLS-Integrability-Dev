import QuantumNLS.Ext025LGP03Cx
import QuantumNLS.Ext025LGP03

/-!
# EXT-025 GP-03 complexification fix, part 2: `contract_GP03_fixed`

Printed text: FINAL_EXTERNAL_THEOREM_INSTANCES.json (sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782), instance `FIN-EXT025-GP-03`,
lines 3308-3312.  Hypotheses (1) differentiable theorem; (2) "For the analytic version, the real
map admits a holomorphic complexification on a neighborhood. The inverse of its real derivative
complexifies to a bounded inverse. The relevant field or contour variables lie in a smaller
common neighborhood."  Conclusion: "There is a unique local differentiable inverse or implicit
solution. With the stated complexification and uniform local bounds, that solution is
holomorphic and its real restriction is real analytic."

This module replaces the abstract datum of the frozen `Ext025LGP03` (`GP03_C`) and of the
round 27 `Ext025GP03R27m` (`GP03_E_fixed`), which admitted data weaker than a complexification
(round 78 receipt of review record), by the GENUINE datum `IsComplexification`
(`Ext025LGP03Cx`): real Banach spaces `ER, FR` (resp. `P₀, E₀, F₀`) and complex Banach spaces
`EC, FC` (resp. `PC, EC, FC`) with continuous real-linear maps `ι` such that
`(x, y) ↦ ι x + i • ι y` is a topological real-linear isomorphism `X × X ≃L[ℝ] XC`.
Hence `ι` is injective with continuous left inverse `re`, the complex span of `ι X` is `XC`,
and `conj` is a real structure with fixed set `ι X`.

Clause map (one theorem, five conjuncts, as in the frozen reading):
* (A) C^1 inverse over `RCLike 𝕜` with uniqueness: frozen `GP03_A`/`gp03_partA` (no complexification).
* (B) C^1 implicit function over `RCLike 𝕜` with uniqueness: frozen `GP03_B`/`gp03_partB`.
* (C) `GP03_C_gen`: analytic inverse.  Data: genuine complexifications `ιE`, `ιF`; real map
  `f₀` with real derivative `T : ER ≃L[ℝ] FR` at `a`; holomorphic complexification `f'` on a
  neighborhood `V` of `ιE a` extending `f₀` on the real slice near `a`; and the PRINTED
  hypothesis "the inverse of its real derivative complexifies to a bounded inverse":
  a bounded COMPLEX-linear `S : FC →L[ℂ] EC` with `S ∘ ιF = ιE ∘ T⁻¹`.  (No separate complex
  isomorphism `i` is assumed: the complex derivative of `f'` at `ιE a` is derived to be the
  complexification of `T`, with bounded inverse `S`.)  Conclusion: the complex local inverse `G`
  is holomorphic (`DifferentiableOn ℂ` on an open neighbourhood and analytic at the base point),
  its derivative is `S`, two-sided local inverse, unique among left inverses; the real local
  inverse `g` is real analytic with derivative `T⁻¹`, unique among left inverses; and `g` is the
  real restriction of `G` (`ιE ∘ g = G ∘ ιF` near `f₀ a`).
* (D) `GP03_D_gen`: holomorphic implicit function, complex Banach spaces in independent universes.
* (E) `GP03_E_gen`: real-analytic implicit solution from a holomorphic complexification of the
  pair (parameter, unknown): genuine complexifications `ιP, ιE, ιF`; `f₀` and holomorphic `f'`
  on a neighborhood of `(ιP u₀.1, ιE u₀.2)` with `f' (ιP p, ιE e) = ιF (f₀ (p, e))` near `u₀`;
  the real unknown-partial derivative `D_R = fderiv ℝ f₀ u₀ ∘L inr` is a bounded isomorphism and
  its inverse complexifies to a bounded inverse (`S : FC →L[ℂ] EC`, `S ∘ ιF = ιE ∘ D_R⁻¹`).
  Conclusion: the round 27 paired witness `(ψ₀, ψ')`: `ψ₀` real analytic with graph
  characterization and uniqueness among continuous solutions; `ψ'` complex analytic at
  `ιP u₀.1` with the same equation, graph characterization and uniqueness among continuous
  complex solutions; and `ιE ∘ ψ₀ = ψ' ∘ ιP` near `u₀.1`.  The complex partial derivative is
  DERIVED to be invertible (complexification of `D_R` with inverse `S`).

Universes.  All real spaces and all complex spaces live in independent universes
(`analyticAt_gen` lifts through `ULift`).
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace QuantumNLS.Ext025GP03Cx

open QuantumNLS.Ext025L

universe u1 u2 u3 v1 v2 v3

/-- (C): analytic inverse from a genuine holomorphic complexification. -/
def GP03_C_gen : Prop :=
  ∀ (ER : Type u1) (FR : Type u2) (EC : Type v1) (FC : Type v2)
    [NormedAddCommGroup ER] [NormedSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [NormedSpace ℝ FR] [CompleteSpace FR]
    [NormedAddCommGroup EC] [NormedSpace ℂ EC] [CompleteSpace EC]
    [NormedAddCommGroup FC] [NormedSpace ℂ FC] [CompleteSpace FC]
    (ιE : ER →L[ℝ] EC) (ιF : FR →L[ℝ] FC), IsComplexification ιE → IsComplexification ιF →
    ∀ (f₀ : ER → FR) (a : ER) (T : ER ≃L[ℝ] FR), HasFDerivAt f₀ (T : ER →L[ℝ] FR) a →
    ∀ (f' : EC → FC) (V : Set EC), IsOpen V → ιE a ∈ V → DifferentiableOn ℂ f' V →
    (∀ᶠ x in 𝓝 a, f' (ιE x) = ιF (f₀ x)) →
    ∀ (S : FC →L[ℂ] EC), (∀ y, S (ιF y) = ιE (T.symm y)) →
    ∃ (G : FC → EC) (g : FR → ER) (W : Set FC),
      IsOpen W ∧ ιF (f₀ a) ∈ W ∧ DifferentiableOn ℂ G W ∧ AnalyticAt ℂ G (ιF (f₀ a)) ∧
      G (ιF (f₀ a)) = ιE a ∧ HasFDerivAt G S (ιF (f₀ a)) ∧
      (∀ᶠ x in 𝓝 (ιE a), G (f' x) = x) ∧ (∀ᶠ y in 𝓝 (ιF (f₀ a)), f' (G y) = y) ∧
      (∀ G' : FC → EC, (∀ᶠ x in 𝓝 (ιE a), G' (f' x) = x) →
        ∀ᶠ y in 𝓝 (ιF (f₀ a)), G' y = G y) ∧
      AnalyticAt ℝ g (f₀ a) ∧ g (f₀ a) = a ∧ HasFDerivAt g (T.symm : FR →L[ℝ] ER) (f₀ a) ∧
      (∀ᶠ x in 𝓝 a, g (f₀ x) = x) ∧ (∀ᶠ y in 𝓝 (f₀ a), f₀ (g y) = y) ∧
      (∀ g' : FR → ER, (∀ᶠ x in 𝓝 a, g' (f₀ x) = x) → ∀ᶠ y in 𝓝 (f₀ a), g' y = g y) ∧
      (∀ᶠ y in 𝓝 (f₀ a), ιE (g y) = G (ιF y))

theorem gp03_partC_gen : GP03_C_gen.{u1, u2, v1, v2} := by
  intro ER FR EC FC _ _ _ _ _ _ _ _ _ _ _ _ ιE ιF hE hF f₀ a T hT f' V hV haV hf' hext S hS
  have hbase : f' (ιE a) = ιF (f₀ a) := hext.self_of_nhds
  have hdiff : DifferentiableAt ℂ f' (ιE a) := hf'.differentiableAt (hV.mem_nhds haV)
  have hA : AnalyticAt ℂ f' (ιE a) := analyticAt_gen hV hf' haV
  -- real part of the target is the DERIVED retraction `hF.re`
  have h1 : AnalyticAt ℝ (fun x => hF.re (f' (ιE x))) a :=
    (hF.re.analyticAt _).comp (f := fun x => f' (ιE x))
      ((hA.restrictScalars (𝕜 := ℝ)).comp (f := ιE) (ιE.analyticAt a))
  have haf₀ : AnalyticAt ℝ f₀ a := by
    refine h1.congr ?_
    filter_upwards [hext] with x hx
    rw [hx, hF.re_ι]
  -- the complex derivative is the complexification of `T`, with bounded inverse `S`
  have hDι : ∀ x, fderiv ℂ f' (ιE a) (ιE x) = ιF (T x) := fun x => by
    have := deriv_compat ιE ιF hdiff haf₀.differentiableAt hext x
    rwa [hT.fderiv] at this
  have hl : ∀ z, S (fderiv ℂ f' (ιE a) z) = z := fun z => by
    have := hE.ext_ι (L₁ := S.comp (fderiv ℂ f' (ιE a))) (L₂ := ContinuousLinearMap.id ℂ EC)
      (fun x => by simp [hDι, hS])
    exact congrArg (fun L => L z) this
  have hr : ∀ w, fderiv ℂ f' (ιE a) (S w) = w := fun w => by
    have := hF.ext_ι (L₁ := (fderiv ℂ f' (ιE a)).comp S) (L₂ := ContinuousLinearMap.id ℂ FC)
      (fun y => by simp [hDι, hS])
    exact congrArg (fun L => L w) this
  let i : EC ≃L[ℂ] FC := ContinuousLinearEquiv.equivOfInverse (fderiv ℂ f' (ιE a)) S hl hr
  have hi : HasFDerivAt f' (i : EC →L[ℂ] FC) (ιE a) := hdiff.hasFDerivAt
  have hiS : (i.symm : FC →L[ℂ] EC) = S := rfl
  have hs : HasStrictFDerivAt f' (i : EC →L[ℂ] FC) (ιE a) := by
    have := hA.hasStrictFDerivAt
    rwa [hi.fderiv] at this
  have hre : ∀ v, hF.re (ιF v) = v := hF.re_ι
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
  · rw [← hbase, ← hiS]; exact hs.to_localInverse.hasFDerivAt
  · exact hs.eventually_left_inverse
  · rw [← hbase]; exact hs.eventually_right_inverse
  · intro G' hG'
    rw [← hbase]
    exact hs.localInverse_unique hG'
  · exact (hs₀.to_localInverse.hasFDerivAt).congr_of_eventuallyEq hgeq
  · intro g' hg'
    filter_upwards [hs₀.localInverse_unique hg', hgeq] with y h5 h6
    rw [h5, h6]

/-- (D): holomorphic implicit function theorem in complex Banach spaces (independent universes). -/
def GP03_D_gen : Prop :=
  ∀ (P : Type v1) (E : Type v2) (F : Type v3) [NormedAddCommGroup P] [NormedSpace ℂ P]
    [CompleteSpace P] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
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

theorem gp03_partD_gen : GP03_D_gen.{v1, v2, v3} := by
  intro P E F _ _ _ _ _ _ _ _ _ f U hU hf u hu hinv
  have hA : AnalyticAt ℂ f u := analyticAt_gen hU hf hu
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

/-- (E): real-analytic implicit solution from a genuine holomorphic complexification, with the
paired witness `(ψ₀, ψ')`. -/
def GP03_E_gen : Prop :=
  ∀ (P₀ : Type u1) (E₀ : Type u2) (F₀ : Type u3) (PC : Type v1) (EC : Type v2) (FC : Type v3)
    [NormedAddCommGroup P₀] [NormedSpace ℝ P₀] [CompleteSpace P₀]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [CompleteSpace F₀]
    [NormedAddCommGroup PC] [NormedSpace ℂ PC] [CompleteSpace PC]
    [NormedAddCommGroup EC] [NormedSpace ℂ EC] [CompleteSpace EC]
    [NormedAddCommGroup FC] [NormedSpace ℂ FC] [CompleteSpace FC]
    (ιP : P₀ →L[ℝ] PC) (ιE : E₀ →L[ℝ] EC) (ιF : F₀ →L[ℝ] FC),
    IsComplexification ιP → IsComplexification ιE → IsComplexification ιF →
    ∀ (f₀ : P₀ × E₀ → F₀) (u₀ : P₀ × E₀) (f' : PC × EC → FC) (V : Set (PC × EC)),
    IsOpen V → (ιP u₀.1, ιE u₀.2) ∈ V → DifferentiableOn ℂ f' V →
    (∀ᶠ v in 𝓝 u₀, f' (ιP v.1, ιE v.2) = ιF (f₀ v)) →
    (fderiv ℝ f₀ u₀ ∘L ContinuousLinearMap.inr ℝ P₀ E₀).IsInvertible →
    ∀ (S : FC →L[ℂ] EC),
      (∀ y, S (ιF y) = ιE ((fderiv ℝ f₀ u₀ ∘L ContinuousLinearMap.inr ℝ P₀ E₀).inverse y)) →
    ∃ (ψ₀ : P₀ → E₀) (ψ' : PC → EC),
      AnalyticAt ℝ ψ₀ u₀.1 ∧ ψ₀ u₀.1 = u₀.2 ∧ (∀ᶠ p in 𝓝 u₀.1, f₀ (p, ψ₀ p) = f₀ u₀) ∧
      (∀ᶠ v in 𝓝 u₀, f₀ v = f₀ u₀ ↔ ψ₀ v.1 = v.2) ∧
      (∀ χ : P₀ → E₀, ContinuousAt χ u₀.1 → χ u₀.1 = u₀.2 →
        (∀ᶠ p in 𝓝 u₀.1, f₀ (p, χ p) = f₀ u₀) → ∀ᶠ p in 𝓝 u₀.1, χ p = ψ₀ p) ∧
      AnalyticAt ℂ ψ' (ιP u₀.1) ∧ ψ' (ιP u₀.1) = ιE u₀.2 ∧
      (∀ᶠ p in 𝓝 u₀.1, ιE (ψ₀ p) = ψ' (ιP p)) ∧
      (∀ᶠ p in 𝓝 (ιP u₀.1), f' (p, ψ' p) = f' (ιP u₀.1, ιE u₀.2)) ∧
      (∀ᶠ v in 𝓝 (ιP u₀.1, ιE u₀.2),
        f' v = f' (ιP u₀.1, ιE u₀.2) ↔ ψ' v.1 = v.2) ∧
      (∀ χ : PC → EC, ContinuousAt χ (ιP u₀.1) → χ (ιP u₀.1) = ιE u₀.2 →
        (∀ᶠ p in 𝓝 (ιP u₀.1), f' (p, χ p) = f' (ιP u₀.1, ιE u₀.2)) →
        ∀ᶠ p in 𝓝 (ιP u₀.1), χ p = ψ' p)

theorem gp03_partE_gen : GP03_E_gen.{u1, u2, u3, v1, v2, v3} := by
  intro P₀ E₀ F₀ PC EC FC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ιP ιE ιF hP hE hF f₀ u₀ f' V hV hu
    hf' hext hinvR S hS
  set ũ : PC × EC := (ιP u₀.1, ιE u₀.2) with hũ
  have hbase : f' ũ = ιF (f₀ u₀) := hext.self_of_nhds
  have hdiff : DifferentiableAt ℂ f' ũ := hf'.differentiableAt (hV.mem_nhds hu)
  have hAC : AnalyticAt ℂ f' ũ := analyticAt_gen hV hf' hu
  have h1 : AnalyticAt ℝ (fun v : P₀ × E₀ => hF.re (f' (ιP v.1, ιE v.2))) u₀ :=
    (hF.re.analyticAt _).comp (f := fun v : P₀ × E₀ => f' (ιP v.1, ιE v.2))
      ((hAC.restrictScalars (𝕜 := ℝ)).comp (f := fun v : P₀ × E₀ => (ιP v.1, ιE v.2))
        ((ιP.prodMap ιE).analyticAt u₀))
  have haR : AnalyticAt ℝ f₀ u₀ := by
    refine h1.congr ?_
    filter_upwards [hext] with v hv
    rw [hv, hF.re_ι]
  -- the complex partial derivative is the complexification of the real one, inverse `S`
  have hDι : ∀ e : E₀, (fderiv ℂ f' ũ ∘L ContinuousLinearMap.inr ℂ PC EC) (ιE e) =
      ιF ((fderiv ℝ f₀ u₀ ∘L ContinuousLinearMap.inr ℝ P₀ E₀) e) := fun e => by
    have := deriv_compat (ιP.prodMap ιE) ιF (f₀ := f₀) (f' := f') (a := u₀) hdiff
      haR.differentiableAt hext (0, e)
    have h2 : (ιP.prodMap ιE) ((0 : P₀), e) = ((0 : PC), ιE e) := by simp
    rw [h2] at this
    exact this
  obtain ⟨eR, heR⟩ := hinvR
  have hl : ∀ z, S ((fderiv ℂ f' ũ ∘L ContinuousLinearMap.inr ℂ PC EC) z) = z := fun z => by
    have := hE.ext_ι (L₁ := S.comp (fderiv ℂ f' ũ ∘L ContinuousLinearMap.inr ℂ PC EC))
      (L₂ := ContinuousLinearMap.id ℂ EC)
      (fun x => by
        simp only [ContinuousLinearMap.comp_apply, hDι, hS, ← heR]
        simp)
    exact congrArg (fun L => L z) this
  have hr : ∀ w, (fderiv ℂ f' ũ ∘L ContinuousLinearMap.inr ℂ PC EC) (S w) = w := fun w => by
    have := hF.ext_ι (L₁ := (fderiv ℂ f' ũ ∘L ContinuousLinearMap.inr ℂ PC EC).comp S)
      (L₂ := ContinuousLinearMap.id ℂ FC)
      (fun y => by
        simp only [ContinuousLinearMap.comp_apply, hDι, hS, ← heR]
        simp)
    exact congrArg (fun L => L w) this
  have hinvC : (fderiv ℂ f' ũ ∘L ContinuousLinearMap.inr ℂ PC EC).IsInvertible :=
    ⟨ContinuousLinearEquiv.equivOfInverse _ S hl hr, rfl⟩
  have hinvR : (fderiv ℝ f₀ u₀ ∘L ContinuousLinearMap.inr ℝ P₀ E₀).IsInvertible := ⟨eR, heR⟩
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
    cdfC.implicitFunction_apply_self pn hinvC, hrel,
    cdfC.eventually_apply_implicitFunction pn hinvC,
    cdfC.eventually_apply_eq_iff_implicitFunction pn hinvC, ?_⟩
  · intro χ hc hχ0 hr
    have ht : Tendsto (fun p => (p, χ p)) (𝓝 u₀.1) (𝓝 u₀) := by
      have := (continuousAt_id.prodMk hc).tendsto
      simpa [hχ0] using this
    filter_upwards [ht.eventually hiffR, hr] with p h1 h2
    exact (h1.mp h2).symm
  · intro χ hc hχ0 hr
    have ht : Tendsto (fun p => (p, χ p)) (𝓝 ũ.1) (𝓝 ũ) := by
      have := (continuousAt_id.prodMk hc).tendsto
      simpa [hχ0, hũ] using this
    filter_upwards [ht.eventually (cdfC.eventually_apply_eq_iff_implicitFunction pn hinvC), hr]
      with p h1 h2
    exact (h1.mp h2).symm

/-- FIN-EXT025-GP-03 with the genuine complexification datum: all five clauses, with the
paired witness in (E). -/
theorem contract_GP03_fixed :
    GP03_A.{u1, u2} ∧ GP03_B.{u1, u2, u3} ∧ GP03_C_gen.{u1, u2, v1, v2} ∧
      GP03_D_gen.{v1, v2, v3} ∧ GP03_E_gen.{u1, u2, u3, v1, v2, v3} :=
  ⟨gp03_partA, gp03_partB, gp03_partC_gen, gp03_partD_gen, gp03_partE_gen⟩

/-- Non-vacuity of (C): `ℝ ⊂ ℂ`, `f₀ = f' = id`. -/
theorem gp03_C_real_line_instance :
    ∃ (G : ℂ → ℂ) (W : Set ℂ),
      IsOpen W ∧ ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ((id : ℝ → ℝ) 0)) ∈ W ∧
        DifferentiableOn ℂ G W := by
  obtain ⟨G, _, W, hW, hmem, hdG, -⟩ := gp03_partC_gen.{0, 0, 0, 0} ℝ ℝ ℂ ℂ
    Complex.ofRealCLM Complex.ofRealCLM isComplexification_ofReal isComplexification_ofReal
    id 0 (ContinuousLinearEquiv.refl ℝ ℝ) (hasFDerivAt_id _) id Set.univ isOpen_univ
    (Set.mem_univ _) differentiableOn_id (Eventually.of_forall fun _ => rfl)
    (ContinuousLinearMap.id ℂ ℂ) (fun y => rfl)
  exact ⟨G, W, hW, hmem, hdG⟩

/-- Non-vacuity of (E): `ℝ`, `ℂ`, `f₀ (p, e) = e`, `f' (p, e) = e`. -/
theorem gp03_E_real_line_instance :
    ∃ (ψ₀ : ℝ → ℝ) (ψ' : ℂ → ℂ), ψ₀ 0 = 0 ∧ ψ' 0 = 0 := by
  have hI : (fderiv ℝ (fun v : ℝ × ℝ => v.2) ((0 : ℝ), (0 : ℝ)) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    have : fderiv ℝ (fun v : ℝ × ℝ => v.2) ((0 : ℝ), (0 : ℝ)) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ = ContinuousLinearMap.id ℝ ℝ := by
      rw [fderiv_snd]; ext; simp
    rw [this]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℝ, rfl⟩
  have hinv : (fderiv ℝ (fun v : ℝ × ℝ => v.2) ((0 : ℝ), (0 : ℝ)) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).inverse = ContinuousLinearMap.id ℝ ℝ := by
    have : fderiv ℝ (fun v : ℝ × ℝ => v.2) ((0 : ℝ), (0 : ℝ)) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ = ContinuousLinearMap.id ℝ ℝ := by
      rw [fderiv_snd]; ext; simp
    rw [this]
    exact ContinuousLinearMap.inverse_id
  obtain ⟨ψ₀, ψ', -, h0, -, -, -, -, h1, -⟩ := gp03_partE_gen.{0, 0, 0, 0, 0, 0} ℝ ℝ ℝ ℂ ℂ ℂ
    Complex.ofRealCLM Complex.ofRealCLM Complex.ofRealCLM
    isComplexification_ofReal isComplexification_ofReal isComplexification_ofReal
    (fun v : ℝ × ℝ => v.2) (0, 0) (fun v : ℂ × ℂ => v.2) Set.univ isOpen_univ (Set.mem_univ _)
    (differentiableOn_snd) (Eventually.of_forall fun _ => rfl) hI
    (ContinuousLinearMap.id ℂ ℂ) (fun y => by rw [hinv]; rfl)
  exact ⟨ψ₀, ψ', h0, by simpa using h1⟩

end QuantumNLS.Ext025GP03Cx

#print axioms QuantumNLS.Ext025GP03Cx.gp03_partC_gen
#print axioms QuantumNLS.Ext025GP03Cx.gp03_partD_gen
#print axioms QuantumNLS.Ext025GP03Cx.gp03_partE_gen
#print axioms QuantumNLS.Ext025GP03Cx.gp03_C_real_line_instance
#print axioms QuantumNLS.Ext025GP03Cx.gp03_E_real_line_instance
#print axioms QuantumNLS.Ext025GP03Cx.contract_GP03_fixed
