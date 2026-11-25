import Mathlib

/-!
# Compact operators: Fredholm alternative and analytic families (library piece L7 of campaign E01)

Local re-proof from Mathlib (E01-D8: no external code).

## Mathlib inputs (verified at the pinned commit)

* `isClosed_setOfPred_isCompactOperator` (`Mathlib/Analysis/Normed/Operator/Compact/Basic.lean`):
  `{f | IsCompactOperator f}` is closed in `M₁ →SL[σ] M₂` when `M₂` is complete.  (The old name
  `isClosed_setOf_isCompactOperator` is a deprecated alias.)
* `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`
  (`.../Compact/FredholmAlternative.lean`): for compact `T` on a Banach space and `μ ≠ 0`, either
  `μ` is an eigenvalue or `μ` is in the resolvent set.
* `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`: identity theorem.
* `Submodule.Quotient.normedAddCommGroup` (quotient by a closed subspace) replaces Hahn-Banach:
  the Calkin-type quotient `𝓛(X,Y) ⧸ 𝒦(X,Y)` is a normed space and the quotient map is a
  continuous linear map, so the identity theorem applies to `q ∘ G`.

## Main results

* `isCompact_of_analytic_of_open` (plan §6.1 L7): an analytic family `G : E → (X →L[𝕜] Y)` over a
  preconnected domain that is compact on a nonempty open set is compact everywhere.
* `isUnit_one_add_of_injective`, `bijective_of_one_add_compact` (plan §6.1 L7): Fredholm
  alternative for `B + K`, `B` an isomorphism, `K` compact, `B + K` injective.
* `lemmaF7_bijective` and `lemmaF7_of_bilinear`: the form of the book's Lemma F.7 (Grébert-Kappeler,
  Appendix F), see the comment before `lemmaF7_bijective` for exactly how it relates to the book.
-/

set_option autoImplicit false

open Set Filter Topology

namespace NlsGge.GK38.Lib

noncomputable section

/-! ### Part 1: analytic families of operators, compact on an open set -/

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

/-- The set of compact operators `X →L[𝕜] Y` is closed (`Y` complete): a restatement of
`isClosed_setOfPred_isCompactOperator` in the form used below. -/
theorem isClosed_compactOperator : IsClosed {A : X →L[𝕜] Y | IsCompactOperator A} :=
  isClosed_setOfPred_isCompactOperator

/-- **Analytic continuation of membership in a closed subspace.**  If `G : E → V` is analytic on a
preconnected space `E` with values in a normed space `V`, `M ⊆ V` is a closed subspace and `G x ∈ M`
for all `x` in a nonempty open set, then `G x ∈ M` for every `x`.

Proof: `V ⧸ M` is a normed space (`M` closed) and the quotient map `q` is a continuous linear map,
so `q ∘ G` is analytic and vanishes on the open set, hence everywhere by the identity theorem.
(This replaces a Hahn-Banach separation argument.) -/
theorem mem_of_analytic_of_open {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [PreconnectedSpace E] (G : E → V) (hG : AnalyticOnNhd 𝕜 G univ) (M : Submodule 𝕜 V)
    (hM : IsClosed (M : Set V)) (U : Set E) (hU : IsOpen U) (hne : U.Nonempty)
    (hc : ∀ x ∈ U, G x ∈ M) : ∀ x, G x ∈ M := by
  have : IsClosed (M : Set V) := hM
  have hn : ∀ v : V, ‖M.mkQ v‖ ≤ 1 * ‖v‖ := fun v => by
    rw [one_mul]; exact Submodule.Quotient.norm_mk_le M v
  let q : V →L[𝕜] (V ⧸ M) := LinearMap.mkContinuous M.mkQ 1 hn
  have hq : ∀ v, q v = 0 ↔ v ∈ M := fun v => Submodule.Quotient.mk_eq_zero M
  have hqG : AnalyticOnNhd 𝕜 (fun x => q (G x)) univ := fun x hx =>
    (q.analyticAt _).comp (hG x hx)
  obtain ⟨z, hz⟩ := hne
  have hz0 : (fun x => q (G x)) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hU.mem_nhds hz] with x hx
    exact (hq _).2 (hc x hx)
  have h0 := hqG.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ z) hz0
  intro x
  exact (hq _).1 (h0 (mem_univ x))

/-- **Analytic continuation of compactness.**  If `G : E → 𝓛(X, Y)` is analytic on the whole of a
preconnected space `E` and `G x` is a compact operator for all `x` in a nonempty open set `U`, then
`G x` is compact for every `x`.  (`𝒦 = {compact operators}` is a closed subspace of `𝓛(X, Y)`
by `isClosed_compactOperator`; apply `mem_of_analytic_of_open`.) -/
theorem isCompact_of_analytic_of_open [PreconnectedSpace E] (G : E → (X →L[𝕜] Y))
    (hG : AnalyticOnNhd 𝕜 G univ) (U : Set E) (hU : IsOpen U) (hne : U.Nonempty)
    (hc : ∀ x ∈ U, IsCompactOperator (G x)) : ∀ x, IsCompactOperator (G x) := fun x =>
  mem_of_analytic_of_open (M := compactOperator (RingHom.id 𝕜) X Y) G hG
    (isClosed_compactOperator) U hU hne hc x

end Analytic

/-! ### Part 2: Fredholm alternative -/

section Fredholm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- **Fredholm alternative, `1 + K` form.**  If `K` is compact and `1 + K` is injective on a Banach
space, then `1 + K` is invertible in `𝓛(X)`. -/
theorem isUnit_one_add_of_injective {K : X →L[𝕜] X} (hK : IsCompactOperator K)
    (h : Function.Injective ((1 : X →L[𝕜] X) + K)) : IsUnit ((1 : X →L[𝕜] X) + K) := by
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet hK (μ := (-1 : 𝕜))
    (neg_ne_zero.2 one_ne_zero) with hev | hres
  · exfalso
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hv' : K v = -v := by
      have := hv.apply_eq_smul
      simpa using this
    apply hv.2
    apply h
    simp [hv']
  · have hu : IsUnit (algebraMap 𝕜 (X →L[𝕜] X) (-1) - K) := spectrum.mem_resolventSet_iff.1 hres
    have heq : algebraMap 𝕜 (X →L[𝕜] X) (-1) - K = -((1 : X →L[𝕜] X) + K) := by
      simp [sub_eq_add_neg, add_comm]
    rw [heq] at hu
    exact (IsUnit.neg_iff _).1 hu

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **Fredholm alternative (plan §6.1 L7).**  Let `B : X ≃L Y` be an isomorphism, `K : X →L Y`
compact and `A = B + K` injective.  Then `A` is a continuous linear isomorphism: there is
`e : X ≃L[𝕜] Y` with `⇑e = B + K`; in particular `B + K` is bijective. -/
theorem bijective_of_one_add_compact (B : X ≃L[𝕜] Y) (K : X →L[𝕜] Y) (hK : IsCompactOperator K)
    (hinj : Function.Injective ((B : X →L[𝕜] Y) + K)) :
    ∃ e : X ≃L[𝕜] Y, (e : X → Y) = ⇑((B : X →L[𝕜] Y) + K) := by
  -- `A = B ∘ (1 + B⁻¹ K)`
  have hK' : IsCompactOperator ((B.symm : Y →L[𝕜] X).comp K) := hK.clm_comp B.symm.toContinuousLinearMap
  have hinj' : Function.Injective ((1 : X →L[𝕜] X) + (B.symm : Y →L[𝕜] X).comp K) := by
    intro x y hxy
    apply hinj
    have := congrArg (fun z => B z) hxy
    simpa [map_add] using this
  obtain ⟨u, hu⟩ := isUnit_one_add_of_injective hK' hinj'
  refine ⟨(ContinuousLinearEquiv.unitsEquiv 𝕜 X u).trans B, ?_⟩
  ext x
  have hux : (u : X →L[𝕜] X) x = x + B.symm (K x) := by
    rw [hu]; simp
  simp [ContinuousLinearEquiv.unitsEquiv_apply, hux, map_add]

/-- Boolean form of `bijective_of_one_add_compact`. -/
theorem bijective_of_one_add_compact' (B : X ≃L[𝕜] Y) (K : X →L[𝕜] Y) (hK : IsCompactOperator K)
    (hinj : Function.Injective ((B : X →L[𝕜] Y) + K)) :
    Function.Bijective ((B : X →L[𝕜] Y) + K) := by
  obtain ⟨e, he⟩ := bijective_of_one_add_compact B K hK hinj
  rw [← he]
  exact e.bijective

end Fredholm

/-! ### Part 3: the form of the book's Lemma F.7 -/

section LemmaF7

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {ι : Type*}

/-- **Lemma F.7 (Grébert-Kappeler book, Appendix F), abstract form with biorthogonal functionals.**

Book statement: let `(d^±_n)` be a basis of `L²_r`, `A` a compact perturbation of the identity and
`b^±_n = A d^±_n`.  If only the brackets `⟨b⁺_n, J b⁻_n⟩` and `⟨b⁻_n, J b⁺_n⟩` do not vanish, then
`A` is a linear isomorphism of `L²_r` and `(b^±_n)` is a basis.

Here: `E` is a Banach space, `A : E →L E` with `A - 1` compact, `d : ι → E` a family with
unconditional expansions (`hd`: every `h` is `∑ ξ_k d_k` in the `HasSum` sense), and
`ψ : ι → E →L 𝕜` continuous functionals.  The book's functionals are `ψ_j = ⟨·, K b_j⟩`, and its
hypothesis on brackets is: `ψ_j (A d_k)` is nonzero for `k = σ j` and zero for `k ≠ σ j`
(`hψ`, in the form: every `d_k` has a functional `ψ_j` that sees exactly it among the `A d_k'`).
Conclusion: `A` is a continuous linear isomorphism and `(A d_k)` has the same kind of expansions.

*Deviation from the book (stated for K10).*  The book defines "basis" by (a) closed span is the
whole space and (b) minimality, but its proof expands `h = ∑ ξ_k d_k` and pairs termwise, which needs
a Schauder basis (unconditional convergence of the `ℤ`-indexed series).  `hd` is that hypothesis.  It
holds for the `d^±_n` of Prop. 10.9 / Thm. 19.1 because they are explicit combinations of the
orthonormal Fourier exponentials `e^±_n` (a Hilbert basis, hence unconditional). -/
theorem lemmaF7_bijective (A : E →L[𝕜] E) (hA : IsCompactOperator (A - 1 : E →L[𝕜] E))
    (d : ι → E) (hd : ∀ h : E, ∃ ξ : ι → 𝕜, HasSum (fun k => ξ k • d k) h)
    (ψ : ι → (E →L[𝕜] 𝕜))
    (hψ : ∀ k, ∃ j, ψ j (A (d k)) ≠ 0 ∧ ∀ k', k' ≠ k → ψ j (A (d k')) = 0) :
    (∃ e : E ≃L[𝕜] E, (e : E → E) = ⇑A) ∧
      ∀ h : E, ∃ ξ : ι → 𝕜, HasSum (fun k => ξ k • A (d k)) h := by
  have hinj : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro h hAh
    obtain ⟨ξ, hξ⟩ := hd h
    have hsum : HasSum (fun k => ξ k • A (d k)) 0 := by
      have := hξ.mapL A
      simpa [hAh] using this
    have hξ0 : ∀ k, ξ k = 0 := by
      intro k
      obtain ⟨j, hj1, hj2⟩ := hψ k
      have h2 : HasSum (fun k' => ξ k' * ψ j (A (d k'))) 0 := by
        have := hsum.mapL (ψ j)
        simpa using this
      have h3 : HasSum (fun k' => ξ k' * ψ j (A (d k'))) (ξ k * ψ j (A (d k))) :=
        hasSum_single k (fun k' hk' => by rw [hj2 k' hk', mul_zero])
      have := h3.unique h2
      exact (mul_eq_zero.1 this).resolve_right hj1
    have : (fun k => ξ k • d k) = fun _ => (0 : E) := by
      funext k; rw [hξ0 k, zero_smul]
    rw [this] at hξ
    exact hξ.unique hasSum_zero
  have hA' : A = (1 : E ≃L[𝕜] E) + (A - 1) := by
    ext x; simp
  obtain ⟨e, he⟩ := bijective_of_one_add_compact (1 : E ≃L[𝕜] E) (A - 1 : E →L[𝕜] E) hA
    (by
      have : ((1 : E ≃L[𝕜] E) : E →L[𝕜] E) + (A - 1) = A := by ext x; simp
      rwa [this])
  have he' : (e : E → E) = ⇑A := by
    rw [he]; ext x; simp
  refine ⟨⟨e, he'⟩, fun h => ?_⟩
  obtain ⟨ξ, hξ⟩ := hd (e.symm h)
  refine ⟨ξ, ?_⟩
  have := hξ.mapL (e : E →L[𝕜] E)
  simpa [he'] using this

/-- **Lemma F.7, bilinear-bracket form (what K10 consumes).**  Let `B : E →L E →L 𝕜` be a continuous
bilinear form (in the book: `B f g = i⟨f, J g⟩_r`, i.e. `⟨f, K g⟩_r` with `K = iJ`, which is
real-valued on `L²_r`), `σ : ι → ι` an involution (in the book `σ(±, n) = (∓, n)`), and put
`b_k = A d_k`.  If the only nonvanishing brackets `B (b_k) (b_j)` are the ones with `j = σ k`, and
those do not vanish, then `A` is an isomorphism and `(b_k)` expands every vector. -/
theorem lemmaF7_of_bilinear (A : E →L[𝕜] E) (hA : IsCompactOperator (A - 1 : E →L[𝕜] E))
    (d : ι → E) (hd : ∀ h : E, ∃ ξ : ι → 𝕜, HasSum (fun k => ξ k • d k) h)
    (B : E →L[𝕜] E →L[𝕜] 𝕜) (σ : ι → ι) (hσ : Function.Involutive σ)
    (hB0 : ∀ k j, B (A (d k)) (A (d j)) ≠ 0 → j = σ k)
    (hB1 : ∀ k, B (A (d k)) (A (d (σ k))) ≠ 0) :
    (∃ e : E ≃L[𝕜] E, (e : E → E) = ⇑A) ∧
      ∀ h : E, ∃ ξ : ι → 𝕜, HasSum (fun k => ξ k • A (d k)) h := by
  refine lemmaF7_bijective A hA d hd (fun j => B.flip (A (d j))) ?_
  intro k
  refine ⟨σ k, hB1 k, fun k' hk' => ?_⟩
  by_contra hne
  have := hB0 k' (σ k) hne
  exact hk' (by rw [← hσ k', ← this, hσ k])

end LemmaF7

end

end NlsGge.GK38.Lib
