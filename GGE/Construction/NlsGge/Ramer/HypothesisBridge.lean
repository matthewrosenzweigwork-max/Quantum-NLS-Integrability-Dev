import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.Module.Equiv
import NlsGge.Sobolev.CMInclusionBasisIndependent

/-!
# From the v2 hypotheses to Ramer's hypotheses (1)–(3)

Ramer, J. Funct. Anal. 15 (1974), Section 1, assumes for `T = I + K` on `U ⊆ E`:

1. `T` is a homeomorphism of `U` onto an open set;
2. `K(U) ⊂ H` and `K : U → H` is continuous;
3. `K` is `H − C¹`; its `H`-derivative `DK(x)` is Hilbert–Schmidt, continuous in
   the Hilbert–Schmidt norm, and `I_H + DK(x) ∈ GL(H)`.

Ramer's Section 6(A), condition (3″), says that (3) follows from `K : U → H`
being `C¹`, together with invertibility, by his Lemma 2.1(i):
`L(E, H) ↪ HS(H)`, `A ↦ A ∘ i`. This file proves that bridge in the setting of
v2 (`prop:gaussiancommon`): `E` and `H` are real inner product spaces, the
inclusion `i : H → E` is injective and Hilbert–Schmidt, `T` is a homeomorphism
of `E`, and `T = id + i ∘ K`, `T⁻¹ = id + i ∘ K'` with `K, K' : E → H` of class
`C¹`. That last condition is implied by v2's real analyticity
(`contDiff_one_of_analytic`).

"Hilbert–Schmidt" is expressed against an arbitrary Hilbert basis `b` of `H`, as
summability of `n ↦ ‖A (b n)‖²`. The theorem holds for every basis, so no
basis-independence lemma is needed. It is NOT the sibling package's real HS
type. The integrator must connect the two through that package's
basis-independence theorem.

The last section instantiates the hypotheses with the actual inclusion
`cmToFullWeightedHilbert c s : H → E_s`, `1/2 < s`, of checkpoint 20.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace NlsGge.Ramer

section Abstract

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type*}

/-- **Ramer, Lemma 2.1(i), Hilbert case.** If `i : H → E` is Hilbert–Schmidt for a
Hilbert basis `b`, then for every bounded `A : E → H` the composite `A ∘ i` is
Hilbert–Schmidt on `H`, with `Σ ‖A i bₙ‖² ≤ ‖A‖² Σ ‖i bₙ‖²`. -/
theorem hs_comp_left (i : H →L[ℝ] E) (b : HilbertBasis ι ℝ H)
    (hi : Summable fun n => ‖i (b n)‖ ^ 2) (A : E →L[ℝ] H) :
    Summable (fun n => ‖(A.comp i) (b n)‖ ^ 2) ∧
      ∑' n, ‖(A.comp i) (b n)‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑' n, ‖i (b n)‖ ^ 2 := by
  have hle : ∀ n, ‖(A.comp i) (b n)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖i (b n)‖ ^ 2 := by
    intro n
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
  have hs : Summable (fun n => ‖(A.comp i) (b n)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle (hi.mul_left _)
  refine ⟨hs, ?_⟩
  calc ∑' n, ‖(A.comp i) (b n)‖ ^ 2 ≤ ∑' n, ‖A‖ ^ 2 * ‖i (b n)‖ ^ 2 :=
        hs.tsum_le_tsum hle (hi.mul_left _)
    _ = ‖A‖ ^ 2 * ∑' n, ‖i (b n)‖ ^ 2 := tsum_mul_left

variable (i : H →L[ℝ] E)

/-- Derivative of `T = id + i ∘ K`. -/
theorem hasFDerivAt_id_add_comp (K : E → H) (x : E) (hK : DifferentiableAt ℝ K x) :
    HasFDerivAt (fun y => y + i (K y))
      (ContinuousLinearMap.id ℝ E + i.comp (fderiv ℝ K x)) x :=
  (hasFDerivAt_id x).add (i.hasFDerivAt.comp x hK.hasFDerivAt)

/-- **Ramer, Section 6(A), (3″) ⇒ H-differentiability.** If `K : E → H` is
Fréchet differentiable at `x`, then `h ↦ K(x + i h)` is Fréchet differentiable
at `0` in `H`, with `H`-derivative `D_E K(x) ∘ i`. -/
theorem hasFDerivAt_H_direction (K : E → H) (x : E) (hK : DifferentiableAt ℝ K x) :
    HasFDerivAt (fun h : H => K (x + i h)) ((fderiv ℝ K x).comp i) 0 := by
  have hin : HasFDerivAt (fun h : H => x + i h) i 0 := by
    simpa using (i.hasFDerivAt (x := (0 : H))).const_add x
  have hKx : HasFDerivAt K (fderiv ℝ K x) (x + i 0) := by
    simpa using hK.hasFDerivAt
  exact hKx.comp (0 : H) hin

/-- Chain-rule identity on `H` from one-sided inverse identities on `E`.
If `(I + i B')(I + i B) = I_E` and `i` is injective, then
`(I_H + B' i)(I_H + B i) = I_H`. -/
theorem H_leftInverse_of_E (hinj : Function.Injective i) (B B' : E →L[ℝ] H)
    (hE : (ContinuousLinearMap.id ℝ E + i.comp B').comp
      (ContinuousLinearMap.id ℝ E + i.comp B) = ContinuousLinearMap.id ℝ E) (h : H) :
    (ContinuousLinearMap.id ℝ H + B'.comp i) ((ContinuousLinearMap.id ℝ H + B.comp i) h) = h := by
  apply hinj
  have := congrArg (fun L : E →L[ℝ] E => L (i h)) hE
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_add] at this ⊢
  exact this

/-- **Ramer (3), invertibility.** Let `T` be a homeomorphism of `E` with
`T = id + i ∘ K`, `T⁻¹ = id + i ∘ K'`, where `K, K'` are differentiable and `i`
is injective. Then `I_H + D_E K(x) ∘ i` is a continuous linear equivalence of
`H`. Its inverse is `I_H + D_E K'(T x) ∘ i`, the restriction of `D(T⁻¹)(T x)`. -/
theorem exists_inverse_id_add_HDeriv (hinj : Function.Injective i)
    (T : E ≃ₜ E) (K K' : E → H)
    (hT : ∀ x, T x = x + i (K x)) (hTs : ∀ y, T.symm y = y + i (K' y))
    (hK : Differentiable ℝ K) (hK' : Differentiable ℝ K') (x : E) :
    ∃ L : H ≃L[ℝ] H,
      (L : H →L[ℝ] H) = ContinuousLinearMap.id ℝ H + (fderiv ℝ K x).comp i ∧
      ((L.symm : H ≃L[ℝ] H) : H →L[ℝ] H) =
        ContinuousLinearMap.id ℝ H + (fderiv ℝ K' (T x)).comp i := by
  have hTf : (T : E → E) = fun y => y + i (K y) := funext hT
  have hTsf : (T.symm : E → E) = fun y => y + i (K' y) := funext hTs
  set B := fderiv ℝ K x
  set B' := fderiv ℝ K' (T x)
  have dT : HasFDerivAt (T : E → E) (ContinuousLinearMap.id ℝ E + i.comp B) x := by
    rw [hTf]; exact hasFDerivAt_id_add_comp i K x (hK x)
  have dTs : HasFDerivAt (T.symm : E → E) (ContinuousLinearMap.id ℝ E + i.comp B') (T x) := by
    rw [hTsf]; exact hasFDerivAt_id_add_comp i K' (T x) (hK' (T x))
  -- T⁻¹ ∘ T = id at x
  have h1 : (ContinuousLinearMap.id ℝ E + i.comp B').comp
      (ContinuousLinearMap.id ℝ E + i.comp B) = ContinuousLinearMap.id ℝ E := by
    have hc := dTs.comp x dT
    have hid : HasFDerivAt ((T.symm : E → E) ∘ T) (ContinuousLinearMap.id ℝ E) x := by
      have : ((T.symm : E → E) ∘ T) = id := by funext y; simp
      rw [this]; exact hasFDerivAt_id x
    exact hc.unique hid
  -- T ∘ T⁻¹ = id at T x; note T⁻¹ (T x) = x
  have h2 : (ContinuousLinearMap.id ℝ E + i.comp B).comp
      (ContinuousLinearMap.id ℝ E + i.comp B') = ContinuousLinearMap.id ℝ E := by
    have dT' : HasFDerivAt (T : E → E) (ContinuousLinearMap.id ℝ E + i.comp B)
        (T.symm (T x)) := by simpa using dT
    have hc := dT'.comp (T x) dTs
    have hid : HasFDerivAt ((T : E → E) ∘ T.symm) (ContinuousLinearMap.id ℝ E) (T x) := by
      have : ((T : E → E) ∘ T.symm) = id := by funext y; simp
      rw [this]; exact hasFDerivAt_id (T x)
    exact hc.unique hid
  refine ⟨ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.id ℝ H + B.comp i) (ContinuousLinearMap.id ℝ H + B'.comp i)
    (fun h => H_leftInverse_of_E i hinj B B' h1 h)
    (fun h => H_leftInverse_of_E i hinj B' B h2 h), rfl, rfl⟩

/-- **The bridge.** Under the hypotheses of v2 `prop:gaussiancommon`, written
with `C¹` regularity, every hypothesis of Ramer's Jacobi theorem holds with
`U = E` and `H`-derivative `D_H K(x) = D_E K(x) ∘ i`:

* (2) `K : E → H` is continuous;
* (3a) `K` is `H`-differentiable at every `x`, with derivative `D_E K(x) ∘ i`;
* (3b) `D_H K(x)` is Hilbert–Schmidt for every `x`, with an explicit bound;
* (3c) `x ↦ D_H K(x)` is continuous in the Hilbert–Schmidt norm, stated as
  `Σ ‖(D_H K(y) − D_H K(x)) bₙ‖² → 0` as `y → x`;
* (3d) `I_H + D_H K(x)` is a continuous linear equivalence of `H`.

Hypothesis (1) is the assumption that `T` is a homeomorphism. -/
theorem ramer_hypotheses_of_v2 (hinj : Function.Injective i)
    (b : HilbertBasis ι ℝ H) (hi : Summable fun n => ‖i (b n)‖ ^ 2)
    (T : E ≃ₜ E) (K K' : E → H)
    (hT : ∀ x, T x = x + i (K x)) (hTs : ∀ y, T.symm y = y + i (K' y))
    (hK : ContDiff ℝ 1 K) (hK' : ContDiff ℝ 1 K') :
    Continuous K ∧
    (∀ x, HasFDerivAt (fun h : H => K (x + i h)) ((fderiv ℝ K x).comp i) 0) ∧
    (∀ x, Summable (fun n => ‖fderiv ℝ K x (i (b n))‖ ^ 2) ∧
      ∑' n, ‖fderiv ℝ K x (i (b n))‖ ^ 2 ≤
        ‖fderiv ℝ K x‖ ^ 2 * ∑' n, ‖i (b n)‖ ^ 2) ∧
    (∀ x y, Summable (fun n => ‖fderiv ℝ K y (i (b n)) - fderiv ℝ K x (i (b n))‖ ^ 2)) ∧
    (∀ x, Tendsto (fun y => ∑' n,
        ‖fderiv ℝ K y (i (b n)) - fderiv ℝ K x (i (b n))‖ ^ 2) (𝓝 x) (𝓝 0)) ∧
    (∀ x, ∃ L : H ≃L[ℝ] H,
      (∀ h, L h = h + fderiv ℝ K x (i h)) ∧
      (∀ h, L.symm h = h + fderiv ℝ K' (T x) (i h))) := by
  have hKd : Differentiable ℝ K := hK.differentiable (by norm_num)
  have hK'd : Differentiable ℝ K' := hK'.differentiable (by norm_num)
  have hDc : Continuous (fderiv ℝ K) := hK.continuous_fderiv (by norm_num)
  refine ⟨hK.continuous, fun x => hasFDerivAt_H_direction i K x (hKd x),
    fun x => hs_comp_left i b hi (fderiv ℝ K x), ?_, ?_, ?_⟩
  · intro x y
    have h := (hs_comp_left i b hi (fderiv ℝ K y - fderiv ℝ K x)).1
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply] using h
  · intro x
    have hbound : ∀ y, ∑' n, ‖fderiv ℝ K y (i (b n)) - fderiv ℝ K x (i (b n))‖ ^ 2 ≤
        ‖fderiv ℝ K y - fderiv ℝ K x‖ ^ 2 * ∑' n, ‖i (b n)‖ ^ 2 := fun y => by
      have h := (hs_comp_left i b hi (fderiv ℝ K y - fderiv ℝ K x)).2
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply] using h
    have hlim : Tendsto (fun y => ‖fderiv ℝ K y - fderiv ℝ K x‖ ^ 2 * ∑' n, ‖i (b n)‖ ^ 2)
        (𝓝 x) (𝓝 0) := by
      have h0 : Tendsto (fun y => ‖fderiv ℝ K y - fderiv ℝ K x‖) (𝓝 x) (𝓝 0) := by
        have := (hDc.tendsto x).sub_const (fderiv ℝ K x)
        simpa using this.norm
      simpa using (h0.pow 2).mul_const (∑' n, ‖i (b n)‖ ^ 2)
    exact squeeze_zero (fun y => tsum_nonneg (fun n => by positivity)) hbound hlim
  · intro x
    obtain ⟨L, hL, hLs⟩ := exists_inverse_id_add_HDeriv i hinj T K K' hT hTs hKd hK'd x
    refine ⟨L, fun h => ?_, fun h => ?_⟩
    · have := congrArg (fun F : H →L[ℝ] H => F h) hL
      simpa using this
    · have := congrArg (fun F : H →L[ℝ] H => F h) hLs
      simpa using this

/-- v2 assumes real analyticity into `H`; this gives the `C¹` regularity used above. -/
theorem contDiff_one_of_analytic {K : E → H} [CompleteSpace H]
    (hK : AnalyticOnNhd ℝ K Set.univ) : ContDiff ℝ 1 K :=
  hK.contDiff

end Abstract

/-! ### The actual Cameron–Martin inclusion of checkpoint 20 -/

section Concrete

variable {lower upper : ℝ}

/-- The actual inclusion `H = WeightedRealHilbert (cmModeWeight c) → E_s` is
injective. It is the identity on Fourier coordinates. -/
theorem cmToFullWeightedHilbert_injective (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : 0 ≤ s) :
    Function.Injective (NlsGge.Pilot.cmToFullWeightedHilbert c s hs) := by
  intro x y hxy
  apply Subtype.ext
  funext n
  have hx := NlsGge.Pilot.cmToFullWeightedHilbert_apply c s hs x n
  have hy := NlsGge.Pilot.cmToFullWeightedHilbert_apply c s hs y n
  rw [hxy] at hx
  exact hx.symm.trans hy

/-- The image of the actual inclusion `H → E_s` is dense: the symmetric Fourier
truncations of any `x ∈ E_s` lie in `H` and converge to `x` in `E_s`. With
injectivity and the Hilbert–Schmidt property, this makes `(i, H, E_s)` an abstract
Wiener space in Ramer's sense (p. 169: for a Hilbert space `E`, the norm is
measurable iff `i` is Hilbert–Schmidt; `E` is the completion of `H`). -/
theorem cmToFullWeightedHilbert_denseRange (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : 0 ≤ s) :
    DenseRange (NlsGge.Pilot.cmToFullWeightedHilbert c s hs) := by
  intro x
  have ht := NlsGge.Pilot.weightedProjection_tendsto (NlsGge.Pilot.fullModeWeight c s) x
  refine mem_closure_of_tendsto ht (Filter.Eventually.of_forall fun N => ?_)
  classical
  set f : ℤ → ℂ := (NlsGge.Pilot.weightedProjection (NlsGge.Pilot.fullModeWeight c s)
    (NlsGge.Pilot.symmetricModes N) x : ℤ → ℂ) with hf
  have hfin : ∀ n ∉ NlsGge.Pilot.symmetricModes N,
      ‖NlsGge.Pilot.weightedCoordinates (NlsGge.Pilot.cmModeWeight c) f n‖ ^
        (2 : ENNReal).toReal = 0 := by
    intro n hn
    have : f n = 0 := by
      have h := NlsGge.Pilot.weightedProjection_apply (NlsGge.Pilot.fullModeWeight c s)
        (NlsGge.Pilot.symmetricModes N)
        (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x) n
      rw [if_neg hn] at h
      exact h
    simp [NlsGge.Pilot.weightedCoordinates, this]
  have hmem : f ∈ NlsGge.Pilot.weightedSubmodule (NlsGge.Pilot.cmModeWeight c) := by
    change Memℓp (NlsGge.Pilot.weightedCoordinates (NlsGge.Pilot.cmModeWeight c) f) 2
    exact memℓp_gen (summable_of_ne_finset_zero hfin)
  refine ⟨⟨f, hmem⟩, ?_⟩
  apply Subtype.ext
  funext n
  exact NlsGge.Pilot.cmToFullWeightedHilbert_apply c s hs ⟨f, hmem⟩ n

/-- The actual inclusion is Hilbert–Schmidt for every real Hilbert basis of the
CM space, for `1/2 < s` (checkpoint-20 theorem, restated in the form used here). -/
theorem cmToFullWeightedHilbert_hs (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) {ι : Type*}
    (b : HilbertBasis ι ℝ (NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))) :
    Summable (fun n => ‖NlsGge.Pilot.cmToFullWeightedHilbert c s
      (le_of_lt (by linarith : 0 < s)) (b n)‖ ^ 2) :=
  NlsGge.Pilot.cmToFullWeightedHilbert_any_sourceBasis_square_summable c s hs b

/-- **Concrete bridge.** For the actual spaces `E = E_s` (`1/2 < s`) and
`H = ` the actual CM space with norm² `2 Σ q_n |h_n|²`, any homeomorphism
`T = id + i ∘ K` with inverse `id + i ∘ K'`, where `K, K' : E_s → H` are `C¹`,
satisfies all of Ramer's hypotheses (2)–(3) on `U = E_s`. This is the
`ramer_hypotheses_of_v2` conclusion for the actual inclusion. -/
theorem actual_ramer_hypotheses_of_v2 (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) {ι : Type*}
    (b : HilbertBasis ι ℝ (NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)))
    (T : NlsGge.Pilot.FullWeightedHilbert c s ≃ₜ NlsGge.Pilot.FullWeightedHilbert c s)
    (K K' : NlsGge.Pilot.FullWeightedHilbert c s →
      NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (hT : ∀ x, T x = x + NlsGge.Pilot.cmToFullWeightedHilbert c s
      (le_of_lt (by linarith : 0 < s)) (K x))
    (hTs : ∀ y, T.symm y = y + NlsGge.Pilot.cmToFullWeightedHilbert c s
      (le_of_lt (by linarith : 0 < s)) (K' y))
    (hK : ContDiff ℝ 1 K) (hK' : ContDiff ℝ 1 K') :
    Continuous K ∧
    (∀ x, HasFDerivAt (fun h => K (x + NlsGge.Pilot.cmToFullWeightedHilbert c s
        (le_of_lt (by linarith : 0 < s)) h))
      ((fderiv ℝ K x).comp (NlsGge.Pilot.cmToFullWeightedHilbert c s
        (le_of_lt (by linarith : 0 < s)))) 0) ∧
    (∀ x, Summable (fun n => ‖fderiv ℝ K x (NlsGge.Pilot.cmToFullWeightedHilbert c s
        (le_of_lt (by linarith : 0 < s)) (b n))‖ ^ 2)) ∧
    (∀ x y, Summable (fun n =>
        ‖fderiv ℝ K y (NlsGge.Pilot.cmToFullWeightedHilbert c s
            (le_of_lt (by linarith : 0 < s)) (b n)) -
          fderiv ℝ K x (NlsGge.Pilot.cmToFullWeightedHilbert c s
            (le_of_lt (by linarith : 0 < s)) (b n))‖ ^ 2)) ∧
    (∀ x, Tendsto (fun y => ∑' n,
        ‖fderiv ℝ K y (NlsGge.Pilot.cmToFullWeightedHilbert c s
            (le_of_lt (by linarith : 0 < s)) (b n)) -
          fderiv ℝ K x (NlsGge.Pilot.cmToFullWeightedHilbert c s
            (le_of_lt (by linarith : 0 < s)) (b n))‖ ^ 2) (𝓝 x) (𝓝 0)) ∧
    (∀ x, ∃ L : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c) ≃L[ℝ]
        NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c),
      (∀ h, L h = h + fderiv ℝ K x (NlsGge.Pilot.cmToFullWeightedHilbert c s
        (le_of_lt (by linarith : 0 < s)) h)) ∧
      (∀ h, L.symm h = h + fderiv ℝ K' (T x) (NlsGge.Pilot.cmToFullWeightedHilbert c s
        (le_of_lt (by linarith : 0 < s)) h))) := by
  obtain ⟨h1, h2, h3, h4s, h4, h5⟩ := ramer_hypotheses_of_v2 _
    (cmToFullWeightedHilbert_injective c s _) b (cmToFullWeightedHilbert_hs c s hs b)
    T K K' hT hTs hK hK'
  exact ⟨h1, h2, fun x => (h3 x).1, h4s, h4, h5⟩

end Concrete

end NlsGge.Ramer
