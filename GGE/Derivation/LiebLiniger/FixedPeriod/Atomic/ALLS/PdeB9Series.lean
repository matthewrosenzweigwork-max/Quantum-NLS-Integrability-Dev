import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB8Approved

/-! # Track B, contract 24 support: absolutely summable Fourier series and the cubic

For an absolutely summable coefficient sequence `c` (`IsL1 c`), `serC c = ∑ₖ c k • e_k` is the
uniformly convergent Fourier series in `C(𝕋, ℂ)`. Proved here, with all summability side
conditions first:
* `fourierCoeff_serC`: its Fourier coefficients are `c` (uniqueness through the `L²` Hilbert
  basis `fourierLp`);
* `serC_mul`: `serC c · serC d = serC (conv c d)` (Cauchy product on `ℤ × ℤ`, fibrewise sums);
* `conj_serC`: `conj (serC c) = serC (cstar c)`;
* `physicalFourier_cubicNL_serC`: the Fourier coefficients of `cubicNL ∘ serC c` are the sequence
  nonlinearity `nonlin c` of `IsNLSSolM`;
* `norm_serC_sub_le`: `‖serC c - serC d‖_∞ ≤ ∑ₖ ‖c k - d k‖`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff ComplexConjugate
set_option autoImplicit false
noncomputable section

/-- The Fourier series `∑ₖ c k • e_k` as a continuous function on the circle (meaningful for
`IsL1 c`). -/
def serC (c : ℤ → ℂ) : C(PhysicalCircle, ℂ) := ∑' k : ℤ, c k • fourier (T := (1 : ℝ)) k

theorem summable_serC {c : ℤ → ℂ} (hc : IsL1 c) :
    Summable fun k : ℤ => c k • fourier (T := (1 : ℝ)) k := by
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm, mul_one] using (isL1_iff.1 hc)

theorem hasSum_serC {c : ℤ → ℂ} (hc : IsL1 c) :
    HasSum (fun k : ℤ => c k • fourier (T := (1 : ℝ)) k) (serC c) :=
  (summable_serC hc).hasSum

theorem serC_apply {c : ℤ → ℂ} (hc : IsL1 c) (x : PhysicalCircle) :
    serC c x = ∑' k : ℤ, c k * fourier (T := (1 : ℝ)) k x := by
  rw [serC, ← ContinuousMap.tsum_apply (summable_serC hc)]
  rfl

theorem summable_serC_apply {c : ℤ → ℂ} (hc : IsL1 c) (x : PhysicalCircle) :
    Summable fun k : ℤ => c k * fourier (T := (1 : ℝ)) k x := by
  apply Summable.of_norm
  have h : ∀ k : ℤ, ‖c k * fourier (T := (1 : ℝ)) k x‖ = ‖c k‖ := fun k => by
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  simpa only [h] using (isL1_iff.1 hc)

theorem hasSum_serC_apply {c : ℤ → ℂ} (hc : IsL1 c) (x : PhysicalCircle) :
    HasSum (fun k : ℤ => c k * fourier (T := (1 : ℝ)) k x) (serC c x) := by
  rw [serC_apply hc]
  exact (summable_serC_apply hc x).hasSum

/-- The Fourier coefficients of `serC c` are `c`. -/
theorem fourierCoeff_serC {c : ℤ → ℂ} (hc : IsL1 c) (n : ℤ) :
    fourierCoeff (serC c) n = c n := by
  have h := (ContinuousMap.toLp (E := ℂ) 2 (@AddCircle.haarAddCircle (1 : ℝ) _) ℂ).hasSum (hasSum_serC hc)
  simp only [map_smul] at h
  change HasSum (fun k : ℤ => c k • fourierLp (T := (1 : ℝ)) 2 k) _ at h
  have h2 := h.map (innerSL ℂ (fourierLp (T := (1 : ℝ)) 2 n)) (innerSL ℂ _).continuous
  have hite := orthonormal_iff_ite.1 (orthonormal_fourier (T := (1 : ℝ)))
  have h3 : HasSum (fun k : ℤ => c k * (if n = k then (1 : ℂ) else 0))
      (inner ℂ (fourierLp (T := (1 : ℝ)) 2 n)
        (ContinuousMap.toLp (E := ℂ) 2 (@AddCircle.haarAddCircle (1 : ℝ) _) ℂ (serC c))) := by
    convert h2 using 1
    · funext k
      simp only [Function.comp_apply, innerSL_apply_apply, inner_smul_right, hite n k]
    · simp only [innerSL_apply_apply]
  have h4 : HasSum (fun k : ℤ => c k * (if n = k then (1 : ℂ) else 0)) (c n) := by
    have := hasSum_single (f := fun k : ℤ => c k * (if n = k then (1 : ℂ) else 0)) n
      (fun k hk => by simp [Ne.symm hk])
    simpa using this
  rw [← fourierCoeff_toLp, ← fourierBasis_repr, HilbertBasis.repr_apply_apply, coe_fourierBasis]
  exact h3.unique h4

theorem norm_fourierS_apply (k : ℤ) (x : PhysicalCircle) : ‖fourier (T := (1 : ℝ)) k x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

theorem summable_norm_coef_fourier {c : ℤ → ℂ} (hc : IsL1 c) (x : PhysicalCircle) :
    Summable fun k : ℤ => ‖c k * fourier (T := (1 : ℝ)) k x‖ := by
  simpa only [norm_mul, norm_fourierS_apply, mul_one] using isL1_iff.1 hc

theorem hasSum_serC_prod {c d : ℤ → ℂ} (hc : IsL1 c) (hd : IsL1 d) (x : PhysicalCircle) :
    HasSum (fun p : ℤ × ℤ => c p.1 * fourier (T := (1 : ℝ)) p.1 x *
      (d p.2 * fourier (T := (1 : ℝ)) p.2 x)) (serC c x * serC d x) := by
  have h1 : HasSum (fun k : ℤ => c k * fourier (T := (1 : ℝ)) k x) (serC c x) :=
    hasSum_serC_apply hc x
  have h2 : HasSum (fun k : ℤ => d k * fourier (T := (1 : ℝ)) k x) (serC d x) :=
    hasSum_serC_apply hd x
  have hs : Summable (fun p : ℤ × ℤ => c p.1 * fourier (T := (1 : ℝ)) p.1 x *
      (d p.2 * fourier (T := (1 : ℝ)) p.2 x)) :=
    summable_mul_of_summable_norm (f := fun k : ℤ => c k * fourier (T := (1 : ℝ)) k x)
      (g := fun k : ℤ => d k * fourier (T := (1 : ℝ)) k x)
      (summable_norm_coef_fourier hc x) (summable_norm_coef_fourier hd x)
  exact HasSum.mul (f := fun k : ℤ => c k * fourier (T := (1 : ℝ)) k x)
    (g := fun k : ℤ => d k * fourier (T := (1 : ℝ)) k x) h1 h2 hs

theorem fourier_mul_sub (n k : ℤ) (x : PhysicalCircle) :
    fourier (T := (1 : ℝ)) k x * fourier (T := (1 : ℝ)) (n - k) x = fourier (T := (1 : ℝ)) n x := by
  rw [← fourier_add, add_sub_cancel]

theorem hasSum_serC_prod' {c d : ℤ → ℂ} (hc : IsL1 c) (hd : IsL1 d) (x : PhysicalCircle) :
    HasSum (fun q : ℤ × ℤ => c q.2 * d (q.1 - q.2) * fourier (T := (1 : ℝ)) q.1 x)
      (serC c x * serC d x) := by
  have h := (pairEquiv.hasSum_iff (f := fun p : ℤ × ℤ => c p.1 * fourier (T := (1 : ℝ)) p.1 x *
      (d p.2 * fourier (T := (1 : ℝ)) p.2 x))).2 (hasSum_serC_prod hc hd x)
  refine h.congr_fun ?_
  intro q
  simp only [Function.comp_apply, pairEquiv, Equiv.coe_fn_mk]
  rw [← fourier_mul_sub q.1 q.2 x]
  ring

/-- Product of absolutely summable Fourier series: `serC c · serC d = serC (conv c d)`. -/
theorem serC_mul {c d : ℤ → ℂ} (hc : IsL1 c) (hd : IsL1 d) (x : PhysicalCircle) :
    serC c x * serC d x = serC (conv c d) x := by
  have hfib : ∀ n : ℤ, HasSum (fun k : ℤ => c k * d (n - k) * fourier (T := (1 : ℝ)) n x)
      (conv c d n * fourier (T := (1 : ℝ)) n x) := fun n =>
    ((summable_conv_term hc hd n).hasSum).mul_right _
  have hg := (hasSum_serC_prod' hc hd x).prod_fiberwise hfib
  exact hg.unique (hasSum_serC_apply (isL1_conv hc hd).1 x)

/-- Conjugate of an absolutely summable Fourier series. -/
theorem conj_serC {c : ℤ → ℂ} (hc : IsL1 c) (x : PhysicalCircle) :
    conj (serC c x) = serC (cstar c) x := by
  have h := (hasSum_serC_apply hc x).star
  have h2 := ((Equiv.neg ℤ).hasSum_iff
    (f := fun k : ℤ => star (c k * fourier (T := (1 : ℝ)) k x))).2 h
  have h3 : HasSum (fun k : ℤ => cstar c k * fourier (T := (1 : ℝ)) k x) (conj (serC c x)) := by
    convert h2 using 1
    · funext k
      simp only [Function.comp_apply, Equiv.neg_apply, cstar, star_mul', fourier_neg]
      change conj (c (-k)) * fourier (T := (1 : ℝ)) k x =
        conj (c (-k)) * conj (conj (fourier (T := (1 : ℝ)) k x))
      rw [Complex.conj_conj]
    · rfl
  exact h3.unique (hasSum_serC_apply ((isL1_cstar_iff c).2 hc) x)

/-- The cubic of an absolutely summable Fourier series. -/
theorem cubicNL_serC {c : ℤ → ℂ} (hc : IsL1 c) (x : PhysicalCircle) :
    cubicNL (serC c x) = 2 * serC (conv (conv c c) (cstar c)) x := by
  have hcc := (isL1_conv hc hc).1
  have hcs := (isL1_cstar_iff c).2 hc
  rw [← serC_mul hcc hcs, ← serC_mul hc hc, ← conj_serC hc, cubicNL]
  have h : ((‖serC c x‖ ^ 2 : ℝ) : ℂ) = serC c x * conj (serC c x) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h]
  ring

/-- **The cubic in Fourier variables**: for absolutely summable `c`, the Fourier coefficients of
`2|serC c|² serC c` are the sequence nonlinearity `nonlin c`. -/
theorem physicalFourier_cubicNL_serC {c : ℤ → ℂ} (hc : IsL1 c) (n : ℤ) :
    physicalFourier (fun x => cubicNL (serC c x)) n = nonlin c n := by
  have hN := (isL1_conv (isL1_conv hc hc).1 ((isL1_cstar_iff c).2 hc)).1
  have h : (fun x => cubicNL (serC c x)) = fun x => 2 * serC (conv (conv c c) (cstar c)) x :=
    funext fun x => cubicNL_serC hc x
  rw [physicalFourier, h, fourierCoeff.const_mul, fourierCoeff_serC hN, nonlin]

theorem serC_sub {c d : ℤ → ℂ} (hc : IsL1 c) (hd : IsL1 d) :
    serC c - serC d = serC (c - d) := by
  have h := (hasSum_serC hc).sub (hasSum_serC hd)
  refine h.unique ?_
  convert hasSum_serC (isL1_sub hc hd) using 1
  funext k
  simp only [Pi.sub_apply, sub_smul]

theorem norm_serC_le {c : ℤ → ℂ} (hc : IsL1 c) : ‖serC c‖ ≤ ∑' k : ℤ, ‖c k‖ := by
  have hn : ∀ k : ℤ, ‖c k • fourier (T := (1 : ℝ)) k‖ = ‖c k‖ := fun k => by
    rw [norm_smul, fourier_norm, mul_one]
  calc ‖serC c‖ ≤ ∑' k : ℤ, ‖c k • fourier (T := (1 : ℝ)) k‖ :=
        norm_tsum_le_tsum_norm (by simpa only [hn] using (isL1_iff.1 hc))
    _ = ∑' k : ℤ, ‖c k‖ := by simp only [hn]

theorem norm_serC_sub_le {c d : ℤ → ℂ} (hc : IsL1 c) (hd : IsL1 d) :
    ‖serC c - serC d‖ ≤ ∑' k : ℤ, ‖c k - d k‖ := by
  rw [serC_sub hc hd]
  exact norm_serC_le (isL1_sub hc hd)

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
