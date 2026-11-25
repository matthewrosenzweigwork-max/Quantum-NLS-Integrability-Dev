-- INERT source-first KST013 prerequisite. NOT_RUN; root + independent review required.
-- Locally re-earns coefficient identities from PUBLIC KST003/LIB002/KST004 APIs.
-- No import or private-name access to KST012 is used.
-- B/C/D are locally re-earned proof bodies, NOT imported private theorem values.
import NlsGge.Atomic.KST.KST012

set_option autoImplicit false
noncomputable section
namespace NlsGge.Atomic.KST013

open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

private def stage13A_scalarBasis : HilbertBasis ℤ ℂ SpectralScalarL2 :=
  fourierBasis (T := (2 : ℝ))

private lemma stage13A_scalarBasis_apply (m : ℤ) :
    stage13A_scalarBasis m = spectralBasis m := by
  exact congrFun (coe_fourierBasis (T := (2 : ℝ))) m

set_option backward.isDefEq.respectTransparency false in
private lemma stage13A_scalarBasis_repr (f : SpectralScalarL2) (m : ℤ) :
    stage13A_scalarBasis.repr f m = fourierCoeff f m := by
  change (fourierBasis (T := (2 : ℝ))).repr f m = fourierCoeff f m
  simpa only [spectralHaar] using (fourierBasis_repr (T := (2 : ℝ)) f m)

private lemma stage13A_coeff_smul (c : ℂ) (f : SpectralScalarL2) (m : ℤ) :
    fourierCoeff (c • f) m = c * fourierCoeff f m := by
  rw [← stage13A_scalarBasis_repr, ← stage13A_scalarBasis_repr, map_smul]
  rfl

private lemma stage13A_coeff_sub (f g : SpectralScalarL2) (m : ℤ) :
    fourierCoeff (f - g) m = fourierCoeff f m - fourierCoeff g m := by
  rw [← stage13A_scalarBasis_repr, ← stage13A_scalarBasis_repr, ← stage13A_scalarBasis_repr, map_sub]
  rfl

private lemma stage13A_coeff_basis (a m : ℤ) :
    fourierCoeff (spectralBasis a) m = if m = a then 1 else 0 := by
  calc
    fourierCoeff (spectralBasis a) m =
        inner ℂ (stage13A_scalarBasis m) (spectralBasis a) := by
      rw [← stage13A_scalarBasis_repr, stage13A_scalarBasis.repr_apply_apply]
    _ = if m = a then 1 else 0 := by
      rw [← stage13A_scalarBasis_apply a]
      exact (orthonormal_iff_ite.mp stage13A_scalarBasis.orthonormal) m a

private lemma stage13A_inner_upper (n : ℤ) (h : KSTPairL2) :
    inner ℂ (kstPnUpper n) h = fourierCoeff (h true) (-n) := by
  calc
    inner ℂ (kstPnUpper n) h = inner ℂ (spectralBasis (-n)) (h true) := by
      simp [kstPnUpper, PiLp.inner_apply, Fintype.sum_bool]
    _ = fourierCoeff (h true) (-n) := by
      rw [← stage13A_scalarBasis_apply, ← stage13A_scalarBasis.repr_apply_apply,
        stage13A_scalarBasis_repr]

private lemma stage13A_inner_lower (n : ℤ) (h : KSTPairL2) :
    inner ℂ (kstPnLower n) h = fourierCoeff (h false) n := by
  calc
    inner ℂ (kstPnLower n) h = inner ℂ (spectralBasis n) (h false) := by
      simp [kstPnLower, PiLp.inner_apply, Fintype.sum_bool]
    _ = fourierCoeff (h false) n := by
      rw [← stage13A_scalarBasis_apply, ← stage13A_scalarBasis.repr_apply_apply,
        stage13A_scalarBasis_repr]

private lemma stage13A_Pn_component (n : ℤ) (h : KSTPairL2) (b : Bool) :
    spectralPn n h b =
      fourierCoeff (h b) (if b then -n else n) •
        spectralBasis (if b then -n else n) := by
  rw [spectralPn_apply, stage13A_inner_upper, stage13A_inner_lower]
  cases b <;> simp [kstPnUpper, kstPnLower]

private lemma stage13A_coeff_Pn (n : ℤ) (h : KSTPairL2) (b : Bool) (m : ℤ) :
    fourierCoeff (spectralPn n h b) m =
      if sourceModeIndex b m = n then fourierCoeff (h b) m else 0 := by
  rw [stage13A_Pn_component, stage13A_coeff_smul, stage13A_coeff_basis]
  cases b
  · by_cases hm : m = n
    · subst m
      simp [sourceModeIndex]
    · simp [sourceModeIndex, hm]
  · by_cases hm : m = -n
    · subst m
      simp [sourceModeIndex]
    · have hneg : -m ≠ n := by omega
      simp [sourceModeIndex, hm, hneg]

private lemma stage13A_coeff_Qn (n : ℤ) (h : KSTPairL2) (b : Bool) (m : ℤ) :
    fourierCoeff (spectralQn n h b) m =
      if sourceModeIndex b m = n then 0 else fourierCoeff (h b) m := by
  change fourierCoeff (h b - spectralPn n h b) m = _
  rw [stage13A_coeff_sub, stage13A_coeff_Pn]
  by_cases hm : sourceModeIndex b m = n <;> simp [hm]

set_option backward.isDefEq.respectTransparency false in
private lemma stage13A_coeff_complement (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) (m : ℤ) :
    fourierCoeff (complementaryMultiplier n z hz h b) m =
      complementaryResolventCoeff n z (sourceModeIndex b m) *
        fourierCoeff (h b) m := by
  change fourierCoeff (scalarComplementaryMultiplier n z hz b (h b)) m = _
  have hr := scalarComplementaryMultiplier_repr n z hz b (h b) m
  change stage13A_scalarBasis.repr (scalarComplementaryMultiplier n z hz b (h b)) m =
    complementaryResolventCoeff n z (sourceModeIndex b m) *
      stage13A_scalarBasis.repr (h b) m at hr
  simpa only [stage13A_scalarBasis_repr] using hr

/-- Coefficients of the actual all-test free graph, with the source's
upper reflected / lower raw labels. No regularity premise is added. -/
private lemma stage13A_free_graph_coeff
    {v y : KSTPairL2} (hgraph : HasKSTFreeDiracGraph v y)
    (b : Bool) (m : ℤ) :
    fourierCoeff (y b) m =
      (sourceModeIndex b m : ℂ) * (Real.pi : ℂ) * fourierCoeff (v b) m := by
  obtain ⟨du, dl, hdu, hdl, hy⟩ := hgraph
  cases b
  · have hcomponent : y false = (-Complex.I) • dl := by
      rw [hy]
      simp
    have hcoeff : fourierCoeff dl m =
        NlsGge.Atomic.LIB002.fourierMultiplier (2 : ℝ) m ^ 1 *
          fourierCoeff (v false) m := by
      simpa only [SpectralCircle, SpectralScalarL2, spectralHaar] using!
        (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff hdl m)
    rw [hcomponent, stage13A_coeff_smul, hcoeff]
    simp only [NlsGge.Atomic.LIB002.fourierMultiplier, pow_one, sourceModeIndex]
    push_cast
    ring_nf <;> simp only [Complex.I_sq] <;> ring
  · have hcomponent : y true = Complex.I • du := by
      rw [hy]
      simp
    have hcoeff : fourierCoeff du m =
        NlsGge.Atomic.LIB002.fourierMultiplier (2 : ℝ) m ^ 1 *
          fourierCoeff (v true) m := by
      simpa only [SpectralCircle, SpectralScalarL2, spectralHaar] using!
        (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff hdu m)
    rw [hcomponent, stage13A_coeff_smul, hcoeff]
    simp only [NlsGge.Atomic.LIB002.fourierMultiplier, pow_one, sourceModeIndex]
    push_cast
    ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- Genuine complementary left inverse on an arbitrary actual weak free
Dirac graph. The full signed spectrum and the two removed resonant modes
are retained. Membership of the multiplier output in the SAME L2 carrier
is furnished by the public bounded CLM before any inverse cancellation. -/
private lemma stage13A_complementary_left_inverse
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (v g : KSTPairL2)
    (hgraph : HasKSTFreeDiracGraph v (z • v - g)) :
    complementaryMultiplier n z hz g = spectralQn n v := by
  apply PiLp.ext
  intro b
  apply stage13A_scalarBasis.repr.injective
  apply lp.ext
  funext m
  rw [stage13A_scalarBasis_repr, stage13A_scalarBasis_repr,
    stage13A_coeff_complement, stage13A_coeff_Qn]
  by_cases hkn : sourceModeIndex b m = n
  · simp only [hkn, complementaryResolventCoeff_resonant, zero_mul, if_true]
  · have hden : z - (sourceModeIndex b m : ℂ) * (Real.pi : ℂ) ≠ 0 :=
      complementary_denominator_ne_zero n (sourceModeIndex b m) z hz hkn
    have hfree := stage13A_free_graph_coeff hgraph b m
    change fourierCoeff (z • v b - g b) m = _ at hfree
    rw [stage13A_coeff_sub, stage13A_coeff_smul] at hfree
    have hmul :
        (z - (sourceModeIndex b m : ℂ) * (Real.pi : ℂ)) *
          fourierCoeff (v b) m = fourierCoeff (g b) m := by
      linear_combination hfree
    rw [if_neg hkn]
    simp only [complementaryResolventCoeff, if_neg hkn]
    rw [← hmul, ← mul_assoc, inv_mul_cancel₀ hden, one_mul]

/-- On the actual Q-range, the left inverse reconstructs the SAME vector.
The Q-range hypothesis is a literal domain property, not a target equation. -/
private lemma stage13A_complementary_left_inverse_on_Q
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (v g : KSTPairL2) (hv : spectralQn n v = v)
    (hgraph : HasKSTFreeDiracGraph v (z • v - g)) :
    complementaryMultiplier n z hz g = v := by
  exact (stage13A_complementary_left_inverse n z hz v g hgraph).trans hv

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

private local instance stage13B_spectralHaar_probability : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

private lemma stage13B_distance_sq_summable (n : ℤ) :
    Summable (fun m : ℤ => 1 / (Int.natAbs (m - n) : ℝ) ^ 2) := by
  have hbase0 : Summable (fun d : ℤ => 1 / (d : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hbase : Summable (fun d : ℤ => 1 / (Int.natAbs d : ℝ) ^ 2) := by
    convert hbase0 using 1 <;> simp [Nat.cast_natAbs, Int.cast_abs, abs_pow]
  have hshift := (Equiv.addRight (-n)).summable_iff.mpr hbase
  have hs : Summable (fun m : ℤ => 1 / (Int.natAbs (m + -n) : ℝ) ^ 2) :=
    hshift.congr fun m => by rfl
  exact hs.congr fun m => by rw [show m + -n = m - n by omega]

private lemma stage13B_resolvent_sq_summable (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (b : Bool) :
    Summable (fun m : ℤ =>
      ‖complementaryResolventCoeff n z (sourceModeIndex b m)‖ ^ 2) := by
  have hs : Summable (fun k : ℤ => ‖complementaryResolventCoeff n z k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
      (stage13B_distance_sq_summable n)
    have hsq := (sq_le_sq₀ (norm_nonneg (complementaryResolventCoeff n z k))
      (by positivity : 0 ≤ 1 / (Int.natAbs (k - n) : ℝ))).2
        (complementaryResolventCoeff_bound n k z hz)
    simpa only [div_pow, one_pow] using hsq
  cases b
  · simpa [sourceModeIndex] using hs
  · simpa [sourceModeIndex, Function.comp_def] using (Equiv.neg ℤ).summable_iff.mpr hs

private def stage13B_resolventLp (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (b : Bool) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun m => complementaryResolventCoeff n z (sourceModeIndex b m),
    memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        stage13B_resolvent_sq_summable n z hz b)⟩

private lemma stage13B_holder22 :
    Real.HolderConjugate (2 : ENNReal).toReal (2 : ENNReal).toReal := by
  rw [Real.holderConjugate_iff]
  norm_num

set_option backward.isDefEq.respectTransparency false in
private lemma stage13B_complement_coeff_norm_summable (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) :
    Summable (fun m : ℤ =>
      ‖fourierCoeff (complementaryMultiplier n z hz h b) m‖) := by
  have hs := lp.summable_mul stage13B_holder22 (stage13B_resolventLp n z hz b)
    (stage13A_scalarBasis.repr (h b))
  refine hs.congr fun m => ?_
  change ‖complementaryResolventCoeff n z (sourceModeIndex b m)‖ *
      ‖stage13A_scalarBasis.repr (h b) m‖ = _
  rw [stage13A_scalarBasis_repr, stage13A_coeff_complement, norm_mul]

private lemma stage13B_complement_coeff_summable (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) :
    Summable (fun m : ℤ =>
      fourierCoeff (complementaryMultiplier n z hz h b) m) :=
  (stage13B_complement_coeff_norm_summable n z hz h b).of_norm

private lemma stage13B_continuous_synthesis (v : SpectralScalarL2)
    (hv : Summable (fun m : ℤ => ‖fourierCoeff v m‖)) :
    ∃ g : C(SpectralCircle, ℂ),
      ContinuousMap.toLp (E := ℂ) 2 spectralHaar ℂ g = v ∧
      HasSum (fun m : ℤ => fourierCoeff v m •
        (fourier m : C(SpectralCircle, ℂ))) g := by
  have hnorm : Summable (fun m : ℤ =>
      ‖fourierCoeff v m • (fourier m : C(SpectralCircle, ℂ))‖) := by
    simpa only [norm_smul, fourier_norm, mul_one] using hv
  have hcont : Summable (fun m : ℤ => fourierCoeff v m •
      (fourier m : C(SpectralCircle, ℂ))) := hnorm.of_norm
  let g : C(SpectralCircle, ℂ) :=
    ∑' m : ℤ, fourierCoeff v m • (fourier m : C(SpectralCircle, ℂ))
  refine ⟨g, ?_, hcont.hasSum⟩
  let C : C(SpectralCircle, ℂ) →L[ℂ] SpectralScalarL2 :=
    ContinuousMap.toLp (E := ℂ) 2 spectralHaar ℂ
  have hmapped : HasSum
      (fun m : ℤ => C (fourierCoeff v m • (fourier m : C(SpectralCircle, ℂ))))
      (C g) :=
    C.hasSum hcont.hasSum
  have hterm (m : ℤ) :
      fourierCoeff v m • (fourierLp 2 m : SpectralScalarL2) =
        C (fourierCoeff v m • (fourier m : C(SpectralCircle, ℂ))) := by
    have h := (ContinuousLinearMap.map_smul C (fourierCoeff v m)
      (fourier m : C(SpectralCircle, ℂ))).symm
    simpa only [C, fourierLp, SpectralScalarL2, spectralHaar] using! h
  have hL2 : HasSum (fun m : ℤ => fourierCoeff v m • fourierLp 2 m)
      (ContinuousMap.toLp (E := ℂ) 2 spectralHaar ℂ g) :=
    hmapped.congr_fun hterm
  exact hL2.unique (hasSum_fourier_series_L2 v)

private lemma stage13B_complement_continuous_representative (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) :
    ∃ g : C(SpectralCircle, ℂ),
      ContinuousMap.toLp (E := ℂ) 2 spectralHaar ℂ g =
        complementaryMultiplier n z hz h b ∧
      ((complementaryMultiplier n z hz h b : SpectralCircle → ℂ) =ᵐ[spectralHaar] g) ∧
      HasSum (fun m : ℤ =>
        fourierCoeff (complementaryMultiplier n z hz h b) m •
          (fourier m : C(SpectralCircle, ℂ))) g := by
  obtain ⟨g, hg, hsum⟩ := stage13B_continuous_synthesis
    (complementaryMultiplier n z hz h b)
    (stage13B_complement_coeff_norm_summable n z hz h b)
  refine ⟨g, hg, ?_, hsum⟩
  have hae : ((ContinuousMap.toLp (E := ℂ) 2 spectralHaar ℂ g : SpectralScalarL2) :
      SpectralCircle → ℂ) =ᵐ[spectralHaar] g :=
    ContinuousMap.coeFn_toLp spectralHaar g
  rwa [hg] at hae

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

local instance : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

private lemma stage13C_product_memLp
    (f : SpectralScalarL2) (g : C(SpectralCircle, ℂ)) :
    MemLp (fun x : SpectralCircle => f x * g x) 2 spectralHaar := by
  apply (Lp.memLp f).of_le_mul (c := ‖g‖)
    ((Lp.aestronglyMeasurable f).mul g.continuous.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    calc
      ‖f x * g x‖ = ‖g x‖ * ‖f x‖ := by rw [norm_mul, mul_comm]
      _ ≤ ‖g‖ * ‖f x‖ :=
        mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _)

/- For a genuine summable continuous Fourier synthesis, this is the needed
   product coefficient theorem. `f` is the actual L² field, `g` the actual
   continuous representative, and `a` the actual coefficient sequence. -/
private lemma stage13C_product_fourierCoeff
    (f : SpectralScalarL2) (a : ℤ → ℂ) (g : C(SpectralCircle, ℂ))
    (ha : Summable fun m : ℤ => ‖a m‖)
    (hseries : HasSum (fun m : ℤ => a m • (fourier m : C(SpectralCircle, ℂ))) g)
    (l : ℤ) :
    Summable (fun m : ℤ => a m * fourierCoeff f (l - m)) ∧
      fourierCoeff (fun x : SpectralCircle => f x * g x) l =
        ∑' m : ℤ, a m * fourierCoeff f (l - m) := by
  have hf : Integrable (f : SpectralCircle → ℂ) spectralHaar :=
    MemLp.integrable (by norm_num) (Lp.memLp f)
  let F : ℤ → SpectralCircle → ℂ := fun m x =>
    a m * (fourier (m - l) x * f x)
  have hF_integrable (m : ℤ) : Integrable (F m) spectralHaar := by
    have hbase : Integrable (fun x : SpectralCircle => fourier (m - l) x * f x)
        spectralHaar := by
      simpa only [SpectralCircle, SpectralScalarL2, spectralHaar, smul_eq_mul] using!
        hf.fourier_smul (m - l)
    simpa only [F] using hbase.const_mul (a m)
  have hF_norm_integral (m : ℤ) :
      (∫ x : SpectralCircle, ‖F m x‖ ∂spectralHaar) =
        ‖a m‖ * ∫ x : SpectralCircle, ‖f x‖ ∂spectralHaar := by
    calc
      (∫ x : SpectralCircle, ‖F m x‖ ∂spectralHaar) =
          ∫ x : SpectralCircle, ‖a m‖ * ‖f x‖ ∂spectralHaar := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp [F, norm_mul, fourier_apply, Circle.norm_coe]
      _ = ‖a m‖ * ∫ x : SpectralCircle, ‖f x‖ ∂spectralHaar :=
        integral_const_mul _ _
  have hF_norm_summable :
      Summable (fun m : ℤ => ∫ x : SpectralCircle, ‖F m x‖ ∂spectralHaar) := by
    convert ha.mul_right (∫ x : SpectralCircle, ‖f x‖ ∂spectralHaar) using 1
    funext m
    exact hF_norm_integral m
  have h_integrals_norm_summable :
      Summable (fun m : ℤ => ‖∫ x : SpectralCircle, F m x ∂spectralHaar‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => norm_integral_le_integral_norm (F m)) hF_norm_summable
  have hterm (m : ℤ) :
      (∫ x : SpectralCircle, F m x ∂spectralHaar) =
        a m * fourierCoeff f (l - m) := by
    rw [show F m = fun x : SpectralCircle =>
      a m * (fourier (m - l) x * f x) by rfl, integral_const_mul, fourierCoeff]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change fourier (m - l) x * f x =
        fourier (-(l - m)) x • f x
      rw [show m - l = -(l - m) by omega, smul_eq_mul]
  have hcoeff_norm_summable :
      Summable (fun m : ℤ => ‖a m * fourierCoeff f (l - m)‖) :=
    h_integrals_norm_summable.congr fun m => by rw [← hterm m]
  have hpointwise (x : SpectralCircle) :
      HasSum (fun m : ℤ => F m x) (fourier (-l) x * f x * g x) := by
    have heval : HasSum (fun m : ℤ => a m * fourier m x) (g x) := by
      simpa only [ContinuousMap.evalCLM_apply, map_smul, smul_eq_mul] using
        (ContinuousMap.evalCLM ℂ x).hasSum hseries
    have hmul := heval.mul_left (fourier (-l) x * f x)
    apply hmul.congr_fun
    intro m
    symm
    change fourier (-l) x * f x * (a m * fourier m x) =
      a m * (fourier (m - l) x * f x)
    rw [show m - l = m + -l by omega, fourier_add]
    ring
  have h_integral_tsum :
      (∑' m : ℤ, ∫ x : SpectralCircle, F m x ∂spectralHaar) =
        ∫ x : SpectralCircle, ∑' m : ℤ, F m x ∂spectralHaar :=
    integral_tsum_of_summable_integral_norm hF_integrable hF_norm_summable
  have hpointwise_tsum (x : SpectralCircle) :
      (∑' m : ℤ, F m x) = fourier (-l) x * f x * g x :=
    (hpointwise x).tsum_eq
  have hfourierCoeff :
      fourierCoeff (fun x : SpectralCircle => f x * g x) l =
        ∫ x : SpectralCircle, fourier (-l) x * f x * g x ∂spectralHaar := by
    rw [fourierCoeff]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [smul_eq_mul]
      ring
  constructor
  · exact hcoeff_norm_summable.of_norm
  · calc
      fourierCoeff (fun x : SpectralCircle => f x * g x) l =
          ∫ x : SpectralCircle, fourier (-l) x * f x * g x ∂spectralHaar := hfourierCoeff
      _ = ∫ x : SpectralCircle, ∑' m : ℤ, F m x ∂spectralHaar := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => (hpointwise_tsum x).symm
      _ = ∑' m : ℤ, ∫ x : SpectralCircle, F m x ∂spectralHaar := h_integral_tsum.symm
      _ = ∑' m : ℤ, a m * fourierCoeff f (l - m) := tsum_congr hterm

private lemma stage13C_productLp_fourierCoeff
    (f : SpectralScalarL2) (a : ℤ → ℂ) (g : C(SpectralCircle, ℂ))
    (ha : Summable fun m : ℤ => ‖a m‖)
    (hseries : HasSum (fun m : ℤ => a m • (fourier m : C(SpectralCircle, ℂ))) g)
    (l : ℤ) :
    Summable (fun m : ℤ => a m * fourierCoeff f (l - m)) ∧
      fourierCoeff
          ((stage13C_product_memLp f g).toLp (fun x : SpectralCircle => f x * g x)) l =
        ∑' m : ℤ, a m * fourierCoeff f (l - m) := by
  obtain ⟨hsum, hcoeff⟩ := stage13C_product_fourierCoeff f a g ha hseries l
  have hrepresentative := (stage13C_product_memLp f g).coeFn_toLp
  have hfc := fourierCoeff_congr_ae hrepresentative
  exact ⟨hsum, (congrFun hfc l).trans hcoeff⟩

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

set_option backward.isDefEq.respectTransparency false in
private lemma stage13D_qOperator_component_product
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) :
    MemLp (fun x : SpectralCircle =>
        NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
          complementaryMultiplier n z hz h (!b) x) 2 spectralHaar ∧
      (NlsGge.Atomic.KST006.qOperator φ n z hz h b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
          complementaryMultiplier n z hz h (!b) x) := by
  obtain ⟨g, _hg, hvg, hseries⟩ :=
    stage13B_complement_continuous_representative n z hz h (!b)
  have ha := stage13B_complement_coeff_norm_summable n z hz h (!b)
  let f : SpectralScalarL2 := NlsGge.Analysis.naturalPhysicalCoverL2 (φ b)
  have hmem : MemLp (fun x : SpectralCircle => f x * g x) 2 spectralHaar :=
    stage13C_product_memLp f g
  have hactual_ae : (fun x : SpectralCircle => f x * g x) =ᵐ[spectralHaar]
      (fun x => f x * complementaryMultiplier n z hz h (!b) x) := by
    filter_upwards [hvg] with x hv
    exact congrArg (fun t : ℂ => f x * t) hv.symm
  have hactual_mem : MemLp (fun x : SpectralCircle =>
      f x * complementaryMultiplier n z hz h (!b) x) 2 spectralHaar :=
    (memLp_congr_ae hactual_ae).mp hmem
  let p : SpectralScalarL2 := hmem.toLp (fun x : SpectralCircle => f x * g x)
  have hproduct (l : ℤ) :
      Summable (fun m : ℤ =>
        fourierCoeff (complementaryMultiplier n z hz h (!b)) m *
          fourierCoeff f (l - m)) ∧
        fourierCoeff p l =
          ∑' m : ℤ,
            fourierCoeff (complementaryMultiplier n z hz h (!b)) m *
              fourierCoeff f (l - m) := by
    exact stage13C_productLp_fourierCoeff f
      (fun m => fourierCoeff (complementaryMultiplier n z hz h (!b)) m)
      g ha hseries l
  have hq_coeff (l : ℤ) :
      fourierCoeff (NlsGge.Atomic.KST006.qOperator φ n z hz h b) l =
        ∑' m : ℤ, fourierCoeff f (l - m) *
          fourierCoeff (complementaryMultiplier n z hz h (!b)) m := by
    cases b
    · change fourierCoeff (NlsGge.Atomic.KST006.qOperator φ n z hz h false) l =
        ∑' m : ℤ,
          fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 (φ false)) (l - m) *
            fourierCoeff (complementaryMultiplier n z hz h true) m
      have hc := NlsGge.Atomic.KST006.qOperator_lower_coeff φ n z hz h l
      change stage13A_scalarBasis.repr
          (NlsGge.Atomic.KST006.qOperator φ n z hz h false) l =
        ∑' m : ℤ,
          fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 (φ false)) (l - m) *
            (complementaryResolventCoeff n z (-m) *
              stage13A_scalarBasis.repr (h true) m) at hc
      simp only [stage13A_scalarBasis_repr] at hc
      rw [hc]
      apply tsum_congr
      intro m
      rw [stage13A_coeff_complement]
      simp [sourceModeIndex]
    · change fourierCoeff (NlsGge.Atomic.KST006.qOperator φ n z hz h true) l =
        ∑' m : ℤ,
          fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 (φ true)) (l - m) *
            fourierCoeff (complementaryMultiplier n z hz h false) m
      have hc := NlsGge.Atomic.KST006.qOperator_upper_coeff φ n z hz h l
      change stage13A_scalarBasis.repr
          (NlsGge.Atomic.KST006.qOperator φ n z hz h true) l =
        ∑' m : ℤ,
          fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 (φ true)) (l - m) *
            (complementaryResolventCoeff n z m *
              stage13A_scalarBasis.repr (h false) m) at hc
      simp only [stage13A_scalarBasis_repr] at hc
      rw [hc]
      apply tsum_congr
      intro m
      rw [stage13A_coeff_complement]
      simp [sourceModeIndex]
  have heq : NlsGge.Atomic.KST006.qOperator φ n z hz h b = p := by
    apply stage13A_scalarBasis.repr.injective
    apply lp.ext
    funext l
    simp only [stage13A_scalarBasis_repr]
    obtain ⟨hsum, hcoeff⟩ := hproduct l
    calc
      fourierCoeff (NlsGge.Atomic.KST006.qOperator φ n z hz h b) l =
          ∑' m : ℤ, fourierCoeff f (l - m) *
            fourierCoeff (complementaryMultiplier n z hz h (!b)) m := hq_coeff l
      _ = ∑' m : ℤ,
          fourierCoeff (complementaryMultiplier n z hz h (!b)) m *
            fourierCoeff f (l - m) := by
        apply tsum_congr
        intro m
        exact mul_comm _ _
      _ = fourierCoeff p l := hcoeff.symm
  have hp_ae : (p : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x : SpectralCircle => f x * g x) := hmem.coeFn_toLp
  refine ⟨hactual_mem, ?_⟩
  rw [heq]
  exact hp_ae.trans hactual_ae

/-- An arbitrary actual L2 representative of the two potential products is
identified with the public Q-operator only after the general product/AE
identity has been earned above. This is not an extra premise on a potential. -/
private lemma stage13D_qOperator_eq_of_actual_product
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h w : KSTPairL2)
    (hproduct : ∀ b : Bool,
      (w b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
          complementaryMultiplier n z hz h (!b) x)) :
    NlsGge.Atomic.KST006.qOperator φ n z hz h = w := by
  apply PiLp.ext
  intro b
  exact Lp.ext ((stage13D_qOperator_component_product φ n z hz h b).2.trans
    (hproduct b).symm)

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED private fragment. Requires locally re-earned A/B/C/D,
   and only PUBLIC frozen KST012 declarations. No public head is proposed.
   The unit premise is a genuine generic invertibility condition, to be
   discharged by the locally-uniform public KST012 theorem in final assembly.
   The potential-product witnesses are literal graph/domain data, not an
   assumed multiplication operator or extra regularity on the potential. -/

private lemma stage13F_arbitrary_graph_reconstruction
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f g : KSTPairL2)
    (hgraph : HasKSTFreeDiracGraph f (z • f - g))
    (hproduct : ∀ b : Bool,
      (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x))
    (hunit : IsUnit (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)) :
    g - NlsGge.Atomic.KST012.potentialOnPn φ n (spectralPn n f) =
        NlsGge.Atomic.KST012.qEquationSolution φ n z hz (spectralPn n f) ∧
      NlsGge.Atomic.KST012.reconstructedComplement φ n z hz (spectralPn n f) =
        spectralQn n f ∧
      f = spectralPn n f +
        NlsGge.Atomic.KST012.reconstructedComplement φ n z hz (spectralPn n f) := by
  let u : KSTPairL2 := spectralPn n f
  let p : KSTPairL2 := NlsGge.Atomic.KST012.potentialOnPn φ n u
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
  have hu : spectralPn n u = u := by
    have hi := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S f)
      (spectralPn_idempotent n)
    simpa only [ContinuousLinearMap.comp_apply] using hi
  have hp := NlsGge.Atomic.KST012.potentialOnPn_ae φ n u hu
  have hpAE (b : Bool) :
      (p b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * u (!b) x) := by
    cases b
    · simpa only [Bool.not_false] using hp.2
    · simpa only [Bool.not_true] using hp.1
  have hM : complementaryMultiplier n z hz g = spectralQn n f :=
    stage13A_complementary_left_inverse n z hz f g hgraph
  have hM_AE (b : Bool) :
      (complementaryMultiplier n z hz g (!b) : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => f (!b) x - u (!b) x) := by
    rw [hM]
    change ((f (!b) - u (!b) : SpectralScalarL2) : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => f (!b) x - u (!b) x)
    exact Lp.coeFn_sub (f (!b)) (u (!b))
  have hwAE (b : Bool) :
      ((g - p) b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
          complementaryMultiplier n z hz g (!b) x) := by
    change ((g b - p b : SpectralScalarL2) : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
        complementaryMultiplier n z hz g (!b) x)
    filter_upwards [hproduct b, hpAE b, Lp.coeFn_sub (g b) (p b), hM_AE b]
      with x hg hp' hsub hm
    rw [hsub]
    change g b x - p b x =
      NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
        complementaryMultiplier n z hz g (!b) x
    rw [hg, hp', hm]
    ring
  have hTg : T g = g - p :=
    stage13D_qOperator_eq_of_actual_product φ n z hz g (g - p) hwAE
  have hw : (1 - T) (g - p) = T p := by
    change (g - p) - T (g - p) = T p
    rw [map_sub, hTg]
    abel
  have hback : Ring.inverse (1 - T) ((1 - T) (g - p)) = g - p := by
    have hi := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S (g - p))
      (Ring.inverse_mul_cancel (1 - T) hunit)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using hi
  have hw_solution : g - p =
      NlsGge.Atomic.KST012.qEquationSolution φ n z hz u := by
    calc
      g - p = Ring.inverse (1 - T) ((1 - T) (g - p)) := hback.symm
      _ = Ring.inverse (1 - T) (T p) := congrArg (fun v : KSTPairL2 => Ring.inverse (1 - T) v) hw
      _ = NlsGge.Atomic.KST012.qEquationSolution φ n z hz u := by rfl
  have hv_reconstruction :
      NlsGge.Atomic.KST012.reconstructedComplement φ n z hz u = spectralQn n f := by
    calc
      NlsGge.Atomic.KST012.reconstructedComplement φ n z hz u =
          complementaryMultiplier n z hz (p +
            NlsGge.Atomic.KST012.qEquationSolution φ n z hz u) := by rfl
      _ = complementaryMultiplier n z hz (p + (g - p)) := by rw [← hw_solution]
      _ = complementaryMultiplier n z hz g := by
        congr 1
        abel
      _ = spectralQn n f := hM
  refine ⟨hw_solution, hv_reconstruction, ?_⟩
  rw [hv_reconstruction]
  change f = spectralPn n f + (f - spectralPn n f)
  abel
/- INERT / UNCOMPILED private continuation after locally proved ABCDF.
   This is actual graph-domain injectivity, not a new standing hypothesis. -/

private lemma stage13G_weakDerivative_sub
    {u₁ u₂ v₁ v₂ : SpectralScalarL2}
    (h₁ : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 u₁ v₁)
    (h₂ : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 u₂ v₂) :
    NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 (u₁ - u₂) (v₁ - v₂) := by
  have hraw
      (a b c d : Lp ℂ 2 (@AddCircle.haarAddCircle (2 : ℝ) inferInstance))
      (ha : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 a c)
      (hb : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 b d) :
      NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 (a - b) (c - d) := by
    intro test
    simp only [inner_sub_right]
    rw [ha test, hb test]
    ring
  simpa only [SpectralCircle, SpectralScalarL2, spectralHaar] using!
    (hraw u₁ u₂ v₁ v₂ h₁ h₂)

private lemma stage13G_freeGraph_sub
    {f₁ f₂ y₁ y₂ : KSTPairL2}
    (h₁ : HasKSTFreeDiracGraph f₁ y₁)
    (h₂ : HasKSTFreeDiracGraph f₂ y₂) :
    HasKSTFreeDiracGraph (f₁ - f₂) (y₁ - y₂) := by
  obtain ⟨du₁, dl₁, hdu₁, hdl₁, hy₁⟩ := h₁
  obtain ⟨du₂, dl₂, hdu₂, hdl₂, hy₂⟩ := h₂
  refine ⟨du₁ - du₂, dl₁ - dl₂,
    stage13G_weakDerivative_sub hdu₁ hdu₂,
    stage13G_weakDerivative_sub hdl₁ hdl₂, ?_⟩
  rw [hy₁, hy₂]
  apply PiLp.ext
  intro b
  cases b <;> simp [smul_sub]

lemma stage13G_projection_zero_forces_zero
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f g : KSTPairL2)
    (hgraph : HasKSTFreeDiracGraph f (z • f - g))
    (hproduct : ∀ b : Bool,
      (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x))
    (hunit : IsUnit (1 - NlsGge.Atomic.KST006.qOperator φ n z hz))
    (hzero : spectralPn n f = 0) : f = 0 := by
  have hf := (stage13F_arbitrary_graph_reconstruction φ n z hz f g
    hgraph hproduct hunit).2.2
  rw [hzero] at hf
  simpa only [NlsGge.Atomic.KST012.reconstructedComplement,
    NlsGge.Atomic.KST012.qEquationSolution, map_zero, add_zero, zero_add] using hf

private lemma stage13G_projection_injective_on_actual_eigenpairs
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f₁ g₁ f₂ g₂ : KSTPairL2)
    (hgraph₁ : HasKSTFreeDiracGraph f₁ (z • f₁ - g₁))
    (hgraph₂ : HasKSTFreeDiracGraph f₂ (z • f₂ - g₂))
    (hproduct₁ : ∀ b : Bool,
      (g₁ b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f₁ (!b) x))
    (hproduct₂ : ∀ b : Bool,
      (g₂ b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f₂ (!b) x))
    (hunit : IsUnit (1 - NlsGge.Atomic.KST006.qOperator φ n z hz))
    (hequal : spectralPn n f₁ = spectralPn n f₂) : f₁ = f₂ := by
  have hgraph : HasKSTFreeDiracGraph (f₁ - f₂) (z • (f₁ - f₂) - (g₁ - g₂)) := by
    have h := stage13G_freeGraph_sub hgraph₁ hgraph₂
    have hout : (z • f₁ - g₁) - (z • f₂ - g₂) =
        z • (f₁ - f₂) - (g₁ - g₂) := by
      rw [smul_sub]
      abel
    rw [hout] at h
    exact h
  have hproduct (b : Bool) :
      ((g₁ - g₂) b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
          (f₁ - f₂) (!b) x) := by
    change ((g₁ b - g₂ b : SpectralScalarL2) : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
        (f₁ (!b) - f₂ (!b)) x)
    filter_upwards [hproduct₁ b, hproduct₂ b, Lp.coeFn_sub (g₁ b) (g₂ b),
      Lp.coeFn_sub (f₁ (!b)) (f₂ (!b))] with x hg₁ hg₂ hsubg hsubf
    rw [hsubg, hsubf]
    change g₁ b x - g₂ b x =
      NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
        (f₁ (!b) x - f₂ (!b) x)
    rw [hg₁, hg₂]
    ring
  have hzero : spectralPn n (f₁ - f₂) = 0 := by
    rw [map_sub, hequal, sub_self]
  exact sub_eq_zero.mp
    (stage13G_projection_zero_forces_zero φ n z hz (f₁ - f₂) (g₁ - g₂)
      hgraph hproduct hunit hzero)

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED. Exact private P-equation ingredients from the actual
   all-test graph and full Fourier masks. No public reduced-map definition
   or kernel/eigenvalue command is introduced by this fragment. -/

private lemma stage13H_freeGraph_projected_output
    (n : ℤ) {v y : KSTPairL2} (hgraph : HasKSTFreeDiracGraph v y) :
    spectralPn n y = ((n : ℂ) * (Real.pi : ℂ)) • spectralPn n v := by
  apply PiLp.ext
  intro b
  apply stage13A_scalarBasis.repr.injective
  apply lp.ext
  funext m
  rw [stage13A_scalarBasis_repr, stage13A_scalarBasis_repr]
  change fourierCoeff (spectralPn n y b) m =
    fourierCoeff (((n : ℂ) * (Real.pi : ℂ)) • spectralPn n v b) m
  rw [stage13A_coeff_smul, stage13A_coeff_Pn, stage13A_coeff_Pn]
  by_cases hkn : sourceModeIndex b m = n
  · rw [if_pos hkn, if_pos hkn, stage13A_free_graph_coeff hgraph b m, hkn]
  · rw [if_neg hkn, if_neg hkn, mul_zero]

private lemma stage13H_projected_actual_eigen_equation
    (n : ℤ) (z : ℂ) (f g : KSTPairL2)
    (hgraph : HasKSTFreeDiracGraph f (z • f - g)) :
    spectralPn n g = (z - (n : ℂ) * (Real.pi : ℂ)) • spectralPn n f := by
  have hp := stage13H_freeGraph_projected_output n hgraph
  rw [map_sub, map_smul] at hp
  calc
    spectralPn n g = z • spectralPn n f -
        (z • spectralPn n f - spectralPn n g) := by abel
    _ = z • spectralPn n f - ((n : ℂ) * (Real.pi : ℂ)) • spectralPn n f := by rw [hp]
    _ = (z - (n : ℂ) * (Real.pi : ℂ)) • spectralPn n f :=
      (sub_smul z ((n : ℂ) * (Real.pi : ℂ)) (spectralPn n f)).symm

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED private consumption after actual F/G and reviewed H.
   The source forward reduced equation is earned from the actual graph and
   actual product witness. No reduced-map field or extra final premise is
   introduced; hunit is later supplied by the SAME public012 epsilon,N0. -/

lemma stage13K_actual_forward_reduced_formula
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f g : KSTPairL2)
    (hgraph : HasKSTFreeDiracGraph f (z • f - g))
    (hproduct : ∀ b : Bool,
      (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x))
    (hunit : IsUnit (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)) :
    (z - (n : ℂ) * (Real.pi : ℂ)) • spectralPn n f =
      spectralPn n
        (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)
          (NlsGge.Atomic.KST012.potentialOnPn φ n (spectralPn n f))) := by
  let u : KSTPairL2 := spectralPn n f
  let p : KSTPairL2 := NlsGge.Atomic.KST012.potentialOnPn φ n u
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
  have hw_solution : g - p =
      NlsGge.Atomic.KST012.qEquationSolution φ n z hz u :=
    (stage13F_arbitrary_graph_reconstruction φ n z hz f g hgraph hproduct hunit).1
  have hw : (1 - T) (g - p) = T p := by
    rw [hw_solution]
    change (1 - T) (Ring.inverse (1 - T) (T p)) = T p
    have hi := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S (T p))
      (Ring.mul_inverse_cancel (1 - T) hunit)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using hi
  have hag : (1 - T) g = p := by
    have heq := hw
    rw [map_sub] at heq
    change (1 - T) g - (p - T p) = T p at heq
    have hzero : (1 - T) g - p = 0 := by
      calc
        (1 - T) g - p = ((1 - T) g - (p - T p)) - T p := by abel
        _ = T p - T p := by rw [heq]
        _ = 0 := sub_self _
    exact sub_eq_zero.mp hzero
  have hback : Ring.inverse (1 - T) ((1 - T) g) = g := by
    have hi := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S g)
      (Ring.inverse_mul_cancel (1 - T) hunit)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using hi
  have hginv : g = Ring.inverse (1 - T) p := by
    calc
      g = Ring.inverse (1 - T) ((1 - T) g) := hback.symm
      _ = Ring.inverse (1 - T) p :=
        congrArg (fun v : KSTPairL2 => Ring.inverse (1 - T) v) hag
  calc
    (z - (n : ℂ) * (Real.pi : ℂ)) • spectralPn n f = spectralPn n g :=
      (stage13H_projected_actual_eigen_equation n z f g hgraph).symm
    _ = spectralPn n (Ring.inverse (1 - T) p) := congrArg (spectralPn n) hginv
    _ = spectralPn n
        (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)
          (NlsGge.Atomic.KST012.potentialOnPn φ n (spectralPn n f))) := by rfl

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED. Source (26a) backward construction on the actual
   doubled weak graph, with the SAME epsilon,N0 earned by public KST012.
   This is a private intermediate command, not a public reduced-map definition. -/

private lemma stage13L_weakDerivative_add {u₁ u₂ v₁ v₂ : SpectralScalarL2}
    (h₁ : LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 u₁ v₁)
    (h₂ : LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 u₂ v₂) :
    LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 (u₁ + u₂) (v₁ + v₂) := by
  have hraw
      (a b c d : Lp ℂ 2 (@AddCircle.haarAddCircle (2 : ℝ) inferInstance))
      (ha : LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 a c)
      (hb : LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 b d) :
      LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 (a + b) (c + d) := by
    intro test
    simp only [inner_add_right]
    rw [ha test, hb test]
    ring
  simpa only [SpectralCircle, SpectralScalarL2, spectralHaar] using!
    (hraw u₁ u₂ v₁ v₂ h₁ h₂)

private lemma stage13L_freeGraph_add {x₁ x₂ y₁ y₂ : KSTPairL2}
    (h₁ : HasKSTFreeDiracGraph x₁ y₁)
    (h₂ : HasKSTFreeDiracGraph x₂ y₂) :
    HasKSTFreeDiracGraph (x₁ + x₂) (y₁ + y₂) := by
  obtain ⟨du₁, dl₁, hdu₁, hdl₁, hy₁⟩ := h₁
  obtain ⟨du₂, dl₂, hdu₂, hdl₂, hy₂⟩ := h₂
  refine ⟨du₁ + du₂, dl₁ + dl₂,
    stage13L_weakDerivative_add hdu₁ hdu₂,
    stage13L_weakDerivative_add hdl₁ hdl₂, ?_⟩
  rw [hy₁, hy₂]
  apply PiLp.ext
  intro b
  cases b <;> simp [smul_add]

private lemma stage13L_actual_backward_locally
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ ψ : NlsGge.Atomic.KST002.PhysicalPairLp, ‖ψ - φ‖ < ε →
        ∀ n : ℤ, N₀ ≤ n.natAbs →
          ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
            IsUnit (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz) ∧
            ∀ u : KSTPairL2, spectralPn n u = u →
            (z - (n : ℂ) * (Real.pi : ℂ)) • u =
              spectralPn n
                (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz)
                  (NlsGge.Atomic.KST012.potentialOnPn ψ n u)) →
            let v := NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u
            let g := NlsGge.Atomic.KST012.potentialOnPn ψ n u +
              NlsGge.Atomic.KST012.qEquationSolution ψ n z hz u
            HasKSTFreeDiracGraph (u + v) (z • (u + v) - g) ∧
            (∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
              (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x *
                (u + v) (!b) x)) ∧
            spectralPn n (u + v) = u ∧
            (u ≠ 0 → u + v ≠ 0) := by
  obtain ⟨ε, hε, N₀, hN₀, hlocal⟩ := NlsGge.Atomic.KST012.qEquation_solve_locally φ
  refine ⟨ε, hε, N₀, hN₀, ?_⟩
  intro ψ hψ n hn z hz
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator ψ n z hz
  obtain ⟨hunit, _hformula, _hright, _hleft, hsol⟩ := hlocal ψ hψ n hn z hz
  refine ⟨hunit, ?_⟩
  intro u hu hred
  dsimp only
  let p : KSTPairL2 := NlsGge.Atomic.KST012.potentialOnPn ψ n u
  let w : KSTPairL2 := NlsGge.Atomic.KST012.qEquationSolution ψ n z hz u
  let v : KSTPairL2 := NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u
  let g : KSTPairL2 := p + w
  let c : ℂ := (n : ℂ) * (Real.pi : ℂ)
  obtain ⟨hw, _huniq, hqrange, hgraphv, hup, hlow⟩ := hsol u hu
  have hag : (1 - T) g = p := by
    have heq : w - T w = T p := by
      simpa only [sub_apply, one_apply_eq_self] using hw
    change (1 - T) (p + w) = p
    rw [map_add]
    change (p - T p) + (w - T w) = p
    rw [heq]
    abel
  have hginv : g = Ring.inverse (1 - T) p := by
    have hi := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S g)
      (Ring.inverse_mul_cancel (1 - T) hunit)
    have hback : Ring.inverse (1 - T) ((1 - T) g) = g := by
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using hi
    calc
      g = Ring.inverse (1 - T) ((1 - T) g) := hback.symm
      _ = Ring.inverse (1 - T) p := congrArg (fun x : KSTPairL2 => Ring.inverse (1 - T) x) hag
  have hpg : spectralPn n g = (z - c) • u := by
    rw [hginv]
    exact hred.symm
  have hgraphu : HasKSTFreeDiracGraph u (c • u) := by
    have h := kstFreeDirac_on_Pn n u
    rw [hu] at h
    have hscalar : ((n * Real.pi : ℝ) : ℂ) = c := by
      dsimp only [c]
      push_cast
      rfl
    have hreal : HasKSTFreeDiracGraph u (((n * Real.pi : ℝ) : ℂ) • u) := by
      simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := KSTPairL2)] using! h
    rw [hscalar] at hreal
    exact hreal
  have hgraph : HasKSTFreeDiracGraph (u + v) (z • (u + v) - g) := by
    have h := stage13L_freeGraph_add hgraphu hgraphv
    have hout : c • u + (z • v - spectralQn n g) = z • (u + v) - g := by
      change c • u + (z • v - (g - spectralPn n g)) = _
      rw [hpg, sub_smul, smul_add]
      abel
    rw [hout] at h
    exact h
  have hproduct (b : Bool) :
      (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * (u + v) (!b) x) := by
    have hp : (p b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * u (!b) x) := by
      have hpae := NlsGge.Atomic.KST012.potentialOnPn_ae ψ n u hu
      cases b
      · simpa only [Bool.not_false] using hpae.2
      · simpa only [Bool.not_true] using hpae.1
    have hwprod : (w b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * v (!b) x) := by
      cases b
      · simpa only [Bool.not_false] using hlow
      · simpa only [Bool.not_true] using hup
    change ((p b + w b : SpectralScalarL2) : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * (u (!b) + v (!b)) x)
    filter_upwards [hp, hwprod, Lp.coeFn_add (p b) (w b),
      Lp.coeFn_add (u (!b)) (v (!b))] with x hpx hwx hsumg hsumf
    rw [hsumg, hsumf]
    change p b x + w b x =
      NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * (u (!b) x + v (!b) x)
    rw [hpx, hwx]
    ring
  have hpv : spectralPn n v = 0 := by
    have hq : v - spectralPn n v = v := hqrange
    have heq : spectralPn n v = 0 := by
      have : v - spectralPn n v - v = 0 := sub_eq_zero.mpr hq
      have hz : -(spectralPn n v) = 0 := by
        calc
          -(spectralPn n v) = v - spectralPn n v - v := by abel
          _ = 0 := this
      exact neg_eq_zero.mp hz
    exact heq
  have hpuv : spectralPn n (u + v) = u := by rw [map_add, hu, hpv, add_zero]
  refine ⟨hgraph, hproduct, hpuv, ?_⟩
  intro hne hzero
  apply hne
  calc
    u = spectralPn n (u + v) := hpuv.symm
    _ = 0 := by rw [hzero, map_zero]

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED. The raw actual period-two graph/kernel equivalence
   consuming L02, K and G. No public reduced-map definition is activated. -/

private lemma stage13M_actual_uniform_raw_kernel_equivalence
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ ψ : NlsGge.Atomic.KST002.PhysicalPairLp, ‖ψ - φ‖ < ε →
        ∀ n : ℤ, N₀ ≤ n.natAbs →
          ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
            ((∃ f g : KSTPairL2, f ≠ 0 ∧
                HasKSTFreeDiracGraph f (z • f - g) ∧
                ∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
                  (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * f (!b) x)) ↔
              ∃ u : KSTPairL2, u ≠ 0 ∧ spectralPn n u = u ∧
                (z - (n : ℂ) * (Real.pi : ℂ)) • u =
                  spectralPn n
                    (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz)
                      (NlsGge.Atomic.KST012.potentialOnPn ψ n u))) ∧
            ∀ f₁ g₁ f₂ g₂ : KSTPairL2,
              HasKSTFreeDiracGraph f₁ (z • f₁ - g₁) →
              HasKSTFreeDiracGraph f₂ (z • f₂ - g₂) →
              (∀ b : Bool, (g₁ b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
                (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * f₁ (!b) x)) →
              (∀ b : Bool, (g₂ b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
                (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * f₂ (!b) x)) →
              spectralPn n f₁ = spectralPn n f₂ → f₁ = f₂ := by
  obtain ⟨ε, hε, N₀, hN₀, hlocal⟩ := stage13L_actual_backward_locally φ
  refine ⟨ε, hε, N₀, hN₀, ?_⟩
  intro ψ hψ n hn z hz
  obtain ⟨hunit, hback⟩ := hlocal ψ hψ n hn z hz
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨f, g, hf, hgraph, hproduct⟩
      have hpu : spectralPn n (spectralPn n f) = spectralPn n f := by
        have hi := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S f)
          (spectralPn_idempotent n)
        simpa only [ContinuousLinearMap.comp_apply] using hi
      have hpne : spectralPn n f ≠ 0 := by
        intro hpzero
        exact hf (stage13G_projection_zero_forces_zero ψ n z hz f g
          hgraph hproduct hunit hpzero)
      exact ⟨spectralPn n f, hpne, hpu,
        stage13K_actual_forward_reduced_formula ψ n z hz f g hgraph hproduct hunit⟩
    · rintro ⟨u, hu_ne, hu, hred⟩
      obtain ⟨hgraph, hproduct, _hprojection, hnonzero⟩ := hback u hu hred
      exact ⟨u + NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u,
        NlsGge.Atomic.KST012.potentialOnPn ψ n u +
          NlsGge.Atomic.KST012.qEquationSolution ψ n z hz u,
        hnonzero hu_ne, hgraph, hproduct⟩
  · intro f₁ g₁ f₂ g₂ hgraph₁ hgraph₂ hproduct₁ hproduct₂ heq
    exact stage13G_projection_injective_on_actual_eigenpairs ψ n z hz f₁ g₁ f₂ g₂
      hgraph₁ hgraph₂ hproduct₁ hproduct₂ hunit heq

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED. Actual coefficient transport for the domain bridge.
   Both parity sectors and the existing reflected mixedIndex are retained.
   This lemma identifies coefficients only, not a Dirac action or H1_loc domain. -/

private lemma stage13P_coeff_add (f g : SpectralScalarL2) (m : ℤ) :
    fourierCoeff (f + g) m = fourierCoeff f m + fourierCoeff g m := by
  rw [← stage13A_scalarBasis_repr, ← stage13A_scalarBasis_repr,
    ← stage13A_scalarBasis_repr, map_add]
  rfl

private lemma stage13P_scalar_parity_repr_eq_coeff (n : ℤ)
    (u : scalarParity n) (m : Sector n) :
    scalarParityRepr n u m = fourierCoeff (u : SpectralScalarL2) m.val := by
  rw [scalarParityRepr_apply]
  change stage13A_scalarBasis.repr (u : SpectralScalarL2) m.val = _
  exact stage13A_scalarBasis_repr (u : SpectralScalarL2) m.val

private lemma stage13P_half_translation_coeff (u : SpectralScalarL2) (m : ℤ) :
    fourierCoeff (halfTranslation u) m = spectralSign m * fourierCoeff u m := by
  have h := halfTranslation_repr u m
  change stage13A_scalarBasis.repr (halfTranslation u) m =
    spectralSign m * stage13A_scalarBasis.repr u m at h
  simpa only [stage13A_scalarBasis_repr] using h

private lemma stage13P_actual_parity_projection_coeff
    (u : SpectralScalarL2) (p : Fin 2) (m : Sector (p.val : ℤ)) :
    scalarParityRepr (p.val : ℤ) (actualScalarParityProjectionLinearEquiv u p) m =
      fourierCoeff u m.val := by
  fin_cases p
  · change scalarParityRepr (0 : ℤ) (actualEvenParityProjection u) m = _
    rw [stage13P_scalar_parity_repr_eq_coeff]
    change fourierCoeff ((2 : ℂ)⁻¹ • (u + halfTranslation u)) m.val = _
    rw [stage13A_coeff_smul, stage13P_coeff_add, stage13P_half_translation_coeff]
    have hsign : spectralSign m.val = 1 := by
      have hp : m.val % 2 = 0 := by simpa only [Int.natCast_zero, Int.zero_emod] using m.property
      simp only [spectralSign, hp, ite_true]
    rw [hsign]
    norm_num <;> ring
  · change scalarParityRepr (1 : ℤ) (actualOddParityProjection u) m = _
    rw [stage13P_scalar_parity_repr_eq_coeff]
    change fourierCoeff ((2 : ℂ)⁻¹ • (u - halfTranslation u)) m.val = _
    rw [stage13A_coeff_smul, stage13A_coeff_sub, stage13P_half_translation_coeff]
    have hsign : spectralSign m.val = -1 := by
      have hp : m.val % 2 = 1 := by simpa only [Int.natCast_one, Int.one_emod_two] using m.property
      simp only [spectralSign, hp, one_ne_zero, ite_false]
    rw [hsign]
    norm_num <;> ring

private lemma stage13P_actual_full_assembly_repr
    (f : KSTPairL2) (p : Fin 2) (i : Bool × Sector (p.val : ℤ)) :
    sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly f p) i =
      fourierCoeff (f i.1) (mixedIndex (p.val : ℤ) i).val := by
  let a : ParityPair (p.val : ℤ) := WithLp.toLp 2
    (fun b : Bool => actualScalarParityProjectionLinearEquiv (f b) p)
  change parityPairRepr (p.val : ℤ)
    ((parityPairIntervalEquiv (p.val : ℤ)).symm
      ((parityPairIntervalEquiv (p.val : ℤ)) a)) i = _
  rw [(parityPairIntervalEquiv (p.val : ℤ)).symm_apply_apply, parityPairRepr_apply]
  change scalarParityRepr (p.val : ℤ)
    (actualScalarParityProjectionLinearEquiv (f i.1) p) (mixedIndex (p.val : ℤ) i) = _
  exact stage13P_actual_parity_projection_coeff (f i.1) p (mixedIndex (p.val : ℤ) i)


/- INERT / UNCOMPILED. Forward graph-domain/action transport using actual P
   coefficients. KST's free action is NEGATIVE the existing project free
   block action under this unswapped assembly. No perturbed or H1_loc claim. -/

private lemma stage13Q_actual_source_weighted_coordinates
    {f y : KSTPairL2} (hgraph : HasKSTFreeDiracGraph f y)
    (p : Fin 2) (i : Bool × Sector (p.val : ℤ)) :
    spectralCenter i.2.val *
        sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly f p) i =
      -(sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly y p) i) := by
  rw [stage13P_actual_full_assembly_repr, stage13P_actual_full_assembly_repr,
    stage13A_free_graph_coeff hgraph]
  have hindex : sourceModeIndex i.1 (mixedIndex (p.val : ℤ) i).val = -i.2.val := by
    rcases i with ⟨b, m⟩
    cases b <;> simp [sourceModeIndex, mixedIndex, negateIndex]
  rw [hindex]
  simp only [spectralCenter, Int.cast_neg, neg_mul, neg_neg]

private lemma stage13Q_graph_to_actual_source_block_domain_and_negative_free_action
    {f y : KSTPairL2} (hgraph : HasKSTFreeDiracGraph f y) :
    f ∈ actualFullPeriodTwoSourceDoubledCircleDomain ∧
      ∀ (p : Fin 2)
        (hp : actualFullPeriodTwoSourceIntervalAssembly f p ∈
          NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (p.val : ℤ)),
        actualFullPeriodTwoSourceIntervalAssembly y p =
          -actualSourceFreeDiracMapAfterAE (p.val : ℤ)
            ⟨actualFullPeriodTwoSourceIntervalAssembly f p, hp⟩ := by
  have hblock (p : Fin 2) : actualFullPeriodTwoSourceIntervalAssembly f p ∈
      NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (p.val : ℤ) := by
    change Memℓp (fun i : Bool × Sector (p.val : ℤ) =>
      spectralCenter i.2.val *
        sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly f p) i) 2
    have heq : (fun i : Bool × Sector (p.val : ℤ) =>
        spectralCenter i.2.val *
          sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly f p) i) =
        -(sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly y p) :
          Bool × Sector (p.val : ℤ) → ℂ) := by
      funext i
      exact stage13Q_actual_source_weighted_coordinates hgraph p i
    rw [heq]
    exact (lp.memℓp
      (sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly y p))).neg
  refine ⟨?_, ?_⟩
  · change ∀ p : Fin 2, actualFullPeriodTwoSourceIntervalAssembly f p ∈
      NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (p.val : ℤ)
    exact hblock
  · intro p hp
    apply (sourcePairRepr (p.val : ℤ)).injective
    rw [map_neg, actualSourceFreeDiracMapAfterAE_repr_apply]
    apply lp.ext
    funext i
    change sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly y p) i =
      -(spectralCenter i.2.val *
        sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly f p) i)
    calc
      sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly y p) i =
          -(-sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly y p) i) :=
        (neg_neg _).symm
      _ = -(spectralCenter i.2.val *
          sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly f p) i) :=
        congrArg (fun a : ℂ => -a)
          (stage13Q_actual_source_weighted_coordinates hgraph p i).symm

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED converse actual domain bridge. No potential or H1_loc
   extension is inferred. All signed coefficients, both parity sectors and
   both Bool components are explicitly retained. -/

private lemma stage13R_free_graph_of_coefficients (f y : KSTPairL2)
    (hcoeff : ∀ (b : Bool) (m : ℤ), fourierCoeff (y b) m =
      (sourceModeIndex b m : ℂ) * (Real.pi : ℂ) * fourierCoeff (f b) m) :
    HasKSTFreeDiracGraph f y := by
  have hduCoeff (m : ℤ) : fourierCoeff ((-Complex.I) • y true) m =
      NlsGge.Atomic.LIB002.fourierMultiplier (2 : ℝ) m ^ 1 * fourierCoeff (f true) m := by
    rw [stage13A_coeff_smul, hcoeff]
    simp only [NlsGge.Atomic.LIB002.fourierMultiplier, pow_one, sourceModeIndex]
    push_cast
    ring
  have hdu : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1
      (f true) ((-Complex.I) • y true) := by
    apply (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff_iff (T := (2 : ℝ)) (m := 1)).2
    intro m
    simpa only [SpectralCircle, SpectralScalarL2, spectralHaar] using! hduCoeff m
  have hdlCoeff (m : ℤ) : fourierCoeff (Complex.I • y false) m =
      NlsGge.Atomic.LIB002.fourierMultiplier (2 : ℝ) m ^ 1 * fourierCoeff (f false) m := by
    rw [stage13A_coeff_smul, hcoeff]
    simp only [NlsGge.Atomic.LIB002.fourierMultiplier, pow_one, sourceModeIndex]
    push_cast
    ring
  have hdl : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1
      (f false) (Complex.I • y false) := by
    apply (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff_iff (T := (2 : ℝ)) (m := 1)).2
    intro m
    simpa only [SpectralCircle, SpectralScalarL2, spectralHaar] using! hdlCoeff m
  refine ⟨(-Complex.I) • y true, Complex.I • y false, hdu, hdl, ?_⟩
  apply PiLp.ext
  intro b
  cases b <;> simp [smul_smul, Complex.I_mul_I]

private lemma stage13R_actual_source_block_domain_to_weak_graph
    (f : KSTPairL2) (hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain) :
    ∃ y : KSTPairL2, HasKSTFreeDiracGraph f y := by
  have hblock (p : Fin 2) : actualFullPeriodTwoSourceIntervalAssembly f p ∈
      NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (p.val : ℤ) := hf p
  let a : ActualFullPeriodTwoSourcePair := WithLp.toLp 2 (fun p : Fin 2 =>
    -actualSourceFreeDiracMapAfterAE (p.val : ℤ)
      ⟨actualFullPeriodTwoSourceIntervalAssembly f p, hblock p⟩)
  let y : KSTPairL2 := actualFullPeriodTwoSourceIntervalAssembly.symm a
  have hy (p : Fin 2) : actualFullPeriodTwoSourceIntervalAssembly y p =
      -actualSourceFreeDiracMapAfterAE (p.val : ℤ)
        ⟨actualFullPeriodTwoSourceIntervalAssembly f p, hblock p⟩ := by
    have h := congrArg (fun x : ActualFullPeriodTwoSourcePair => x p)
      (actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply a)
    exact h
  have hcoordinate (p : Fin 2) (i : Bool × Sector (p.val : ℤ)) :
      sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly y p) i =
        -(spectralCenter i.2.val *
          sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly f p) i) := by
    rw [hy, map_neg, actualSourceFreeDiracMapAfterAE_repr_apply]
    rfl
  refine ⟨y, stage13R_free_graph_of_coefficients f y ?_⟩
  intro b m
  let k : ℤ := if b then m else -m
  let p : Fin 2 := ⟨(k % 2).toNat, by omega⟩
  let s : Sector (p.val : ℤ) := ⟨k, by dsimp only [p]; omega⟩
  have hmixed : (mixedIndex (p.val : ℤ) (b, s)).val = m := by
    cases b <;> simp [mixedIndex, negateIndex, s, k]
  have hlabel : -s.val = sourceModeIndex b m := by
    cases b <;> simp [s, k, sourceModeIndex]
  have h := hcoordinate p (b, s)
  rw [stage13P_actual_full_assembly_repr, stage13P_actual_full_assembly_repr, hmixed] at h
  calc
    fourierCoeff (y b) m = -(spectralCenter s.val * fourierCoeff (f b) m) := h
    _ = (sourceModeIndex b m : ℂ) * (Real.pi : ℂ) * fourierCoeff (f b) m := by
      rw [← hlabel]
      simp only [spectralCenter, Int.cast_neg, neg_mul]

private lemma stage13R_weak_graph_domain_iff_actual_source_block_domain (f : KSTPairL2) :
    (∃ y : KSTPairL2, HasKSTFreeDiracGraph f y) ↔
      f ∈ actualFullPeriodTwoSourceDoubledCircleDomain := by
  constructor
  · rintro ⟨y, hgraph⟩
    exact (stage13Q_graph_to_actual_source_block_domain_and_negative_free_action hgraph).1
  · exact stage13R_actual_source_block_domain_to_weak_graph f

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED. Actual rough-L2 product transport through both parity
   projections. An actual L2 product witness is preserved, not postulated as
   a final source premise; J earns it on the real weak domain. -/

private lemma stage13S_half_translation_actual_product
    (φ : NlsGge.Pilot.PhysicalL2) (f g : SpectralScalarL2)
    (hproduct : (g : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 φ x * f x)) :
    (halfTranslation g : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 φ x * halfTranslation f x) := by
  have hshift := halfShift_preserving.quasiMeasurePreserving.ae_eq_comp hproduct
  have hφ := halfTranslation_ae (NlsGge.Analysis.naturalPhysicalCoverL2 φ)
  rw [NlsGge.Analysis.naturalPhysicalCoverL2_halfTranslation] at hφ
  filter_upwards [halfTranslation_ae g, hshift, halfTranslation_ae f, hφ]
    with x hg hs hf hφx
  change g (x + ((1 : ℝ) : SpectralCircle)) =
    NlsGge.Analysis.naturalPhysicalCoverL2 φ (x + ((1 : ℝ) : SpectralCircle)) *
      f (x + ((1 : ℝ) : SpectralCircle)) at hs
  calc
    halfTranslation g x = g (x + ((1 : ℝ) : SpectralCircle)) := hg
    _ = NlsGge.Analysis.naturalPhysicalCoverL2 φ (x + ((1 : ℝ) : SpectralCircle)) *
        f (x + ((1 : ℝ) : SpectralCircle)) := hs
    _ = NlsGge.Analysis.naturalPhysicalCoverL2 φ x * halfTranslation f x := by
      rw [← hφx, ← hf]

private lemma stage13S_actual_parity_projection_product
    (φ : NlsGge.Pilot.PhysicalL2) (f g : SpectralScalarL2)
    (hproduct : (g : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 φ x * f x))
    (p : Fin 2) :
    ((actualScalarParityProjectionLinearEquiv g p : SpectralScalarL2) :
      SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 φ x *
        (actualScalarParityProjectionLinearEquiv f p : SpectralScalarL2) x) := by
  have hshift := stage13S_half_translation_actual_product φ f g hproduct
  fin_cases p
  · change (((2 : ℂ)⁻¹ • (g + halfTranslation g) : SpectralScalarL2) :
      SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 φ x *
        ((2 : ℂ)⁻¹ • (f + halfTranslation f) : SpectralScalarL2) x)
    filter_upwards [hproduct, hshift,
      Lp.coeFn_smul (2 : ℂ)⁻¹ (g + halfTranslation g),
      Lp.coeFn_add g (halfTranslation g),
      Lp.coeFn_smul (2 : ℂ)⁻¹ (f + halfTranslation f),
      Lp.coeFn_add f (halfTranslation f)] with x hg ht hsg hag hsf haf
    rw [hsg, hsf]
    change (2 : ℂ)⁻¹ * (g + halfTranslation g) x =
      NlsGge.Analysis.naturalPhysicalCoverL2 φ x *
        ((2 : ℂ)⁻¹ * (f + halfTranslation f) x)
    rw [hag, haf]
    change (2 : ℂ)⁻¹ * (g x + halfTranslation g x) =
      NlsGge.Analysis.naturalPhysicalCoverL2 φ x *
        ((2 : ℂ)⁻¹ * (f x + halfTranslation f x))
    rw [hg, ht]
    ring
  · change (((2 : ℂ)⁻¹ • (g - halfTranslation g) : SpectralScalarL2) :
      SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 φ x *
        ((2 : ℂ)⁻¹ • (f - halfTranslation f) : SpectralScalarL2) x)
    filter_upwards [hproduct, hshift,
      Lp.coeFn_smul (2 : ℂ)⁻¹ (g - halfTranslation g),
      Lp.coeFn_sub g (halfTranslation g),
      Lp.coeFn_smul (2 : ℂ)⁻¹ (f - halfTranslation f),
      Lp.coeFn_sub f (halfTranslation f)] with x hg ht hsg hag hsf haf
    rw [hsg, hsf]
    change (2 : ℂ)⁻¹ * (g - halfTranslation g) x =
      NlsGge.Analysis.naturalPhysicalCoverL2 φ x *
        ((2 : ℂ)⁻¹ * (f - halfTranslation f) x)
    rw [hag, haf]
    change (2 : ℂ)⁻¹ * (g x - halfTranslation g x) =
      NlsGge.Analysis.naturalPhysicalCoverL2 φ x *
        ((2 : ℂ)⁻¹ * (f x - halfTranslation f x))
    rw [hg, ht]
    ring


/- INERT / UNCOMPILED. Actual potential-product transport. The input domain
   is the already-defined proper source block domain, not an H1-potential
   premise. No free-action or global endpoint assertion is made here. -/

private lemma stage13T_actual_source_interval_product
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (f g : KSTPairL2)
    (hproduct : ∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x))
    (p : Fin 2) (b : Bool) :
    (actualFullPeriodTwoSourceIntervalAssembly g p b : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun t => actualPhysicalL2SourcePotential (φ b) t *
        actualFullPeriodTwoSourceIntervalAssembly f p (!b) t) := by
  have hparity := stage13S_actual_parity_projection_product (φ b) (f (!b)) (g b)
    (hproduct b) p
  have hpull := spectral_ae_pullback_first_half hparity
  have hg : (actualFullPeriodTwoSourceIntervalAssembly g p b : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun t => (actualScalarParityProjectionLinearEquiv (g b) p : SpectralScalarL2)
        (t : SpectralCircle)) := by
    rw [actualFullPeriodTwoSourceIntervalAssembly_apply]
    exact scalarParityRestrictValue_ae (p.val : ℤ)
      (actualScalarParityProjectionLinearEquiv (g b) p)
  have hf : (actualFullPeriodTwoSourceIntervalAssembly f p (!b) : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun t => (actualScalarParityProjectionLinearEquiv (f (!b)) p : SpectralScalarL2)
        (t : SpectralCircle)) := by
    rw [actualFullPeriodTwoSourceIntervalAssembly_apply]
    exact scalarParityRestrictValue_ae (p.val : ℤ)
      (actualScalarParityProjectionLinearEquiv (f (!b)) p)
  have hφ : (actualPhysicalL2SourcePotential (φ b) : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun t => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) (t : SpectralCircle)) :=
    scalarParityRestrictValue_ae 0
      ⟨NlsGge.Analysis.naturalPhysicalCoverL2 (φ b),
        NlsGge.Analysis.naturalPhysicalCoverL2_mem_even (φ b)⟩
  filter_upwards [hpull, hg, hf, hφ] with t hprod hgt hft hφt
  rw [hgt, hft, hφt]
  exact hprod

private lemma stage13T_source_domain_potential_product
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (p : Fin 2)
    (x : NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (p.val : ℤ))
    (b : Bool) :
    (actualSourcePotentialOnRecoveredWeightedDomainAfterAE (p.val : ℤ)
      (φ true) (φ false) x b : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun t => actualPhysicalL2SourcePotential (φ b) t * x.val (!b) t) := by
  let F := actualSourceWeightedDomainLInfRepresentativeMap (p.val : ℤ)
    (recoveredActualSourceWeightedDomainSequenceMapAfterAE (p.val : ℤ) x)
  have hrepr (c : Bool) := actualSourceWeightedDomainRepresentative_matches_source_ae
    (p.val : ℤ) x c
  have hmap := actualSourcePotentialOnRecoveredWeightedDomain_apply
    (p.val : ℤ) (φ true) (φ false) x
  cases b
  · change (actualSourcePotentialOnRecoveredWeightedDomainAfterAE (p.val : ℤ)
      (φ true) (φ false) x false : ℝ → ℂ) =ᵐ[_]
      (fun t => actualPhysicalL2SourcePotential (φ false) t * x.val true t)
    rw [hmap, actualL2PotentialParityPairSourceOperator_apply_false]
    have hmul := actualSourceL2PotentialTimesLInf_ae (φ false) (F true)
    filter_upwards [hmul, hrepr true] with t hmult hrep
    change actualSourceL2PotentialTimesLInf (φ false) (F true) t = _
    rw [hmult, hrep]
  · change (actualSourcePotentialOnRecoveredWeightedDomainAfterAE (p.val : ℤ)
      (φ true) (φ false) x true : ℝ → ℂ) =ᵐ[_]
      (fun t => actualPhysicalL2SourcePotential (φ true) t * x.val false t)
    rw [hmap, actualL2PotentialParityPairSourceOperator_apply_true]
    have hmul := actualSourceL2PotentialTimesLInf_ae (φ true) (F false)
    filter_upwards [hmul, hrepr false] with t hmult hrep
    change actualSourceL2PotentialTimesLInf (φ true) (F false) t = _
    rw [hmult, hrep]

private lemma stage13T_actual_potential_source_block
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (f g : KSTPairL2)
    (hproduct : ∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x))
    (hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain)
    (p : Fin 2) :
    actualFullPeriodTwoSourceIntervalAssembly g p =
      actualSourcePotentialOnRecoveredWeightedDomainAfterAE (p.val : ℤ) (φ true) (φ false)
        ⟨actualFullPeriodTwoSourceIntervalAssembly f p, hf p⟩ := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  exact (stage13T_actual_source_interval_product φ f g hproduct p b).trans
    (stage13T_source_domain_potential_product φ p
      ⟨actualFullPeriodTwoSourceIntervalAssembly f p, hf p⟩ b).symm

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED. Actual forward full operator-action transport.
   Under the SAME unswapped assembly, KST L(phi) corresponds to the NEGATIVE
   existing block D+V(-phi). This is an earned identity, not a source relabel.
   It does not assert H1_loc/endpoint extension or a source eigenvalue iff. -/

private lemma stage13U_negative_actual_product
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (f g : KSTPairL2)
    (hproduct : ∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x)) :
    ∀ b : Bool, ((-g) b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 ((-φ) b) x * f (!b) x) := by
  intro b
  have hcover : NlsGge.Analysis.naturalPhysicalCoverL2 ((-φ) b) =
      -NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) :=
    NlsGge.Analysis.naturalPhysicalCoverL2.map_neg (φ b)
  rw [hcover]
  change ((-g b : SpectralScalarL2) : SpectralCircle → ℂ) =ᵐ[spectralHaar]
    (fun x => (-NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) : SpectralScalarL2) x * f (!b) x)
  filter_upwards [hproduct b, Lp.coeFn_neg (g b),
    Lp.coeFn_neg (NlsGge.Analysis.naturalPhysicalCoverL2 (φ b))]
      with x hprod hneg_g hneg_φ
  rw [hneg_g, hneg_φ]
  change -(g b x) = -(NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x) * f (!b) x
  rw [hprod]
  ring

private lemma stage13U_forward_perturbed_source_block_action
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (f g y : KSTPairL2)
    (hgraph : HasKSTFreeDiracGraph f (y - g))
    (hproduct : ∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x)) :
    ∃ hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain,
      ∀ p : Fin 2,
        actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) (-(φ true)) (-(φ false))
          ⟨actualFullPeriodTwoSourceIntervalAssembly f p, hf p⟩ =
          -actualFullPeriodTwoSourceIntervalAssembly y p := by
  obtain ⟨hf, hfree⟩ :=
    stage13Q_graph_to_actual_source_block_domain_and_negative_free_action hgraph
  refine ⟨hf, ?_⟩
  intro p
  let x : NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (p.val : ℤ) :=
    ⟨actualFullPeriodTwoSourceIntervalAssembly f p, hf p⟩
  let D : SourcePairL2 := actualSourceFreeDiracMapAfterAE (p.val : ℤ) x
  let V : SourcePairL2 := actualSourcePotentialOnRecoveredWeightedDomainAfterAE
    (p.val : ℤ) (-(φ true)) (-(φ false)) x
  let F : SourcePairL2 := actualFullPeriodTwoSourceIntervalAssembly y p
  let G : SourcePairL2 := actualFullPeriodTwoSourceIntervalAssembly g p
  have hD : F - G = -D := by
    have h := hfree p (hf p)
    change actualFullPeriodTwoSourceIntervalAssembly (y - g) p = -D at h
    simpa only [map_sub, PiLp.sub_apply, F, G] using h
  have hV : V = -G := by
    have h := stage13T_actual_potential_source_block (-φ) f (-g)
      (stage13U_negative_actual_product φ f g hproduct) hf p
    have hneg : actualFullPeriodTwoSourceIntervalAssembly (-g) p = -G := by
      have h' := congrArg (fun a : ActualFullPeriodTwoSourcePair => a p)
        (actualFullPeriodTwoSourceIntervalAssembly.map_neg g)
      exact h'
    change actualFullPeriodTwoSourceIntervalAssembly (-g) p = V at h
    rw [hneg] at h
    exact h.symm
  change D + V = -F
  rw [hV]
  have hD' : D = -(F - G) := by rw [hD, neg_neg]
  rw [hD']
  abel

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED private domain bridge, using only locally re-earned
   A/B/C and public source operators. Every actual weak free-graph vector
   has a continuous representative, so its rough L2-potential products are
   genuinely L2. The finite zero mode is retained through P0, not divided out.
   This earns the domain product witness instead of adding an H1 potential
   or pretending an abstract multiplier exists. -/

private lemma stage13J_weakGraph_continuous_representative
    {f y : KSTPairL2} (hgraph : HasKSTFreeDiracGraph f y) (b : Bool) :
    ∃ G : C(SpectralCircle, ℂ),
      (f b : SpectralCircle → ℂ) =ᵐ[spectralHaar] G := by
  have hz : (0 : ℂ) ∈ spectralStrip (0 : ℤ) := by
    norm_num [spectralStrip] <;> positivity
  have hgraph0 : HasKSTFreeDiracGraph f ((0 : ℂ) • f - (-y)) := by
    simpa only [zero_smul, zero_sub, neg_neg] using hgraph
  have hM : complementaryMultiplier 0 0 hz (-y) = spectralQn 0 f :=
    stage13A_complementary_left_inverse 0 0 hz f (-y) hgraph0
  obtain ⟨q, _hqL2, hqAE, _hqsum⟩ :=
    stage13B_complement_continuous_representative 0 0 hz (-y) b
  let c : ℂ := fourierCoeff (f b) 0
  let G : C(SpectralCircle, ℂ) := ContinuousMap.const SpectralCircle c + q
  have hP : spectralPn 0 f b = c • spectralBasis 0 := by
    simpa only [neg_zero, ite_self] using stage13A_Pn_component 0 f b
  have hbasis : (spectralBasis 0 : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fourier 0) := by
    simpa only [spectralBasis, SpectralCircle, SpectralScalarL2, spectralHaar] using!
      (coeFn_fourierLp 2 (0 : ℤ))
  have hP_AE : (spectralPn 0 f b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun _ => c) := by
    rw [hP]
    filter_upwards [Lp.coeFn_smul c (spectralBasis 0), hbasis] with x hsmul hb
    rw [hsmul]
    change c * spectralBasis 0 x = c
    rw [hb]
    simp only [fourier_zero, mul_one]
  have hdecomp : f b = spectralPn 0 f b + complementaryMultiplier 0 0 hz (-y) b := by
    rw [hM]
    change f b = spectralPn 0 f b + (f b - spectralPn 0 f b)
    abel
  refine ⟨G, ?_⟩
  rw [hdecomp]
  filter_upwards [Lp.coeFn_add (spectralPn 0 f b)
    (complementaryMultiplier 0 0 hz (-y) b), hP_AE, hqAE] with x hadd hp hq
  rw [hadd]
  change spectralPn 0 f b x + complementaryMultiplier 0 0 hz (-y) b x = G x
  rw [hp, hq]
  rfl

private lemma stage13J_weakGraph_potential_product_memLp
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp)
    {f y : KSTPairL2} (hgraph : HasKSTFreeDiracGraph f y) (b : Bool) :
    MemLp (fun x : SpectralCircle =>
      NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x) 2 spectralHaar := by
  obtain ⟨G, hG⟩ := stage13J_weakGraph_continuous_representative hgraph (!b)
  have hmem := stage13C_product_memLp
    (NlsGge.Analysis.naturalPhysicalCoverL2 (φ b)) G
  have hae : (fun x : SpectralCircle =>
      NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * G x) =ᵐ[spectralHaar]
      (fun x : SpectralCircle =>
        NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x) := by
    filter_upwards [hG] with x hg
    rw [hg]
  exact (memLp_congr_ae hae).mp hmem

private lemma stage13J_weakGraph_actual_potential_product
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp)
    {f y : KSTPairL2} (hgraph : HasKSTFreeDiracGraph f y) :
    ∃ g : KSTPairL2, ∀ b : Bool,
      (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x) := by
  have hmem (b : Bool) := stage13J_weakGraph_potential_product_memLp φ hgraph b
  let g : KSTPairL2 := WithLp.toLp 2 (fun b =>
    (hmem b).toLp (fun x : SpectralCircle =>
      NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x))
  refine ⟨g, ?_⟩
  intro b
  exact (hmem b).coeFn_toLp



/- INERT / UNCOMPILED. Actual full graph/action equivalence consuming R,
   the SAME-potential transport T/U and locally re-earned actual J witness.
   The H1_loc/endpoint-global interpretation is deliberately not asserted. -/

private lemma stage13W_actual_full_source_block_graph_iff
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (f y : KSTPairL2) :
    (∃ g : KSTPairL2, HasKSTFreeDiracGraph f (y - g) ∧
      ∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x)) ↔
    ∃ hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain,
      ∀ p : Fin 2,
        actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) (-(φ true)) (-(φ false))
          ⟨actualFullPeriodTwoSourceIntervalAssembly f p, hf p⟩ =
          -actualFullPeriodTwoSourceIntervalAssembly y p := by
  constructor
  · rintro ⟨g, hgraph, hproduct⟩
    exact stage13U_forward_perturbed_source_block_action φ f g y hgraph hproduct
  · rintro ⟨hf, hblock⟩
    obtain ⟨y₀, hfree⟩ := stage13R_actual_source_block_domain_to_weak_graph f hf
    obtain ⟨g, hproduct⟩ := stage13J_weakGraph_actual_potential_product φ hfree
    have htotal_graph : HasKSTFreeDiracGraph f ((y₀ + g) - g) := by
      simpa only [add_sub_cancel_right] using hfree
    obtain ⟨hf', htotal⟩ := stage13U_forward_perturbed_source_block_action
      φ f g (y₀ + g) htotal_graph hproduct
    have heq : y₀ + g = y := by
      apply actualFullPeriodTwoSourceIntervalAssembly.injective
      apply PiLp.ext
      intro p
      have hneg : -actualFullPeriodTwoSourceIntervalAssembly (y₀ + g) p =
          -actualFullPeriodTwoSourceIntervalAssembly y p :=
        (htotal p).symm.trans (hblock p)
      exact neg_injective hneg
    have hout : y₀ = y - g := by rw [← heq]; abel
    rw [hout] at hfree
    exact ⟨g, hfree, hproduct⟩

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED. Earned interval H1 witnesses from the actual KST
   graph through Q's actual source-domain membership. This is AC + L2
   derivative + twisted trace on [0,1], not the remaining global H1_loc
   continuation/equivalence theorem. -/

private lemma stage13V_actual_graph_interval_ac_derivative_trace
    {f y : KSTPairL2} (hgraph : HasKSTFreeDiracGraph f y)
    (p : Fin 2) (b : Bool) :
    ∃ (F : ℝ → ℂ) (D : SourceIntervalL2),
      AbsolutelyContinuousOnInterval F 0 1 ∧
      (∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt F (D t) t) ∧
      F 1 = spectralSign (p.val : ℤ) * F 0 ∧
      F =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
        (actualFullPeriodTwoSourceIntervalAssembly f p b : ℝ → ℂ) := by
  letI : IsProbabilityMeasure spectralHaar := by
    unfold spectralHaar
    infer_instance
  have hf := (stage13Q_graph_to_actual_source_block_domain_and_negative_free_action hgraph).1
  let x : SectorSquare (p.val : ℤ) :=
    sourcePairRepr (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly f p)
  have hx : x ∈ freeWeightedDomainPointwise (p.val : ℤ) := hf p
  let G : C(SpectralCircle, ℂ) := freeDomainContinuousComponent (p.val : ℤ) x b
  let D : SourceIntervalL2 := sourceFreeCoordinateDerivative (p.val : ℤ) x hx b
  have hcoord : sourceCoordinateComponent (p.val : ℤ) x b =
      actualFullPeriodTwoSourceIntervalAssembly f p b := by
    change scalarParityRestrict (p.val : ℤ)
      ((parityPairRepr (p.val : ℤ)).symm
        ((parityPairRepr (p.val : ℤ))
          ((parityPairIntervalEquiv (p.val : ℤ)).symm
            (actualFullPeriodTwoSourceIntervalAssembly f p))) b) = _
    rw [(parityPairRepr (p.val : ℤ)).symm_apply_apply]
    change scalarParityIntervalEquiv (p.val : ℤ)
      ((scalarParityIntervalEquiv (p.val : ℤ)).symm
        (actualFullPeriodTwoSourceIntervalAssembly f p b)) = _
    exact (scalarParityIntervalEquiv (p.val : ℤ)).apply_symm_apply _
  refine ⟨(fun t => G (t : SpectralCircle)), D, ?_, ?_, ?_, ?_⟩
  · exact absolutelyContinuous_freeDomainContinuousComponent_source (p.val : ℤ) x hx b
  · exact freeDomainContinuousComponent_source_ae_hasDerivAt (p.val : ℤ) x hx b
  · exact (freeDomainContinuousComponent_integral_and_twistedTrace (p.val : ℤ) x hx b).2
  · have hcont := spectral_ae_pullback_first_half
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spectralHaar G)
    have hsource := freeDomainContinuousComponent_toSourceInterval_ae (p.val : ℤ) x hx b
    rw [hcoord] at hsource
    exact hcont.symm.trans hsource

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED generic primitive steps for the remaining global
   extension. Their actual interval-integrability and zero-mean hypotheses
   must be EARNED from the signed L2 derivative extension, not added to a
   final source theorem. No global H1_loc completion is claimed. -/

private lemma stage13X_primitive_periodic_of_zero_mean
    (g : ℝ → ℂ) (c : ℂ) (hg : Function.Periodic g (2 : ℝ))
    (hint : ∀ a b : ℝ, IntervalIntegrable g volume a b)
    (hmean : (∫ t in (0 : ℝ)..2, g t) = 0) :
    Function.Periodic (fun t => c + ∫ s in (0 : ℝ)..t, g s) (2 : ℝ) := by
  intro t
  change c + (∫ s in (0 : ℝ)..t + 2, g s) = c + (∫ s in (0 : ℝ)..t, g s)
  rw [hg.intervalIntegral_add_eq_add 0 t hint]
  simp only [zero_add, hmean, add_zero]

private lemma stage13X_genuine_primitive_ac_on_every_interval
    (g : ℝ → ℂ) (c : ℂ)
    (hint : ∀ a b : ℝ, IntervalIntegrable g volume a b) :
    ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun t => c + ∫ s in (0 : ℝ)..t, g s) a b := by
  intro a b
  have hprimitive := NlsGge.SpectralFoundations.complex_intervalIntegral_primitive_absolutelyContinuousV2
    (hint a b) (c := a) Set.left_mem_uIcc
  have hconstant : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => c + ∫ s in (0 : ℝ)..a, g s) a b := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    refine ⟨1, by norm_num, ?_⟩
    intro E hE hlen
    simpa using hε
  apply (hconstant.add hprimitive).congr
  intro t ht
  change (c + ∫ s in (0 : ℝ)..a, g s) + (∫ s in a..t, g s) =
    c + ∫ s in (0 : ℝ)..t, g s
  rw [add_assoc, intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a t)]

/- INERT / UNCOMPILED actual signed continuation of an interval L2
   derivative class. Local integrability and local L2 are EARNED before
   primitive identities. This does not yet identify the primitive with the
   source state or establish the remaining global H1_loc equivalence. -/

private lemma stage13Y_actual_signed_derivative_extension
    (n : ℤ) (D : SourceIntervalL2) :
    let G : ℝ → ℂ := fun t => sourceSignedCircleValue n D (t : SpectralCircle)
    (∀ t : ℝ, G (t + 1) = spectralSign n * G t) ∧
    Function.Periodic G (2 : ℝ) ∧
    (G =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (D : ℝ → ℂ)) ∧
    ∀ a b : ℝ, IntervalIntegrable G volume a b ∧
      MemLp G 2 (volume.restrict (Set.uIcc a b)) := by
  dsimp only
  let G : ℝ → ℂ := fun t => sourceSignedCircleValue n D (t : SpectralCircle)
  have hshift (t : ℝ) : G (t + 1) = spectralSign n * G t := by
    change sourceSignedCircleValue n D ((t + 1 : ℝ) : SpectralCircle) = _
    rw [AddCircle.coe_add, sourceSignedCircle_halfShift]
  have hperiod : Function.Periodic G (2 : ℝ) := by
    intro t
    change sourceSignedCircleValue n D ((t + 2 : ℝ) : SpectralCircle) = _
    rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hwhole : G =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 2)] sourceSignedHalfValue n D := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with t ht
    change sourceSignedCircleValue n D (t : SpectralCircle) = _
    have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 2) := by simpa only [zero_add] using ht
    rw [sourceSignedCircleValue, AddCircle.liftIoc_coe_apply ht']
  have hmem : MemLp G 2 (volume.restrict (Set.Ioc (0 : ℝ) 2)) :=
    (memLp_congr_ae hwhole).2 (sourceSignedHalf_memLp n D)
  have hGint : IntervalIntegrable G volume 0 2 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 2)).2
    exact hmem.integrable (by norm_num)
  have hsqint : IntervalIntegrable (fun t => ‖G t‖ ^ 2) volume 0 2 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 2)).2
    exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  have hsqperiod : Function.Periodic (fun t => ‖G t‖ ^ 2) (2 : ℝ) := by
    intro t
    change ‖G (t + 2)‖ ^ 2 = ‖G t‖ ^ 2
    rw [hperiod t]
  refine ⟨hshift, hperiod, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with t ht
    change sourceSignedCircleValue n D (t : SpectralCircle) = D t
    have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 2) := ⟨ht.1, ht.2.trans (by norm_num)⟩
    rw [sourceSignedCircleValue, AddCircle.liftIoc_coe_apply ht']
    simp only [sourceSignedHalfValue, ite_eq_left ht.2]
  · intro a b
    have hint := hperiod.intervalIntegrable₀ (by norm_num : (2 : ℝ) ≠ 0) hGint a b
    have hnorm := hsqperiod.intervalIntegrable₀ (by norm_num : (2 : ℝ) ≠ 0) hsqint a b
    have hlocal := (intervalIntegrable_iff').1 hint
    have hnormlocal := (intervalIntegrable_iff').1 hnorm
    exact ⟨hint, (memLp_two_iff_integrable_sq_norm hlocal.aestronglyMeasurable).2 hnormlocal⟩

/- INERT / UNCOMPILED. Literal global signed H1 witness from genuine
   interval AC, an ACTUAL L2 derivative class and its AE derivative/trace.
   These inputs are earned on the weak domain by V; they may not be added
   as new final source premises. The converse global-source theorem is
   separate. No global H1_loc acceptance is claimed before native/review. -/

private lemma stage13Z_global_signed_H1_extension
    (n : ℤ) (F : ℝ → ℂ) (D : SourceIntervalL2)
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hder : ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt F (D t) t)
    (htrace : F 1 = spectralSign n * F 0) :
    ∃ H G : ℝ → ℂ,
      (∀ a b : ℝ, MemLp H 2 (volume.restrict (Set.uIcc a b)) ∧
        MemLp G 2 (volume.restrict (Set.uIcc a b)) ∧
        AbsolutelyContinuousOnInterval H a b) ∧
      (∀ᵐ t ∂volume, HasDerivAt H (G t) t) ∧
      (∀ t : ℝ, H (t + 1) = spectralSign n * H t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, H t = F t) ∧
      (G =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (D : ℝ → ℂ)) := by
  let G : ℝ → ℂ := fun t => sourceSignedCircleValue n D (t : SpectralCircle)
  obtain ⟨hshift, _hperiod, hsame, hlocal⟩ := stage13Y_actual_signed_derivative_extension n D
  have hint (a b : ℝ) : IntervalIntegrable G volume a b := (hlocal a b).1
  have hDint : IntervalIntegrable (fun t => D t) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
    exact (Lp.memLp D).integrable (by norm_num)
  have hprimitive :=
    NlsGge.SpectralFoundations.complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
      hF hDint hder
  have h01 : (∫ t in (0 : ℝ)..1, G t) = ∫ t in (0 : ℝ)..1, D t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_congr_ae hsame
  have hmean1 : (∫ t in (0 : ℝ)..1, G t) = spectralSign n * F 0 - F 0 := by
    rw [h01]
    have hprim1 := hprimitive 1 Set.right_mem_uIcc
    linear_combination htrace - hprim1
  let H : ℝ → ℂ := fun t => F 0 + ∫ s in (0 : ℝ)..t, G s
  have hHshift (t : ℝ) : H (t + 1) = spectralSign n * H t := by
    have htranslated : (∫ s in (1 : ℝ)..t + 1, G s) =
        spectralSign n * ∫ s in (0 : ℝ)..t, G s := by
      calc
        (∫ s in (1 : ℝ)..t + 1, G s) = ∫ s in (0 : ℝ)..t, G (s + 1) := by
          simpa only [zero_add] using
            (intervalIntegral.integral_comp_add_right (f := G) (a := (0 : ℝ)) (b := t) 1).symm
        _ = ∫ s in (0 : ℝ)..t, spectralSign n * G s := by
          congr 1
          funext s
          exact hshift s
        _ = spectralSign n * ∫ s in (0 : ℝ)..t, G s :=
          intervalIntegral.integral_const_mul (spectralSign n) G
    change F 0 + (∫ s in (0 : ℝ)..t + 1, G s) =
      spectralSign n * (F 0 + ∫ s in (0 : ℝ)..t, G s)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 (t + 1)),
      hmean1, htranslated]
    ring
  have hagree (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : H t = F t := by
    have hsubset : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc (0 : ℝ) 1 :=
      fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
    have hsame_t : G =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) t)] (D : ℝ → ℂ) :=
      hsame.filter_mono (ae_mono (Measure.restrict_mono_set volume hsubset))
    have hint_t : (∫ s in (0 : ℝ)..t, G s) = ∫ s in (0 : ℝ)..t, D s := by
      rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
      exact integral_congr_ae hsame_t
    change F 0 + (∫ s in (0 : ℝ)..t, G s) = F t
    rw [hint_t]
    exact (hprimitive t (by simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)).symm
  have hAC (a b : ℝ) : AbsolutelyContinuousOnInterval H a b :=
    stage13X_genuine_primitive_ac_on_every_interval G (F 0) hint a b
  have hlocally : LocallyIntegrable G volume := by
    intro t
    refine ⟨Set.uIcc (t - 1) (t + 1), ?_, (intervalIntegrable_iff').1 (hint (t - 1) (t + 1))⟩
    rw [Set.uIcc_of_le (by linarith : t - 1 ≤ t + 1)]
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hglobal_der : ∀ᵐ t ∂volume, HasDerivAt H (G t) t := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hlocally] with t ht
    simpa only [H] using (ht 0).const_add (F 0)
  refine ⟨H, G, ?_, hglobal_der, hHshift, hagree, hsame⟩
  intro a b
  obtain ⟨C, hC⟩ := (hAC a b).exists_bound
  have hmemH : MemLp H 2 (volume.restrict (Set.uIcc a b)) := by
    letI : IsFiniteMeasure (volume.restrict (Set.uIcc a b)) := by
      change IsFiniteMeasure (volume.restrict (Set.Icc (min a b) (max a b)))
      infer_instance
    apply MemLp.of_bound ((hAC a b).continuousOn.aestronglyMeasurable measurableSet_uIcc) C
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_uIcc] with t ht
    exact hC t ht
  exact ⟨hmemH, (hlocal a b).2, hAC a b⟩

/- INERT / UNCOMPILED source-domain reverse for actual interval H1 data.
   Global H1 witnesses restrict to these premises; no global or source
   acceptance is inferred before actual review/native. -/

private lemma stage13AA_sourceCoordinate_of_sourceRepr
    (n : ℤ) (X : SourcePairL2) (b : Bool) :
    sourceCoordinateComponent n (sourcePairRepr n X) b = X b := by
  change scalarParityRestrict n
    ((parityPairRepr n).symm ((parityPairRepr n) ((parityPairIntervalEquiv n).symm X)) b) = _
  rw [(parityPairRepr n).symm_apply_apply]
  change scalarParityIntervalEquiv n ((scalarParityIntervalEquiv n).symm (X b)) = X b
  exact (scalarParityIntervalEquiv n).apply_symm_apply _

private lemma stage13AA_source_domain_of_actual_interval_H1_representatives
    (n : ℤ) (X : SourcePairL2) (F G : Bool → ℝ → ℂ)
    (hAC : ∀ b : Bool, AbsolutelyContinuousOnInterval (F b) 0 1)
    (hL2 : ∀ b : Bool, MemLp (G b) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hder : ∀ b : Bool, ∀ᵐ t ∂volume,
      t ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt (F b) (G b t) t)
    (hclass : ∀ b : Bool, (X b : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)] F b)
    (htrace : ∀ b : Bool, F b 1 = spectralSign n * F b 0) :
    X ∈ NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain n := by
  have hmem (b : Bool) : MemLp (G b) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (hL2 b).mono_measure (Measure.restrict_mono_set volume Set.Ioc_subset_Icc_self)
  let D : Bool → SourceIntervalL2 := fun b => (hmem b).toLp (G b)
  have hD (b : Bool) : (D b : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)] G b := (hmem b).coeFn_toLp
  have hGint (b : Bool) : IntervalIntegrable (G b) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
    exact (hmem b).integrable (by norm_num)
  have hcoord (b : Bool) :
      (sourceCoordinateComponent n (sourcePairRepr n X) b : ℝ → ℂ) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)] F b := by
    rw [stage13AA_sourceCoordinate_of_sourceRepr]
    exact hclass b
  have hx := sourceFreeDomain_of_actualAC_components n (sourcePairRepr n X)
    D F G hAC hGint hder hcoord hD htrace
  change sourcePairRepr n X ∈ freeWeightedDomainPointwise n
  exact hx

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED actual source-domain equivalence, consuming actual
   private native R/V/XYZ/AA. The right side states genuine compact H1
   representatives and the literal source endpoint condition. It assumes no
   weighted domain, global periodicity, product field, or H1 potential. -/

private lemma stage13AB_actual_source_domain_iff_global_compact_H1
    (f : KSTPairL2) :
    f ∈ actualFullPeriodTwoSourceDoubledCircleDomain ↔
    ∃ F G : Fin 2 → Bool → ℝ → ℂ,
      (∀ (p : Fin 2) (b : Bool) (a c : ℝ),
        MemLp (F p b) 2 (volume.restrict (Set.uIcc a c)) ∧
        MemLp (G p b) 2 (volume.restrict (Set.uIcc a c)) ∧
        AbsolutelyContinuousOnInterval (F p b) a c) ∧
      (∀ (p : Fin 2) (b : Bool), ∀ᵐ t ∂volume,
        HasDerivAt (F p b) (G p b t) t) ∧
      (∀ (p : Fin 2) (b : Bool), F p b 1 = spectralSign (p.val : ℤ) * F p b 0) ∧
      (∀ (p : Fin 2) (b : Bool),
        (actualFullPeriodTwoSourceIntervalAssembly f p b : ℝ → ℂ)
          =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] F p b) := by
  classical
  constructor
  · intro hf
    obtain ⟨y, hgraph⟩ := stage13R_actual_source_block_domain_to_weak_graph f hf
    have hw (p : Fin 2) (b : Bool) :
        ∃ H G : ℝ → ℂ,
          (∀ a c : ℝ, MemLp H 2 (volume.restrict (Set.uIcc a c)) ∧
            MemLp G 2 (volume.restrict (Set.uIcc a c)) ∧
            AbsolutelyContinuousOnInterval H a c) ∧
          (∀ᵐ t ∂volume, HasDerivAt H (G t) t) ∧
          H 1 = spectralSign (p.val : ℤ) * H 0 ∧
          ((actualFullPeriodTwoSourceIntervalAssembly f p b : ℝ → ℂ)
            =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] H) := by
      obtain ⟨F, D, hF, hder, htrace, hclass⟩ :=
        stage13V_actual_graph_interval_ac_derivative_trace hgraph p b
      obtain ⟨H, G, hlocal, hglobal, hshift, hagree, _hGclass⟩ :=
        stage13Z_global_signed_H1_extension (p.val : ℤ) F D hF hder htrace
      have hHclass : H =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
          (actualFullPeriodTwoSourceIntervalAssembly f p b : ℝ → ℂ) := by
        filter_upwards [hclass,
          ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with t ht hmem
        exact (hagree t ⟨le_of_lt hmem.1, hmem.2⟩).trans ht
      refine ⟨H, G, hlocal, hglobal, ?_, hHclass.symm⟩
      simpa only [zero_add] using hshift 0
    choose F G hlocal hder htrace hclass using hw
    exact ⟨F, G, hlocal, hder, htrace, hclass⟩
  · rintro ⟨F, G, hlocal, hder, htrace, hclass⟩
    intro p
    apply stage13AA_source_domain_of_actual_interval_H1_representatives
      (p.val : ℤ) (actualFullPeriodTwoSourceIntervalAssembly f p) (F p) (G p)
    · intro b
      exact (hlocal p b 0 1).2.2
    · intro b
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (hlocal p b 0 1).2.1
    · intro b
      filter_upwards [hder p b] with t ht
      intro _ht
      exact ht
    · exact hclass p
    · exact htrace p

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED proper-domain action/eigenvector transport.
   The SAME unswapped full assembly identifies KST L(phi) with NEGATIVE
   oldAction(-phi). Thus a KST eigenvalue z corresponds to oldAction(-phi)
   eigenvalue -z. Actual domain has been independently characterized by AB;
   no H1loc/product/operator assumption is introduced here. -/

lemma stage13AC_actual_proper_operator_graph_iff
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (f y : KSTPairL2) :
    (∃ g : KSTPairL2, HasKSTFreeDiracGraph f (y - g) ∧
      ∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x)) ↔
    ∃ hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain,
      actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
        ⟨f, hf⟩ = -y := by
  have hneg : actualFullPeriodTwoSourceIntervalAssembly (-y) =
      -actualFullPeriodTwoSourceIntervalAssembly y :=
    map_neg actualFullPeriodTwoSourceIntervalAssembly y
  constructor
  · intro hgraph
    obtain ⟨hf, hblock⟩ := (stage13W_actual_full_source_block_graph_iff φ f y).1 hgraph
    refine ⟨hf, ?_⟩
    apply actualFullPeriodTwoSourceIntervalAssembly.injective
    calc
      actualFullPeriodTwoSourceIntervalAssembly
          (actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
            ⟨f, hf⟩) =
          actualFullPeriodTwoSourceBlockAction (-(φ true)) (-(φ false))
            ⟨actualFullPeriodTwoSourceIntervalAssembly f, hf⟩ := by
              exact actualFullPeriodTwoDoubledCirclePerturbedDiracAction_repr _ _ _
      _ = -actualFullPeriodTwoSourceIntervalAssembly y := by
        apply PiLp.ext
        intro p
        change actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) (-(φ true)) (-(φ false))
          ⟨actualFullPeriodTwoSourceIntervalAssembly f p, hf p⟩ =
            -actualFullPeriodTwoSourceIntervalAssembly y p
        exact hblock p
      _ = actualFullPeriodTwoSourceIntervalAssembly (-y) := hneg.symm
  · rintro ⟨hf, haction⟩
    apply (stage13W_actual_full_source_block_graph_iff φ f y).2
    refine ⟨hf, ?_⟩
    have hassembly :
        actualFullPeriodTwoSourceBlockAction (-(φ true)) (-(φ false))
          ⟨actualFullPeriodTwoSourceIntervalAssembly f, hf⟩ =
            -actualFullPeriodTwoSourceIntervalAssembly y := by
      calc
        _ = actualFullPeriodTwoSourceIntervalAssembly
            (actualFullPeriodTwoDoubledCirclePerturbedDiracAction
              (-(φ true)) (-(φ false)) ⟨f, hf⟩) := by
                symm
                exact actualFullPeriodTwoDoubledCirclePerturbedDiracAction_repr _ _ _
        _ = actualFullPeriodTwoSourceIntervalAssembly (-y) :=
          congrArg actualFullPeriodTwoSourceIntervalAssembly haction
        _ = -actualFullPeriodTwoSourceIntervalAssembly y := hneg
    intro p
    have hp := congrArg (fun a : ActualFullPeriodTwoSourcePair => a p) hassembly
    change actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) (-(φ true)) (-(φ false))
      ⟨actualFullPeriodTwoSourceIntervalAssembly f p, hf p⟩ =
        -actualFullPeriodTwoSourceIntervalAssembly y p at hp
    exact hp

private lemma stage13AC_actual_source_operator_eigenvector_iff_graph
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (z : ℂ) :
    (∃ (f : KSTPairL2), f ≠ 0 ∧
      ∃ hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain,
        actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
          ⟨f, hf⟩ = (-z) • f) ↔
    ∃ f g : KSTPairL2, f ≠ 0 ∧
      HasKSTFreeDiracGraph f (z • f - g) ∧
      ∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x * f (!b) x) := by
  constructor
  · rintro ⟨f, hfne, hf, haction⟩
    have hneg : actualFullPeriodTwoDoubledCirclePerturbedDiracAction
        (-(φ true)) (-(φ false)) ⟨f, hf⟩ = -(z • f) := by
      simpa only [neg_smul] using haction
    obtain ⟨g, hgraph, hproduct⟩ :=
      (stage13AC_actual_proper_operator_graph_iff φ f (z • f)).2 ⟨hf, hneg⟩
    exact ⟨f, g, hfne, hgraph, hproduct⟩
  · rintro ⟨f, g, hfne, hgraph, hproduct⟩
    obtain ⟨hf, haction⟩ :=
      (stage13AC_actual_proper_operator_graph_iff φ f (z • f)).1 ⟨g, hgraph, hproduct⟩
    refine ⟨f, hfne, hf, ?_⟩
    simpa only [neg_smul] using haction

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED private source-operator/raw-(26a)-kernel criterion.
   SAME epsilon/N0 are selected by M before psi,n,z. The old action is at
   -psi and eigenvalue -z, exactly as earned by AC for original KST signs.
   No public Sn definition, stronger input, H1 potential, or abstract target
   operator is introduced. AB independently characterizes this SAME domain. -/

private lemma stage13AD_same_uniform_source_operator_raw_kernel_criterion
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ ψ : NlsGge.Atomic.KST002.PhysicalPairLp, ‖ψ - φ‖ < ε →
        ∀ n : ℤ, N₀ ≤ n.natAbs →
          ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
            ((∃ f : KSTPairL2, f ≠ 0 ∧
                ∃ hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain,
                  actualFullPeriodTwoDoubledCirclePerturbedDiracAction
                    (-(ψ true)) (-(ψ false)) ⟨f, hf⟩ = (-z) • f) ↔
              ∃ u : KSTPairL2, u ≠ 0 ∧ spectralPn n u = u ∧
                (z - (n : ℂ) * (Real.pi : ℂ)) • u =
                  spectralPn n
                    (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz)
                      (NlsGge.Atomic.KST012.potentialOnPn ψ n u))) ∧
            ∀ (f₁ f₂ : KSTPairL2)
              (hf₁ : f₁ ∈ actualFullPeriodTwoSourceDoubledCircleDomain)
              (hf₂ : f₂ ∈ actualFullPeriodTwoSourceDoubledCircleDomain),
              actualFullPeriodTwoDoubledCirclePerturbedDiracAction
                (-(ψ true)) (-(ψ false)) ⟨f₁, hf₁⟩ = (-z) • f₁ →
              actualFullPeriodTwoDoubledCirclePerturbedDiracAction
                (-(ψ true)) (-(ψ false)) ⟨f₂, hf₂⟩ = (-z) • f₂ →
              spectralPn n f₁ = spectralPn n f₂ → f₁ = f₂ := by
  obtain ⟨ε, hε, N₀, hN₀, hlocal⟩ := stage13M_actual_uniform_raw_kernel_equivalence φ
  refine ⟨ε, hε, N₀, hN₀, ?_⟩
  intro ψ hψ n hn z hz
  obtain ⟨hraw, hinj⟩ := hlocal ψ hψ n hn z hz
  refine ⟨(stage13AC_actual_source_operator_eigenvector_iff_graph ψ z).trans hraw, ?_⟩
  intro f₁ f₂ hf₁ hf₂ he₁ he₂ heq
  have he₁' : actualFullPeriodTwoDoubledCirclePerturbedDiracAction
      (-(ψ true)) (-(ψ false)) ⟨f₁, hf₁⟩ = -(z • f₁) := by
    simpa only [neg_smul] using he₁
  have he₂' : actualFullPeriodTwoDoubledCirclePerturbedDiracAction
      (-(ψ true)) (-(ψ false)) ⟨f₂, hf₂⟩ = -(z • f₂) := by
    simpa only [neg_smul] using he₂
  obtain ⟨g₁, hgraph₁, hproduct₁⟩ :=
    (stage13AC_actual_proper_operator_graph_iff ψ f₁ (z • f₁)).2 ⟨hf₁, he₁'⟩
  obtain ⟨g₂, hgraph₂, hproduct₂⟩ :=
    (stage13AC_actual_proper_operator_graph_iff ψ f₂ (z • f₂)).2 ⟨hf₂, he₂'⟩
  exact hinj f₁ g₁ f₂ g₂ hgraph₁ hgraph₂ hproduct₁ hproduct₂ heq

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT EXACT COMMAND PROPOSAL, NOT STAGED OR COMPILED.
   Context: import NlsGge.Atomic.KST.KST012; autoImplicit false;
   noncomputable section; namespace NlsGge.Atomic.KST013;
   open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004.
   Definition bodies complete; theorem heads await approved implementation.
   No placeholder proof is asserted or registered. -/

/-- The actual two-dimensional source space P_n H, with both channels. -/
def resonantSubspace (n : ℤ) : Submodule ℂ KSTPairL2 :=
  LinearMap.range (spectralPn n).toLinearMap

/-- Literal source S_n(z)=A_z-P_n(1-T_n)^{-1}Phi on P_n H. -/
def reducedS
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) : resonantSubspace n →L[ℂ] resonantSubspace n :=
  let raw : KSTPairL2 →L[ℂ] KSTPairL2 :=
    (z - (n : ℂ) * (Real.pi : ℂ)) • ContinuousLinearMap.id ℂ KSTPairL2 -
      (spectralPn n).comp
        ((Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)).comp
          (NlsGge.Atomic.KST012.potentialOnPn φ n))
  raw.restrict (p := resonantSubspace n) (q := resonantSubspace n) (by
    intro u hu
    change (z - (n : ℂ) * (Real.pi : ℂ)) • u -
        spectralPn n
          (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)
            (NlsGge.Atomic.KST012.potentialOnPn φ n u)) ∈
      LinearMap.range (spectralPn n).toLinearMap
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hu) ⟨_, rfl⟩)

/-- KST's original-sign Dirac action on the actual source domain. The
negative old action at negative potential is the proved unswapped transport. -/
def dirac (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    KSTPairL2 →ₗ.[ℂ] KSTPairL2 :=
  ⟨actualFullPeriodTwoSourceDoubledCircleDomain,
    -actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))⟩

/-- The range has exactly both source resonant directions, not a half-pair. -/
theorem resonantSubspace_finrank (n : ℤ) :
    Module.finrank ℂ (resonantSubspace n) = 2 := by
  change Module.finrank ℂ (LinearMap.range (spectralPn n).toLinearMap) = 2
  rw [spectralPn_range]
  simpa only [Fintype.card_bool] using
    (finrank_span_eq_card (kstPnFrame_orthonormal n).linearIndependent)

/-- Actual proper domain equals SAME interval classes admitting global
compact H1 representatives with the source endpoint signs. -/
theorem dirac_domain_iff_global_compact_H1
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (f : KSTPairL2) :
    f ∈ (dirac φ).domain ↔
    ∃ F G : Fin 2 → Bool → ℝ → ℂ,
      (∀ (p : Fin 2) (b : Bool) (a c : ℝ),
        MemLp (F p b) 2 (volume.restrict (Set.uIcc a c)) ∧
        MemLp (G p b) 2 (volume.restrict (Set.uIcc a c)) ∧
        AbsolutelyContinuousOnInterval (F p b) a c) ∧
      (∀ (p : Fin 2) (b : Bool), ∀ᵐ t ∂volume,
        HasDerivAt (F p b) (G p b t) t) ∧
      (∀ (p : Fin 2) (b : Bool), F p b 1 = spectralSign (p.val : ℤ) * F p b 0) ∧
      (∀ (p : Fin 2) (b : Bool),
        (actualFullPeriodTwoSourceIntervalAssembly f p b : ℝ → ℂ)
          =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] F p b) := by
  exact stage13AB_actual_source_domain_iff_global_compact_H1 f

/-- Packet-literal fixed-potential (26a), both kernel directions and
injectivity of P_n on the actual eigenspace; N0 depends on the fixed phi. -/
theorem dirac_eigen_iff_reduced_kernel
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ n : ℤ, N₀ ≤ n.natAbs →
        ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
          ((∃ f : (dirac φ).domain, (f : KSTPairL2) ≠ 0 ∧
              dirac φ f = z • (f : KSTPairL2)) ↔
            ∃ u : resonantSubspace n, u ≠ 0 ∧ reducedS φ n z hz u = 0) ∧
          ∀ f₁ f₂ : (dirac φ).domain,
            dirac φ f₁ = z • (f₁ : KSTPairL2) →
            dirac φ f₂ = z • (f₂ : KSTPairL2) →
            spectralPn n (f₁ : KSTPairL2) = spectralPn n (f₂ : KSTPairL2) →
            (f₁ : KSTPairL2) = (f₂ : KSTPairL2) := by
  obtain ⟨ε, hε, N₀, hN₀, hlocal⟩ :=
    stage13AD_same_uniform_source_operator_raw_kernel_criterion φ
  refine ⟨N₀, hN₀, ?_⟩
  intro n hn z hz
  have hφ : ‖φ - φ‖ < ε := by
    simpa only [sub_self, norm_zero] using hε
  obtain ⟨hraw, hinj⟩ := hlocal φ hφ n hn z hz
  have haction (f : (dirac φ).domain) :
      dirac φ f = z • (f : KSTPairL2) ↔
      actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
        ⟨(f : KSTPairL2), f.property⟩ = (-z) • (f : KSTPairL2) := by
    have hdirac : dirac φ f =
        -actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
          ⟨(f : KSTPairL2), f.property⟩ := by rfl
    constructor
    · intro he
      have he' :
          -actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
            ⟨(f : KSTPairL2), f.property⟩ = z • (f : KSTPairL2) := hdirac.symm.trans he
      have h := congrArg (fun x : KSTPairL2 => -x) he'
      simpa only [KSTPairL2, ActualTwoChannelSpectralL2, neg_neg, neg_smul] using! h
    · intro he
      have h := congrArg (fun x : ActualTwoChannelSpectralL2 => -x) he
      apply hdirac.trans
      simpa only [KSTPairL2, ActualTwoChannelSpectralL2, neg_smul, neg_neg] using! h
  have heigen :
      (∃ f : (dirac φ).domain, (f : KSTPairL2) ≠ 0 ∧
        dirac φ f = z • (f : KSTPairL2)) ↔
      (∃ f : KSTPairL2, f ≠ 0 ∧
        ∃ hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain,
          actualFullPeriodTwoDoubledCirclePerturbedDiracAction
            (-(φ true)) (-(φ false)) ⟨f, hf⟩ = (-z) • f) := by
    constructor
    · rintro ⟨f, hfne, he⟩
      exact ⟨f, hfne, f.property, (haction f).1 he⟩
    · rintro ⟨f, hfne, hf, he⟩
      exact ⟨⟨f, hf⟩, hfne, (haction ⟨f, hf⟩).2 he⟩
  have hfix (u : resonantSubspace n) : spectralPn n (u : KSTPairL2) = u := by
    obtain ⟨v, hv⟩ := u.property
    change spectralPn n v = (u : KSTPairL2) at hv
    have h := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S v)
      (spectralPn_idempotent n)
    change spectralPn n (spectralPn n v) = spectralPn n v at h
    rw [hv] at h
    exact h
  have hkernel :
      (∃ u : KSTPairL2, u ≠ 0 ∧ spectralPn n u = u ∧
        (z - (n : ℂ) * (Real.pi : ℂ)) • u =
          spectralPn n
            (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)
              (NlsGge.Atomic.KST012.potentialOnPn φ n u))) ↔
      ∃ u : resonantSubspace n, u ≠ 0 ∧ reducedS φ n z hz u = 0 := by
    constructor
    · rintro ⟨u, hune, hu, heq⟩
      let v : resonantSubspace n := ⟨u, ⟨u, hu⟩⟩
      refine ⟨v, ?_, ?_⟩
      · intro hv
        apply hune
        exact congrArg (fun a : resonantSubspace n => (a : KSTPairL2)) hv
      · apply Subtype.ext
        change (z - (n : ℂ) * (Real.pi : ℂ)) • u -
          spectralPn n
            (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)
              (NlsGge.Atomic.KST012.potentialOnPn φ n u)) = 0
        exact sub_eq_zero.mpr heq
    · rintro ⟨u, hune, heq⟩
      refine ⟨u, ?_, hfix u, ?_⟩
      · intro hu
        apply hune
        exact Subtype.ext hu
      · have h := congrArg (fun a : resonantSubspace n => (a : KSTPairL2)) heq
        change (z - (n : ℂ) * (Real.pi : ℂ)) • (u : KSTPairL2) -
          spectralPn n
            (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)
              (NlsGge.Atomic.KST012.potentialOnPn φ n u)) = 0 at h
        exact sub_eq_zero.mp h
  refine ⟨(heigen.trans hraw).trans hkernel, ?_⟩
  intro f₁ f₂ he₁ he₂ hprojection
  exact hinj f₁ f₂ f₁.property f₂.property
    ((haction f₁).1 he₁) ((haction f₂).1 he₂) hprojection

end NlsGge.Atomic.KST013
end

noncomputable section
namespace NlsGge.Atomic.KST013
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/- INERT / UNCOMPILED source-interpretation dependency, no public interface.
   Locally adapts the actual finite-direct-sum template in
   Spectral/ActualFullSourceBlockPointEigenbranchesV3.lean (Apache-2.0).
   That module is NOT imported by the current context; no inherited native
   result is claimed. This relates the existing full proper-domain action
   to one actual periodic/antiperiodic source block, retaining both channels.
   It adds no eigenvector/domain/regularity field as an assumption. -/

private lemma source13_full_actual_operator_eigenvector_iff_parity_branch
    (u₁ u₂ : NlsGge.Pilot.PhysicalL2) (z : ℂ) :
    (∃ f : actualFullPeriodTwoSourceDoubledCircleDomain,
      (f : KSTPairL2) ≠ 0 ∧
      actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂ f = z • (f : KSTPairL2)) ↔
    ∃ p : Fin 2,
      ∃ Y : NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (p.val : ℤ),
        Y.val ≠ 0 ∧
        actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂ Y = z • Y.val := by
  classical
  constructor
  · rintro ⟨f, hfne, heigen⟩
    have hblocks : actualFullPeriodTwoSourceBlockAction u₁ u₂
        ⟨actualFullPeriodTwoSourceIntervalAssembly f, f.property⟩ =
          z • actualFullPeriodTwoSourceIntervalAssembly f := by
      calc
        _ = actualFullPeriodTwoSourceIntervalAssembly
            (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂ f) := by
              symm
              exact actualFullPeriodTwoDoubledCirclePerturbedDiracAction_repr _ _ _
        _ = actualFullPeriodTwoSourceIntervalAssembly (z • (f : KSTPairL2)) :=
          congrArg actualFullPeriodTwoSourceIntervalAssembly heigen
        _ = z • actualFullPeriodTwoSourceIntervalAssembly f :=
          map_smul actualFullPeriodTwoSourceIntervalAssembly z (f : KSTPairL2)
    have hpne : ∃ p : Fin 2, actualFullPeriodTwoSourceIntervalAssembly f p ≠ 0 := by
      by_contra h
      push_neg at h
      apply hfne
      apply actualFullPeriodTwoSourceIntervalAssembly.injective
      calc
        actualFullPeriodTwoSourceIntervalAssembly f = 0 := by
          apply PiLp.ext
          intro p
          exact h p
        _ = actualFullPeriodTwoSourceIntervalAssembly 0 :=
          (map_zero actualFullPeriodTwoSourceIntervalAssembly).symm
    obtain ⟨p, hp⟩ := hpne
    refine ⟨p, ⟨actualFullPeriodTwoSourceIntervalAssembly f p, f.property p⟩, hp, ?_⟩
    have h := congrArg (fun a : ActualFullPeriodTwoSourcePair => a p) hblocks
    exact h
  · rintro ⟨p, Y, hYne, heigen⟩
    let a : ActualFullPeriodTwoSourcePair :=
      WithLp.toLp 2 (fun q : Fin 2 => if q = p then Y.val else 0)
    have ha : a ∈ actualFullPeriodTwoSourceBlockDomain := by
      intro q
      by_cases hq : q = p
      · subst q
        simpa only [a, ↓reduceIte] using Y.property
      · simpa only [a, hq, ↓reduceIte] using
          (NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (q.val : ℤ)).zero_mem
    have haComponent : ∀ q : Fin 2, a q ∈
        NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (q.val : ℤ) := ha
    have hane : a ≠ 0 := by
      intro hzero
      apply hYne
      have h := congrArg (fun v : ActualFullPeriodTwoSourcePair => v p) hzero
      simpa only [a, ↓reduceIte, WithLp.ofLp_zero, Pi.zero_apply] using h
    have haAction : actualFullPeriodTwoSourceBlockAction u₁ u₂ ⟨a, ha⟩ = z • a := by
      apply PiLp.ext
      intro q
      by_cases hq : q = p
      · subst q
        change actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂
          ⟨a p, haComponent p⟩ = z • a p
        have hY : (⟨a p, haComponent p⟩ :
            NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (p.val : ℤ)) = Y := by
          apply Subtype.ext
          simp only [a, ↓reduceIte]
        have hActionEq := congrArg
          (fun X : NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (p.val : ℤ) =>
            actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂ X) hY
        exact hActionEq.trans (by simpa only [a, ↓reduceIte] using heigen)
      · change actualSourcePerturbedDiracPMapAfterAE (q.val : ℤ) u₁ u₂
          ⟨a q, haComponent q⟩ = z • a q
        have hzero : (⟨a q, haComponent q⟩ :
            NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (q.val : ℤ)) = 0 := by
          apply Subtype.ext
          simp only [a, hq, ↓reduceIte, Submodule.coe_zero]
        have hActionEq := congrArg
          (fun X : NlsGge.Schur.TransportBridgeV4.recoveredActualSourceFreeWeightedDomain (q.val : ℤ) =>
            actualSourcePerturbedDiracPMapAfterAE (q.val : ℤ) u₁ u₂ X) hzero
        have hmapZero := LinearPMap.map_zero
          (actualSourcePerturbedDiracPMapAfterAE (q.val : ℤ) u₁ u₂)
        exact hActionEq.trans (hmapZero.trans (by
          simp only [a, hq, ↓reduceIte, smul_zero]))
    let f : KSTPairL2 := actualFullPeriodTwoSourceIntervalAssembly.symm a
    have hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain := by
      change actualFullPeriodTwoSourceIntervalAssembly f ∈ actualFullPeriodTwoSourceBlockDomain
      dsimp only [f]
      rw [actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply]
      exact ha
    have haf : actualFullPeriodTwoSourceIntervalAssembly f = a :=
      actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply a
    have hfne : f ≠ 0 := by
      intro hfzero
      apply hane
      calc
        a = actualFullPeriodTwoSourceIntervalAssembly f := haf.symm
        _ = actualFullPeriodTwoSourceIntervalAssembly 0 := congrArg _ hfzero
        _ = 0 := map_zero actualFullPeriodTwoSourceIntervalAssembly
    refine ⟨⟨f, hf⟩, hfne, ?_⟩
    apply actualFullPeriodTwoSourceIntervalAssembly.injective
    have hdomain : (⟨actualFullPeriodTwoSourceIntervalAssembly f, hf⟩ :
        actualFullPeriodTwoSourceBlockDomain) = ⟨a, ha⟩ := Subtype.ext haf
    calc
      actualFullPeriodTwoSourceIntervalAssembly
          (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂ ⟨f, hf⟩) =
          actualFullPeriodTwoSourceBlockAction u₁ u₂
            ⟨actualFullPeriodTwoSourceIntervalAssembly f, hf⟩ := by
              exact actualFullPeriodTwoDoubledCirclePerturbedDiracAction_repr _ _ _
      _ = z • a := by rw [hdomain]; exact haAction
      _ = z • actualFullPeriodTwoSourceIntervalAssembly f := by rw [haf]
      _ = actualFullPeriodTwoSourceIntervalAssembly (z • f) :=
        (map_smul actualFullPeriodTwoSourceIntervalAssembly z f).symm

end NlsGge.Atomic.KST013
end
