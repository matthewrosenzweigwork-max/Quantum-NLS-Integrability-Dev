import NlsGge.Atomic.KST.KST011
import NlsGge.Atomic.LIB.LIB023
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Algebra.GroupWithZero.Commute

set_option autoImplicit false
noncomputable section
namespace NlsGge.Atomic.KST012

theorem inverse_one_sub_of_sq_norm_lt
    {R : Type*} [NormedRing R] [CompleteSpace R] (T : R)
    (h : ‖T ^ 2‖ < 1) :
    IsUnit (1 - T) ∧
      Ring.inverse (1 - T) = (1 + T) * Ring.inverse (1 - T ^ 2) ∧
      (1 - T) * ((1 + T) * Ring.inverse (1 - T ^ 2)) = 1 ∧
      ((1 + T) * Ring.inverse (1 - T ^ 2)) * (1 - T) = 1 := by
  let S : Rˣ := Units.oneSub (T ^ 2) h
  have hpoly : (1 - T) * (1 + T) = (S : R) := by
    change (1 - T) * (1 + T) = 1 - T ^ 2
    noncomm_ring
  have hcomm : Commute (1 - T) (1 + T) := by
    change (1 - T) * (1 + T) = (1 + T) * (1 - T)
    noncomm_ring
  let U : Rˣ := Units.leftOfMul S (1 - T) (1 + T) hpoly hcomm
  have hunit : IsUnit (1 - T) := ⟨U, rfl⟩
  have hinverse : Ring.inverse (1 - T) = (1 + T) * Ring.inverse (1 - T ^ 2) := by
    change Ring.inverse (U : R) = (1 + T) * Ring.inverse (S : R)
    rw [Ring.inverse_unit, Ring.inverse_unit]
    rfl
  refine ⟨hunit, hinverse, ?_, ?_⟩
  · rw [← hinverse]
    exact Ring.mul_inverse_cancel (1 - T) hunit
  · rw [← hinverse]
    exact Ring.inverse_mul_cancel (1 - T) hunit


def potentialOnPn
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) :
    NlsGge.Atomic.KST003.KSTPairL2 →L[ℂ] NlsGge.Atomic.KST003.KSTPairL2 :=
  InnerProductSpace.rankOne ℂ
      (PiLp.single 2 true
        (NlsGge.Schur.fourierMultiplier n
          (NlsGge.Analysis.naturalPhysicalCoverL2 (φ true))))
      (NlsGge.Atomic.KST003.kstPnLower n) +
    InnerProductSpace.rankOne ℂ
      (PiLp.single 2 false
        (NlsGge.Schur.fourierMultiplier (-n)
          (NlsGge.Analysis.naturalPhysicalCoverL2 (φ false))))
      (NlsGge.Atomic.KST003.kstPnUpper n)

private lemma scalar_character_product_ae (k : ℤ) (c : ℂ)
    (f : NlsGge.Schur.SpectralScalarL2) :
    ((c • NlsGge.Schur.fourierMultiplier k f : NlsGge.Schur.SpectralScalarL2) :
        NlsGge.Schur.SpectralCircle → ℂ) =ᵐ[NlsGge.Schur.spectralHaar]
      (fun x => f x * (c • NlsGge.Schur.spectralBasis k :
        NlsGge.Schur.SpectralScalarL2) x) := by
  have hm : (NlsGge.Schur.fourierMultiplier k f : NlsGge.Schur.SpectralCircle → ℂ) =ᵐ[
      NlsGge.Schur.spectralHaar] (fun x => fourier k x * f x) :=
    NlsGge.Schur.fourierMultiplierValue_ae k f
  have hb : (NlsGge.Schur.spectralBasis k : NlsGge.Schur.SpectralCircle → ℂ) =ᵐ[
      NlsGge.Schur.spectralHaar] (fourier k) := coeFn_fourierLp 2 k
  filter_upwards [MeasureTheory.Lp.coeFn_smul c (NlsGge.Schur.fourierMultiplier k f),
    MeasureTheory.Lp.coeFn_smul c (NlsGge.Schur.spectralBasis k), hm, hb] with x ho hi hm' hb'
  rw [ho, hi]
  change c * (NlsGge.Schur.fourierMultiplier k f) x =
    f x * (c * (NlsGge.Schur.spectralBasis k) x)
  rw [hm', hb']
  ring


theorem potentialOnPn_ae
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ)
    (u : NlsGge.Atomic.KST003.KSTPairL2)
    (hu : NlsGge.Atomic.KST003.spectralPn n u = u) :
    ((potentialOnPn φ n u true : NlsGge.Schur.SpectralCircle → ℂ) =ᵐ[
        NlsGge.Schur.spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ true) x * u false x)) ∧
    ((potentialOnPn φ n u false : NlsGge.Schur.SpectralCircle → ℂ) =ᵐ[
        NlsGge.Schur.spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ false) x * u true x)) := by
  have huUpper : u true =
      inner ℂ (NlsGge.Atomic.KST003.kstPnUpper n) u • NlsGge.Schur.spectralBasis (-n) := by
    have h := congrArg (fun v : NlsGge.Atomic.KST003.KSTPairL2 => v true) hu.symm
    rw [NlsGge.Atomic.KST003.spectralPn_apply] at h
    simpa [NlsGge.Atomic.KST003.kstPnUpper, NlsGge.Atomic.KST003.kstPnLower] using h
  have huLower : u false =
      inner ℂ (NlsGge.Atomic.KST003.kstPnLower n) u • NlsGge.Schur.spectralBasis n := by
    have h := congrArg (fun v : NlsGge.Atomic.KST003.KSTPairL2 => v false) hu.symm
    rw [NlsGge.Atomic.KST003.spectralPn_apply] at h
    simpa [NlsGge.Atomic.KST003.kstPnUpper, NlsGge.Atomic.KST003.kstPnLower] using h
  have houtUpper : potentialOnPn φ n u true =
      inner ℂ (NlsGge.Atomic.KST003.kstPnLower n) u •
        NlsGge.Schur.fourierMultiplier n (NlsGge.Analysis.naturalPhysicalCoverL2 (φ true)) := by
    simp [potentialOnPn, InnerProductSpace.rankOne_apply]
  have houtLower : potentialOnPn φ n u false =
      inner ℂ (NlsGge.Atomic.KST003.kstPnUpper n) u •
        NlsGge.Schur.fourierMultiplier (-n) (NlsGge.Analysis.naturalPhysicalCoverL2 (φ false)) := by
    simp [potentialOnPn, InnerProductSpace.rankOne_apply]
  constructor
  · rw [houtUpper, huLower]
    exact scalar_character_product_ae n _ _
  · rw [houtLower, huUpper]
    exact scalar_character_product_ae (-n) _ _


def qEquationSolution
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (u : NlsGge.Atomic.KST003.KSTPairL2) : NlsGge.Atomic.KST003.KSTPairL2 :=
  (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz))
    (NlsGge.Atomic.KST006.qOperator φ n z hz (potentialOnPn φ n u))

def reconstructedComplement
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (u : NlsGge.Atomic.KST003.KSTPairL2) : NlsGge.Atomic.KST003.KSTPairL2 :=
  NlsGge.Atomic.KST004.complementaryMultiplier n z hz
    (potentialOnPn φ n u + qEquationSolution φ n z hz u)

/- INERT, UNCOMPILED PRIVATE PROOF FRAGMENTS.
Root authorization permits only this .lean.txt note while production 830922f7
is frozen. No placeholder proof, new import, or target hypothesis is used.
Names below are provisional private implementation names, not public APIs.
Place inside the existing KST012 namespace only after the separate stage gate.
-/

open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

private def stageA_scalarBasis : HilbertBasis ℤ ℂ SpectralScalarL2 :=
  fourierBasis (T := (2 : ℝ))

private lemma stageA_scalarBasis_apply (m : ℤ) :
    stageA_scalarBasis m = spectralBasis m := by
  exact congrFun (coe_fourierBasis (T := (2 : ℝ))) m

set_option backward.isDefEq.respectTransparency false in
private lemma stageA_scalarBasis_repr (f : SpectralScalarL2) (m : ℤ) :
    stageA_scalarBasis.repr f m = fourierCoeff f m := by
  change (fourierBasis (T := (2 : ℝ))).repr f m = fourierCoeff f m
  simpa only [spectralHaar] using (fourierBasis_repr (T := (2 : ℝ)) f m)

private lemma stageA_coeff_smul (c : ℂ) (f : SpectralScalarL2) (m : ℤ) :
    fourierCoeff (c • f) m = c * fourierCoeff f m := by
  rw [← stageA_scalarBasis_repr, ← stageA_scalarBasis_repr, map_smul]
  rfl

private lemma stageA_coeff_sub (f g : SpectralScalarL2) (m : ℤ) :
    fourierCoeff (f - g) m = fourierCoeff f m - fourierCoeff g m := by
  rw [← stageA_scalarBasis_repr, ← stageA_scalarBasis_repr, ← stageA_scalarBasis_repr, map_sub]
  rfl

private lemma stageA_coeff_basis (a m : ℤ) :
    fourierCoeff (spectralBasis a) m = if m = a then 1 else 0 := by
  calc
    fourierCoeff (spectralBasis a) m =
        inner ℂ (stageA_scalarBasis m) (spectralBasis a) := by
      rw [← stageA_scalarBasis_repr, stageA_scalarBasis.repr_apply_apply]
    _ = if m = a then 1 else 0 := by
      rw [← stageA_scalarBasis_apply a]
      exact (orthonormal_iff_ite.mp stageA_scalarBasis.orthonormal) m a

private lemma stageA_inner_upper (n : ℤ) (h : KSTPairL2) :
    inner ℂ (kstPnUpper n) h = fourierCoeff (h true) (-n) := by
  calc
    inner ℂ (kstPnUpper n) h = inner ℂ (spectralBasis (-n)) (h true) := by
      simp [kstPnUpper, PiLp.inner_apply, Fintype.sum_bool]
    _ = fourierCoeff (h true) (-n) := by
      rw [← stageA_scalarBasis_apply, ← stageA_scalarBasis.repr_apply_apply,
        stageA_scalarBasis_repr]

private lemma stageA_inner_lower (n : ℤ) (h : KSTPairL2) :
    inner ℂ (kstPnLower n) h = fourierCoeff (h false) n := by
  calc
    inner ℂ (kstPnLower n) h = inner ℂ (spectralBasis n) (h false) := by
      simp [kstPnLower, PiLp.inner_apply, Fintype.sum_bool]
    _ = fourierCoeff (h false) n := by
      rw [← stageA_scalarBasis_apply, ← stageA_scalarBasis.repr_apply_apply,
        stageA_scalarBasis_repr]

private lemma stageA_Pn_component (n : ℤ) (h : KSTPairL2) (b : Bool) :
    spectralPn n h b =
      fourierCoeff (h b) (if b then -n else n) •
        spectralBasis (if b then -n else n) := by
  rw [spectralPn_apply, stageA_inner_upper, stageA_inner_lower]
  cases b <;> simp [kstPnUpper, kstPnLower]

private lemma stageA_coeff_Pn (n : ℤ) (h : KSTPairL2) (b : Bool) (m : ℤ) :
    fourierCoeff (spectralPn n h b) m =
      if sourceModeIndex b m = n then fourierCoeff (h b) m else 0 := by
  rw [stageA_Pn_component, stageA_coeff_smul, stageA_coeff_basis]
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

private lemma stageA_coeff_Qn (n : ℤ) (h : KSTPairL2) (b : Bool) (m : ℤ) :
    fourierCoeff (spectralQn n h b) m =
      if sourceModeIndex b m = n then 0 else fourierCoeff (h b) m := by
  change fourierCoeff (h b - spectralPn n h b) m = _
  rw [stageA_coeff_sub, stageA_coeff_Pn]
  by_cases hm : sourceModeIndex b m = n <;> simp [hm]

set_option backward.isDefEq.respectTransparency false in
private lemma stageA_coeff_complement (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) (m : ℤ) :
    fourierCoeff (complementaryMultiplier n z hz h b) m =
      complementaryResolventCoeff n z (sourceModeIndex b m) *
        fourierCoeff (h b) m := by
  change fourierCoeff (scalarComplementaryMultiplier n z hz b (h b)) m = _
  have hr := scalarComplementaryMultiplier_repr n z hz b (h b) m
  change stageA_scalarBasis.repr (scalarComplementaryMultiplier n z hz b (h b)) m =
    complementaryResolventCoeff n z (sourceModeIndex b m) *
      stageA_scalarBasis.repr (h b) m at hr
  simpa only [stageA_scalarBasis_repr] using hr

private lemma stageA_complement_Pn_zero (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) :
    spectralPn n (complementaryMultiplier n z hz h) = 0 := by
  apply PiLp.ext
  intro b
  rw [stageA_Pn_component]
  have hc : fourierCoeff (complementaryMultiplier n z hz h b)
      (if b then -n else n) = 0 := by
    cases b <;> simp [stageA_coeff_complement, sourceModeIndex]
  rw [hc, zero_smul]
  rfl

private lemma stageA_complement_Qrange (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) :
    spectralQn n (complementaryMultiplier n z hz h) =
      complementaryMultiplier n z hz h := by
  change complementaryMultiplier n z hz h -
    spectralPn n (complementaryMultiplier n z hz h) = _
  rw [stageA_complement_Pn_zero, sub_zero]

private lemma stageA_free_output_coeff (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) (m : ℤ) :
    fourierCoeff ((z • complementaryMultiplier n z hz h - spectralQn n h) b) m =
      (sourceModeIndex b m : ℂ) * (Real.pi : ℂ) *
        fourierCoeff (complementaryMultiplier n z hz h b) m := by
  change fourierCoeff (z • (complementaryMultiplier n z hz h b) -
    spectralQn n h b) m = _
  rw [stageA_coeff_sub, stageA_coeff_smul, stageA_coeff_Qn]
  simp only [stageA_coeff_complement]
  by_cases hkn : sourceModeIndex b m = n
  · simp [hkn]
  · have hden := complementary_denominator_ne_zero n (sourceModeIndex b m) z hz hkn
    have hcancel :
        (z - (sourceModeIndex b m : ℂ) * (Real.pi : ℂ)) *
          complementaryResolventCoeff n z (sourceModeIndex b m) = 1 := by
      simp [complementaryResolventCoeff, hkn, hden]
    rw [if_neg hkn]
    calc
      z * (complementaryResolventCoeff n z (sourceModeIndex b m) *
          fourierCoeff (h b) m) - fourierCoeff (h b) m =
          (sourceModeIndex b m : ℂ) * (Real.pi : ℂ) *
            (complementaryResolventCoeff n z (sourceModeIndex b m) *
              fourierCoeff (h b) m) +
          ((z - (sourceModeIndex b m : ℂ) * (Real.pi : ℂ)) *
            complementaryResolventCoeff n z (sourceModeIndex b m) - 1) *
              fourierCoeff (h b) m := by ring
      _ = _ := by rw [hcancel]; simp

set_option backward.isDefEq.respectTransparency false in
private lemma stageA_complement_free_graph (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) :
    HasKSTFreeDiracGraph (complementaryMultiplier n z hz h)
      (z • complementaryMultiplier n z hz h - spectralQn n h) := by
  let y : KSTPairL2 := z • complementaryMultiplier n z hz h - spectralQn n h
  refine ⟨(-Complex.I) • y true, Complex.I • y false, ?_, ?_, ?_⟩
  · apply (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff_iff
      (T := (2 : ℝ)) (m := 1)).2
    intro m
    rw [stageA_coeff_smul]
    have hc := stageA_free_output_coeff n z hz h true m
    change fourierCoeff (y true) m = _ at hc
    simp [sourceModeIndex] at hc
    rw [hc]
    simp only [NlsGge.Atomic.LIB002.fourierMultiplier, pow_one]
    push_cast
    ring
  · apply (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff_iff
      (T := (2 : ℝ)) (m := 1)).2
    intro m
    rw [stageA_coeff_smul]
    have hc := stageA_free_output_coeff n z hz h false m
    change fourierCoeff (y false) m = _ at hc
    simp [sourceModeIndex] at hc
    rw [hc]
    simp only [NlsGge.Atomic.LIB002.fourierMultiplier, pow_one]
    push_cast
    ring
  · apply PiLp.ext
    intro b
    cases b <;> simp [y, smul_smul, Complex.I_mul_I, mul_neg, neg_mul]

/- Actual complementary Fourier coefficients have a genuine absolutely
convergent continuous Fourier synthesis on the same period-two circle.
The synthesis identifies the same L2 class before using its AE representative.
-/

private local instance stageB_spectralHaar_probability : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

private lemma stageB_distance_sq_summable (n : ℤ) :
    Summable (fun m : ℤ => 1 / (Int.natAbs (m - n) : ℝ) ^ 2) := by
  have hbase0 : Summable (fun d : ℤ => 1 / (d : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hbase : Summable (fun d : ℤ => 1 / (Int.natAbs d : ℝ) ^ 2) := by
    convert hbase0 using 1 <;> simp [Nat.cast_natAbs, Int.cast_abs, abs_pow]
  have hshift := (Equiv.addRight (-n)).summable_iff.mpr hbase
  have hs : Summable (fun m : ℤ => 1 / (Int.natAbs (m + -n) : ℝ) ^ 2) :=
    hshift.congr fun m => by rfl
  exact hs.congr fun m => by rw [show m + -n = m - n by omega]

private lemma stageB_resolvent_sq_summable (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (b : Bool) :
    Summable (fun m : ℤ =>
      ‖complementaryResolventCoeff n z (sourceModeIndex b m)‖ ^ 2) := by
  have hs : Summable (fun k : ℤ => ‖complementaryResolventCoeff n z k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
      (stageB_distance_sq_summable n)
    have hsq := (sq_le_sq₀ (norm_nonneg (complementaryResolventCoeff n z k))
      (by positivity : 0 ≤ 1 / (Int.natAbs (k - n) : ℝ))).2
        (complementaryResolventCoeff_bound n k z hz)
    simpa only [div_pow, one_pow] using hsq
  cases b
  · simpa [sourceModeIndex] using hs
  · simpa [sourceModeIndex, Function.comp_def] using (Equiv.neg ℤ).summable_iff.mpr hs

private def stageB_resolventLp (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (b : Bool) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun m => complementaryResolventCoeff n z (sourceModeIndex b m),
    memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        stageB_resolvent_sq_summable n z hz b)⟩

private lemma stageB_holder22 :
    Real.HolderConjugate (2 : ENNReal).toReal (2 : ENNReal).toReal := by
  rw [Real.holderConjugate_iff]
  norm_num

set_option backward.isDefEq.respectTransparency false in
private lemma stageB_complement_coeff_norm_summable (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) :
    Summable (fun m : ℤ =>
      ‖fourierCoeff (complementaryMultiplier n z hz h b) m‖) := by
  have hs := lp.summable_mul stageB_holder22 (stageB_resolventLp n z hz b)
    (stageA_scalarBasis.repr (h b))
  refine hs.congr fun m => ?_
  change ‖complementaryResolventCoeff n z (sourceModeIndex b m)‖ *
      ‖stageA_scalarBasis.repr (h b) m‖ = _
  rw [stageA_scalarBasis_repr, stageA_coeff_complement, norm_mul]

private lemma stageB_complement_coeff_summable (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) :
    Summable (fun m : ℤ =>
      fourierCoeff (complementaryMultiplier n z hz h b) m) :=
  (stageB_complement_coeff_norm_summable n z hz h b).of_norm

private lemma stageB_continuous_synthesis (v : SpectralScalarL2)
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

private lemma stageB_complement_continuous_representative (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) :
    ∃ g : C(SpectralCircle, ℂ),
      ContinuousMap.toLp (E := ℂ) 2 spectralHaar ℂ g =
        complementaryMultiplier n z hz h b ∧
      ((complementaryMultiplier n z hz h b : SpectralCircle → ℂ) =ᵐ[spectralHaar] g) ∧
      HasSum (fun m : ℤ =>
        fourierCoeff (complementaryMultiplier n z hz h b) m •
          (fourier m : C(SpectralCircle, ℂ))) g := by
  obtain ⟨g, hg, hsum⟩ := stageB_continuous_synthesis
    (complementaryMultiplier n z hz h b)
    (stageB_complement_coeff_norm_summable n z hz h b)
  refine ⟨g, hg, ?_, hsum⟩
  have hae : ((ContinuousMap.toLp (E := ℂ) 2 spectralHaar ℂ g : SpectralScalarL2) :
      SpectralCircle → ℂ) =ᵐ[spectralHaar] g :=
    ContinuousMap.coeFn_toLp spectralHaar g
  rwa [hg] at hae

end NlsGge.Atomic.KST012
end

/-
INERT / UNCOMPILED proof candidate. This is a private fragment for the frozen
KST012 context, not production Lean and not a cache/proof result. It is based on
the exact current StageA source plus the reviewed StageB continuous-synthesis
interface. Do not paste into production until the owner freezes the StageB/C
source route and authorizes a separately queued native check.

Required context already imported by KST012.lean / its KST011 dependency:
  NlsGge.Schur.SpectralScalarL2, SpectralCircle, spectralHaar,
  fourier, fourierCoeff, and the StageB HasSum witness.
The local probability instance is repeated explicitly below so that use of
MemLp.integrable is justified by finite measure, rather than by totalization.
-/

open MeasureTheory NlsGge.Schur

namespace NlsGge.Atomic.KST012

local instance : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

private lemma stageC_product_memLp
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
private lemma stageC_product_fourierCoeff
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

private lemma stageC_productLp_fourierCoeff
    (f : SpectralScalarL2) (a : ℤ → ℂ) (g : C(SpectralCircle, ℂ))
    (ha : Summable fun m : ℤ => ‖a m‖)
    (hseries : HasSum (fun m : ℤ => a m • (fourier m : C(SpectralCircle, ℂ))) g)
    (l : ℤ) :
    Summable (fun m : ℤ => a m * fourierCoeff f (l - m)) ∧
      fourierCoeff
          ((stageC_product_memLp f g).toLp (fun x : SpectralCircle => f x * g x)) l =
        ∑' m : ℤ, a m * fourierCoeff f (l - m) := by
  obtain ⟨hsum, hcoeff⟩ := stageC_product_fourierCoeff f a g ha hseries l
  have hrepresentative := (stageC_product_memLp f g).coeFn_toLp
  have hfc := fourierCoeff_congr_ae hrepresentative
  exact ⟨hsum, (congrFun hfc l).trans hcoeff⟩

end NlsGge.Atomic.KST012

noncomputable section
namespace NlsGge.Atomic.KST012

open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/-
INERT / UNCOMPILED private StageD fragment.
Append inside the existing KST012 namespace only after the exact StageB and
StageC fragments have passed their separate native gates and root review.
No import, public head, public definition body, or operator carrier changes.
The only potential lift below is the SAME actual naturalPhysicalCoverL2.
-/

set_option backward.isDefEq.respectTransparency false in
private lemma stageD_qOperator_component_product
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (h : KSTPairL2) (b : Bool) :
    MemLp (fun x : SpectralCircle =>
        NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
          complementaryMultiplier n z hz h (!b) x) 2 spectralHaar ∧
      (NlsGge.Atomic.KST006.qOperator φ n z hz h b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ b) x *
          complementaryMultiplier n z hz h (!b) x) := by
  obtain ⟨g, _hg, hvg, hseries⟩ :=
    stageB_complement_continuous_representative n z hz h (!b)
  have ha := stageB_complement_coeff_norm_summable n z hz h (!b)
  let f : SpectralScalarL2 := NlsGge.Analysis.naturalPhysicalCoverL2 (φ b)
  have hmem : MemLp (fun x : SpectralCircle => f x * g x) 2 spectralHaar :=
    stageC_product_memLp f g
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
    exact stageC_productLp_fourierCoeff f
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
      change stageA_scalarBasis.repr
          (NlsGge.Atomic.KST006.qOperator φ n z hz h false) l =
        ∑' m : ℤ,
          fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 (φ false)) (l - m) *
            (complementaryResolventCoeff n z (-m) *
              stageA_scalarBasis.repr (h true) m) at hc
      simp only [stageA_scalarBasis_repr] at hc
      rw [hc]
      apply tsum_congr
      intro m
      rw [stageA_coeff_complement]
      simp [sourceModeIndex]
    · change fourierCoeff (NlsGge.Atomic.KST006.qOperator φ n z hz h true) l =
        ∑' m : ℤ,
          fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 (φ true)) (l - m) *
            fourierCoeff (complementaryMultiplier n z hz h false) m
      have hc := NlsGge.Atomic.KST006.qOperator_upper_coeff φ n z hz h l
      change stageA_scalarBasis.repr
          (NlsGge.Atomic.KST006.qOperator φ n z hz h true) l =
        ∑' m : ℤ,
          fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 (φ true)) (l - m) *
            (complementaryResolventCoeff n z m *
              stageA_scalarBasis.repr (h false) m) at hc
      simp only [stageA_scalarBasis_repr] at hc
      rw [hc]
      apply tsum_congr
      intro m
      rw [stageA_coeff_complement]
      simp [sourceModeIndex]
  have heq : NlsGge.Atomic.KST006.qOperator φ n z hz h b = p := by
    apply stageA_scalarBasis.repr.injective
    apply lp.ext
    funext l
    simp only [stageA_scalarBasis_repr]
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

/- These are actual consequences for the literal reconstruction, for every
u and every signed label. No inverse identity is used or claimed here: the
last two left sides are T(p+w), and the future small-square/unit proof must
still earn T(p+w)=w before replacing them by qEquationSolution. -/
lemma stageD_reconstructed_actual_bridges
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (u : KSTPairL2) :
    spectralQn n (reconstructedComplement φ n z hz u) =
        reconstructedComplement φ n z hz u ∧
      HasKSTFreeDiracGraph (reconstructedComplement φ n z hz u)
        (z • reconstructedComplement φ n z hz u -
          spectralQn n (potentialOnPn φ n u + qEquationSolution φ n z hz u)) ∧
      MemLp (fun x : SpectralCircle =>
        NlsGge.Analysis.naturalPhysicalCoverL2 (φ true) x *
          reconstructedComplement φ n z hz u false x) 2 spectralHaar ∧
      MemLp (fun x : SpectralCircle =>
        NlsGge.Analysis.naturalPhysicalCoverL2 (φ false) x *
          reconstructedComplement φ n z hz u true x) 2 spectralHaar ∧
      (NlsGge.Atomic.KST006.qOperator φ n z hz
          (potentialOnPn φ n u + qEquationSolution φ n z hz u) true :
            SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ true) x *
          reconstructedComplement φ n z hz u false x) ∧
      (NlsGge.Atomic.KST006.qOperator φ n z hz
          (potentialOnPn φ n u + qEquationSolution φ n z hz u) false :
            SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (φ false) x *
          reconstructedComplement φ n z hz u true x) := by
  obtain ⟨hmut, hat⟩ := stageD_qOperator_component_product φ n z hz
    (potentialOnPn φ n u + qEquationSolution φ n z hz u) true
  obtain ⟨hmuf, haf⟩ := stageD_qOperator_component_product φ n z hz
    (potentialOnPn φ n u + qEquationSolution φ n z hz u) false
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [reconstructedComplement] using
      stageA_complement_Qrange n z hz
        (potentialOnPn φ n u + qEquationSolution φ n z hz u)
  · simpa only [reconstructedComplement] using
      stageA_complement_free_graph n z hz
        (potentialOnPn φ n u + qEquationSolution φ n z hz u)
  · simpa only [reconstructedComplement, Bool.not_true] using hmut
  · simpa only [reconstructedComplement, Bool.not_false] using hmuf
  · simpa only [reconstructedComplement, Bool.not_true] using hat
  · simpa only [reconstructedComplement, Bool.not_false] using haf

end NlsGge.Atomic.KST012
end

noncomputable section
namespace NlsGge.Atomic.KST012

open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace

/-
INERT / UNCOMPILED future assembly. This note is not production Lean and has
no native/type/axiom/MCP status. It requires the separately checked StageB,
StageC and StageD bodies before application. The final public head is copied
literally from approved proposal8ab04e; no new premise is added.
-/

private lemma stageE_opNorm_le_actual_hsNorm
    (S : KSTPairL2 →L[ℂ] KSTPairL2)
    (hS : NlsGge.Pilot.IsComplexHilbertSchmidt S) :
    ‖S‖ ≤ NlsGge.Pilot.complexHilbertSchmidtNorm S := by
  let b := NlsGge.Pilot.chosenComplexHilbertBasis (E := KSTPairL2)
  have hs := NlsGge.Pilot.summable_basis_of_isComplexHilbertSchmidt b hS
  calc
    ‖S‖ ≤ Real.sqrt (∑' i, ‖S (b i)‖ ^ 2) :=
      NlsGge.Atomic.LIB023.opNorm_le_sqrt_columns b S hs
    _ = NlsGge.Pilot.complexHilbertSchmidtNorm S :=
      (NlsGge.Pilot.complexHilbertSchmidtNorm_eq_basis b hs).symm

theorem qEquation_solve_locally
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ ψ : NlsGge.Atomic.KST002.PhysicalPairLp, ‖ψ - φ‖ < ε →
        ∀ n : ℤ, N₀ ≤ n.natAbs →
          ∀ (z : ℂ) (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n),
            let T : NlsGge.Atomic.KST003.KSTPairL2 →L[ℂ]
                NlsGge.Atomic.KST003.KSTPairL2 :=
              NlsGge.Atomic.KST006.qOperator ψ n z hz
            IsUnit (1 - T) ∧
            Ring.inverse (1 - T) = (1 + T) * Ring.inverse (1 - T ^ 2) ∧
            (1 - T) * ((1 + T) * Ring.inverse (1 - T ^ 2)) = 1 ∧
            ((1 + T) * Ring.inverse (1 - T ^ 2)) * (1 - T) = 1 ∧
            ∀ u : NlsGge.Atomic.KST003.KSTPairL2,
              NlsGge.Atomic.KST003.spectralPn n u = u →
              (1 - T) (qEquationSolution ψ n z hz u) = T (potentialOnPn ψ n u) ∧
              (∀ w : NlsGge.Atomic.KST003.KSTPairL2,
                (1 - T) w = T (potentialOnPn ψ n u) →
                  w = qEquationSolution ψ n z hz u) ∧
              NlsGge.Atomic.KST003.spectralQn n (reconstructedComplement ψ n z hz u) =
                reconstructedComplement ψ n z hz u ∧
              NlsGge.Atomic.KST003.HasKSTFreeDiracGraph
                (reconstructedComplement ψ n z hz u)
                (z • reconstructedComplement ψ n z hz u -
                  NlsGge.Atomic.KST003.spectralQn n
                    (potentialOnPn ψ n u + qEquationSolution ψ n z hz u)) ∧
              ((qEquationSolution ψ n z hz u true : NlsGge.Schur.SpectralCircle → ℂ) =ᵐ[
                  NlsGge.Schur.spectralHaar]
                (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ true) x *
                  reconstructedComplement ψ n z hz u false x)) ∧
              ((qEquationSolution ψ n z hz u false : NlsGge.Schur.SpectralCircle → ℂ) =ᵐ[
                  NlsGge.Schur.spectralHaar]
                (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ false) x *
                  reconstructedComplement ψ n z hz u true x)) := by
  obtain ⟨ε, hε, N₀, hN₀, hlocal⟩ :=
    NlsGge.Atomic.KST011.hs_qOperator_sq_decay φ
  refine ⟨ε, hε, N₀, hN₀, ?_⟩
  intro ψ hψ n hn z hz
  dsimp only
  let T : KSTPairL2 →L[ℂ] KSTPairL2 :=
    NlsGge.Atomic.KST006.qOperator ψ n z hz
  have hsq := (hlocal ψ hψ n hn).2 z hz
  have hsq_finite : NlsGge.Pilot.IsComplexHilbertSchmidt (T ^ 2) := by
    simpa only [T, pow_two, ContinuousLinearMap.mul_def] using hsq.1
  have hsq_bound : NlsGge.Pilot.complexHilbertSchmidtNorm (T ^ 2) ≤ (1 / 2 : ℝ) := by
    simpa only [T, pow_two, ContinuousLinearMap.mul_def] using hsq.2
  have hsmall : ‖T ^ 2‖ < 1 := by
    calc
      ‖T ^ 2‖ ≤ NlsGge.Pilot.complexHilbertSchmidtNorm (T ^ 2) :=
        stageE_opNorm_le_actual_hsNorm (T ^ 2) hsq_finite
      _ ≤ (1 / 2 : ℝ) := hsq_bound
      _ < 1 := by norm_num
  obtain ⟨hunit, hformula, hright, hleft⟩ := inverse_one_sub_of_sq_norm_lt T hsmall
  refine ⟨hunit, hformula, hright, hleft, ?_⟩
  intro u _hu
  let p : KSTPairL2 := potentialOnPn ψ n u
  let w : KSTPairL2 := qEquationSolution ψ n z hz u
  have hw : (1 - T) w = T p := by
    change (1 - T) (Ring.inverse (1 - T) (T p)) = T p
    have happ := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S (T p))
      (Ring.mul_inverse_cancel (1 - T) hunit)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using happ
  have huniq (w' : KSTPairL2) (hw' : (1 - T) w' = T p) : w' = w := by
    have hback : Ring.inverse (1 - T) ((1 - T) w') = w' := by
      have happ := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S w')
        (Ring.inverse_mul_cancel (1 - T) hunit)
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using happ
    calc
      w' = Ring.inverse (1 - T) ((1 - T) w') := hback.symm
      _ = Ring.inverse (1 - T) (T p) :=
        congrArg (fun v : KSTPairL2 => Ring.inverse (1 - T) v) hw'
      _ = w := by rfl
  have hsum : T (p + w) = w := by
    have hs : w - T w = T p := by
      simpa only [sub_apply, one_apply_eq_self] using hw
    calc
      T (p + w) = T p + T w := map_add T p w
      _ = (w - T w) + T w := by rw [hs]
      _ = w := sub_add_cancel _ _
  obtain ⟨hq, hgraph, _hmem_upper, _hmem_lower, hup, hlow⟩ :=
    stageD_reconstructed_actual_bridges ψ n z hz u
  have hupw : (w true : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ true) x *
        reconstructedComplement ψ n z hz u false x) := by
    change (T (p + w) true : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ true) x *
        reconstructedComplement ψ n z hz u false x) at hup
    rw [hsum] at hup
    exact hup
  have hloww : (w false : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ false) x *
        reconstructedComplement ψ n z hz u true x) := by
    change (T (p + w) false : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ false) x *
        reconstructedComplement ψ n z hz u true x) at hlow
    rw [hsum] at hlow
    exact hlow
  exact ⟨hw, huniq, hq, hgraph, hupw, hloww⟩

end NlsGge.Atomic.KST012
end
