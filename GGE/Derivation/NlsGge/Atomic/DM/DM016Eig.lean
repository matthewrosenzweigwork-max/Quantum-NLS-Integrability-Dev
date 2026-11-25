import Mathlib
import NlsGge.ThirdConsultation.DM.DMShared78
import NlsGge.Atomic.DM.DM002
import NlsGge.GK38.GradFundamentalODE
import NlsGge.GK38.PairAnalyticDet
import NlsGge.GK38.PairRealBridge

/- DM-016 support EIG (proof development, author draft; not self-reviewed).
   Bridge E: a zero of the periodic characteristic function `dmPeriodicCharacteristic v lam` yields a nonzero
   periodic or antiperiodic eigenfunction of the genuine realization `zsRealization (scaledPotential v) bc`
   at `pi * lam`, hence `lam ∈ dmSpectrum v bc`.  This generalizes `DM002.N08.exists_unit_eigenpair`
   (real parameter, real-type potential) to complex parameter and arbitrary pair potential, using the
   general-pair ODE facts `GK38.ae_hasDerivAt_fundContP_entry38`, `GK38.ac_fundContP_entry38`. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace NlsGge.ThirdConsultation.DM.Support016
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB038
open NlsGge.Atomic.DM001 NlsGge.Atomic.DM002 NlsGge.Atomic.DM002.N08
open NlsGge.GK38 NlsGge.ThirdConsultation.DM

theorem ae_ode_fundContP (φ : PotPair) (z : ℂ) :
    ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : Fin 2,
      HasDerivAt (fun r => ext38 (fundContP φ z) r a b)
        ((zsCoeffPot38 φ z s * ext38 (fundContP φ z) s) a b) s := by
  filter_upwards [ae_hasDerivAt_fundContP_entry38 φ z 0 0, ae_hasDerivAt_fundContP_entry38 φ z 0 1,
    ae_hasDerivAt_fundContP_entry38 φ z 1 0, ae_hasDerivAt_fundContP_entry38 φ z 1 1] with
    s h00 h01 h10 h11 hs a b
  fin_cases a <;> fin_cases b
  · exact h00 hs
  · exact h01 hs
  · exact h10 hs
  · exact h11 hs

/-- A zero of the periodic characteristic gives a nonzero (anti)periodic eigenpair of the unit-interval
Zakharov-Shabat expression with an arbitrary pair potential and complex spectral parameter. -/
theorem exists_eigenpair_of_perChar_zero (φ : UnitPairL2) (x : ℂ)
    (hz : perChar (unitPhysical (φ true), unitPhysical (φ false)) x = 0) :
    ∃ s : ℂ, s * s = 1 ∧ ∃ g : H1Pair, h1PairValue g ≠ 0 ∧
      (∀ b : Bool, NlsGge.Atomic.LIB026.traceRight (g b) =
        s * NlsGge.Atomic.LIB026.traceLeft (g b)) ∧
      zsApply φ g = x • h1PairValue g := by
  set ψ : PotPair := (unitPhysical (φ true), unitPhysical (φ false)) with hψ
  have hD : (NlsGge.GK38.discrim ψ x) ^ 2 = 4 := by
    rw [perChar_eq] at hz
    linear_combination hz
  set s : ℂ := NlsGge.GK38.discrim ψ x / 2 with hs_def
  have hs : s * s = 1 := by
    rw [hs_def]; linear_combination hD / 4
  have htr : (monodromyPair ψ x).trace = 2 * s := by
    rw [hs_def]; unfold NlsGge.GK38.discrim; ring
  have hdet : (monodromyPair ψ x).det = 1 := det_monodromyPair ψ x
  obtain ⟨a, ha0, haM⟩ := exists_eigvec_of_trace_det (monodromyPair ψ x) s hs htr hdet
  let M : ℝ → PairMat38 := ext38 (fundContP ψ x)
  let F : ℝ → Fin 2 → ℂ := fun t => (M t).mulVec a
  have hFi : ∀ t i, F t i = M t i 0 * a 0 + M t i 1 * a 1 := by
    intro t i
    fin_cases i <;> simp [F, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hac : ∀ i, AbsolutelyContinuousOnInterval (fun t => F t i) 0 1 := by
    intro i
    have h0 := (ac_fundContP_entry38 ψ x i 0).const_smul (a 0)
    have h1 := (ac_fundContP_entry38 ψ x i 1).const_smul (a 1)
    have := h0.add h1
    convert this using 1
    funext t
    rw [hFi]
    simp [M, smul_eq_mul, mul_comm]
  have hP1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0 : ℝ) 1 →
      potRepFst38 ψ t = φ true t := by
    rw [← ae_restrict_iff' measurableSet_Ioc]
    exact e02Pot_ae_unitPhysical (φ true)
  have hP2 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0 : ℝ) 1 →
      potRepSnd38 ψ t = φ false t := by
    rw [← ae_restrict_iff' measurableSet_Ioc]
    exact e02Pot_ae_unitPhysical (φ false)
  have hder : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0 : ℝ) 1 → ∀ b : Bool,
      HasDerivAt (fun s => F s (kk b)) (dfun φ x F b t) t := by
    filter_upwards [ae_ode_fundContP ψ x, hP1, hP2] with t hall h1 h2 ht b
    have hmem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hD : ∀ i : Fin 2, HasDerivAt (fun s => F s i)
        (zsCoeffPot38 ψ x t i 0 * F t 0 + zsCoeffPot38 ψ x t i 1 * F t 1) t := by
      intro i
      have e0 := (hall hmem i 0).mul_const (a 0)
      have e1 := (hall hmem i 1).mul_const (a 1)
      have := e0.add e1
      have hfun : (fun s => F s i) = fun s => M s i 0 * a 0 + M s i 1 * a 1 := by
        funext s; exact hFi s i
      rw [hfun]
      convert this using 1
      rw [hFi t 0, hFi t 1]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have e00 : zsCoeffPot38 ψ x t 0 0 = -Complex.I * x := by
      simp [zsCoeffPot38, zsCoeffPair]
    have e01 : zsCoeffPot38 ψ x t 0 1 = Complex.I * potRepFst38 ψ t := by
      simp [zsCoeffPot38, zsCoeffPair]
    have e10 : zsCoeffPot38 ψ x t 1 0 = -Complex.I * potRepSnd38 ψ t := by
      simp [zsCoeffPot38, zsCoeffPair]
    have e11 : zsCoeffPot38 ψ x t 1 1 = Complex.I * x := by
      simp [zsCoeffPot38, zsCoeffPair]
    cases b
    · have hd : dfun φ x F false t =
          zsCoeffPot38 ψ x t 1 0 * F t 0 + zsCoeffPot38 ψ x t 1 1 * F t 1 := by
        simp only [dfun, kk, Bool.false_eq_true, Bool.not_false, Bool.not_true, if_true, if_false]
        rw [e10, e11, h2 ht]
        ring
      show HasDerivAt (fun s => F s 1) (dfun φ x F false t) t
      rw [hd]
      exact hD 1
    · have hd : dfun φ x F true t =
          zsCoeffPot38 ψ x t 0 0 * F t 0 + zsCoeffPot38 ψ x t 0 1 * F t 1 := by
        simp only [dfun, kk, Bool.false_eq_true, Bool.not_false, Bool.not_true, if_true, if_false]
        rw [e00, e01, h1 ht]
        ring
      show HasDerivAt (fun s => F s 0) (dfun φ x F true t) t
      rw [hd]
      exact hD 0
  obtain ⟨g, hL, hR, hv, heig⟩ := h1_of_solution φ x F hac hder
  have hF0 : ∀ b, F 0 (kk b) = a (kk b) := by
    intro b
    show ((M 0).mulVec a) (kk b) = a (kk b)
    have : M 0 = 1 := by
      show ext38 (fundContP ψ x) 0 = 1
      rw [ext38_of_mem _ ⟨le_rfl, zero_le_one⟩]
      exact fundPair_zero ψ x
    rw [this, Matrix.one_mulVec]
  have hF1 : ∀ b, F 1 (kk b) = s * a (kk b) := by
    intro b
    have := congrFun haM (kk b)
    have hM1 : M 1 = monodromyPair ψ x := by
      show ext38 (fundContP ψ x) 1 = monodromyPair ψ x
      rw [ext38_of_mem _ ⟨zero_le_one, le_rfl⟩]
      rfl
    show ((M 1).mulVec a) (kk b) = s * a (kk b)
    rw [hM1]
    simpa using this
  refine ⟨s, hs, g, ?_, ?_, heig⟩
  · intro hz0
    have key : ∀ b : Bool, a (kk b) = 0 := by
      intro b
      have hb : (g b).value = 0 := by
        have := congrArg (fun p : NlsGge.Schur.SourcePairL2 => p b) hz0
        simpa [h1PairValue] using this
      have hrep : NlsGge.Atomic.LIB026.representative (g b) = 0 := by
        symm
        apply NlsGge.Atomic.LIB026.representative_eq_of_ae
        rw [hb]
        filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)),
          ae_restrict_mem measurableSet_Ioc] with t ht1 ht2
        rw [ht1]
        show Set.IccExtend zero_le_one (0 : C(Set.Icc (0 : ℝ) 1, ℂ)) t = 0
        rw [Set.IccExtend_of_mem zero_le_one _ ⟨ht2.1.le, ht2.2⟩]
        rfl
      have h0 := hL b
      unfold NlsGge.Atomic.LIB026.traceLeft at h0
      rw [hrep, hF0 b] at h0
      exact h0.symm
    apply ha0
    funext i
    fin_cases i
    · exact key true
    · exact key false
  · intro b
    rw [hR b, hL b, hF1 b, hF0 b]

/-- Bridge E: a zero of the periodic characteristic is a periodic or antiperiodic eigenvalue. -/
theorem perChar_zero_mem_dmSpectrum (v : PiPairL2) (lam : ℂ)
    (h : dmPeriodicCharacteristic v lam = 0) :
    ∃ bc : ZSBoundaryCondition, (bc = .periodic ∨ bc = .antiperiodic) ∧
      lam ∈ dmSpectrum v bc := by
  have h' : perChar (unitPhysical (scaledPotential v true), unitPhysical (scaledPotential v false))
      ((Real.pi : ℂ) * lam) = 0 := h
  obtain ⟨s, hs, g, hg0, hgb, hgeig⟩ :=
    exists_eigenpair_of_perChar_zero (scaledPotential v) ((Real.pi : ℂ) * lam) h'
  have hs' : s = 1 ∨ s = -1 := mul_self_eq_one_iff.mp hs
  have key : ∀ bc : ZSBoundaryCondition, HasZSBoundaryCondition bc g →
      lam ∈ dmSpectrum v bc := by
    intro bc hbc
    intro hres
    obtain ⟨T, -, hT2⟩ := hres
    let u : (zsRealization (scaledPotential v) bc).domain :=
      ⟨h1PairValue g, ⟨g, hbc, rfl⟩⟩
    have hAu : zsRealization (scaledPotential v) bc u = ((Real.pi : ℂ) * lam) • h1PairValue g :=
      (zsRealization_apply (scaledPotential v) bc g hbc).trans hgeig
    have h2 := hT2 u
    have hz0 : ((Real.pi : ℂ) * lam) • (u : SourcePairL2) -
        zsRealization (scaledPotential v) bc u = 0 := by
      rw [hAu]; exact sub_self _
    rw [hz0, map_zero] at h2
    apply hg0
    exact h2.symm
  rcases hs' with rfl | rfl
  · refine ⟨.periodic, Or.inl rfl, key _ ?_⟩
    intro b
    simpa using hgb b
  · refine ⟨.antiperiodic, Or.inr rfl, key _ ?_⟩
    intro b
    simpa using hgb b

end NlsGge.ThirdConsultation.DM.Support016
end
