import Mathlib
import NlsGge.Atomic.KSN.KSN018Host
import NlsGge.ThirdConsultation.G1.G1098Reindex

/- KSN019 ASM PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN019Asm.lean.
   SUPPORT (no packet increment): KSN019_of = the KSN-019 head body (Pro, followup13 STATEMENTS/KSN.md, verbatim) from
   (h18) the KSN-018 head body (KSN018_main N hN) and (hSB) the landed KSN001Sup5.scalarBirkhoff_analytic type.
   Route = Pro r15 Q5 row KSN-019 ("local boundedness from quantitative KSN-018 plus coordinate analyticity"; Q6 L1311:
   analyticity through the genuine complex PairScale and the complex-linear pairPotential, not through toSobolevCN):
   * pairPotential N is a continuous ℂ-linear map (ksn019_ppCLM: raw coefficients, norm ≤ 1, then the Fourier isometry),
     so complexDomain N is open and scalarBirkhoff b n ∘ pairPotential is analytic on it;
   * on complexDomain, KSN-018 gives Memℓp at every point, so each coordinate of complexSmoothing is EXACTLY
     scaleWeight·(scalarBirkhoff + raw coefficient) (no sequenceLift fallback), an analytic function;
   * KSN-018 clause 1 gives local boundedness; NlsGge.Atomic.G1098Reindex.analyticOnNhd_of_coords_of_locBdd_reindex
     (G4-007 / GK Thm A.5 over Bool × ℤ ≃ ℤ) gives analyticity; the other clauses are KSN-018's.
   No hypothesis added to the head. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem ksn019_sw_pos (s : ℝ) (n : ℤ) : 0 < scaleWeight s n := by
  unfold scaleWeight bracket
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) s

theorem ksn019_raw_norm_le (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) (n : ℤ) :
    ‖rawCoefficient (N : ℝ) x b n‖ ≤ ‖x (b, n)‖ := by
  unfold rawCoefficient
  have hw : 1 ≤ scaleWeight (N : ℝ) n := by
    unfold scaleWeight bracket
    exact Real.one_le_rpow (le_max_left _ _) (Nat.cast_nonneg N)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  exact div_le_self (norm_nonneg _) hw

/-- The raw coefficient sequence as a continuous ℂ-linear map (norm ≤ 1). -/
def ksn019_rawCLM (N : ℕ) (b : Bool) : PairScale (N : ℝ) →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨rawCoefficient (N : ℝ) x b, rawCoefficient_mem (N : ℝ) (Nat.cast_nonneg N) x b⟩
      map_add' := fun x y => by
        ext n
        simp only [rawCoefficient, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := fun c x => by
        ext n
        simp only [rawCoefficient, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    1 (fun x => by
      rw [one_mul]
      have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      refine lp.norm_le_of_forall_sum_le hp (norm_nonneg _) (fun s => ?_)
      have hx := lp.sum_rpow_le_norm_rpow hp x (s.map ⟨fun n => (b, n), fun a c h => by simpa using h⟩)
      rw [Finset.sum_map] at hx
      refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) hx
      exact Real.rpow_le_rpow (norm_nonneg _) (ksn019_raw_norm_le N x b n) hp.le)

theorem ksn019_rawCLM_apply (N : ℕ) (b : Bool) (x : PairScale (N : ℝ)) (n : ℤ) :
    ksn019_rawCLM N b x n = rawCoefficient (N : ℝ) x b n := rfl

/-- pairPotential N as a continuous ℂ-linear map. -/
def ksn019_ppCLM (N : ℕ) : PairScale (N : ℝ) →L[ℂ] PotPair :=
  ContinuousLinearMap.prod
    ((physicalFourierL2.symm.toContinuousLinearEquiv : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] PhysicalL2).comp
      (ksn019_rawCLM N true))
    ((physicalFourierL2.symm.toContinuousLinearEquiv : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] PhysicalL2).comp
      (ksn019_rawCLM N false))

theorem ksn019_pp_eq (N : ℕ) : pairPotential (N : ℝ) (Nat.cast_nonneg N) = fun x => ksn019_ppCLM N x := by
  funext x
  rfl

theorem ksn019_complexDomain_open (N : ℕ) : IsOpen (complexDomain (N : ℝ) (Nat.cast_nonneg N)) := by
  show IsOpen (pairPotential (N : ℝ) (Nat.cast_nonneg N) ⁻¹' sourceBetaW)
  rw [ksn019_pp_eq]
  exact sourceFamily.V_open.preimage (ksn019_ppCLM N).continuous

theorem ksn019_smoothing_analytic (N : ℕ)
    (hSB : ∀ (b : Bool) (n : ℤ), AnalyticOnNhd ℂ (scalarBirkhoff b n) sourceBetaW) (b : Bool) (n : ℤ) :
    AnalyticOnNhd ℂ (fun x => smoothingCoefficient N x b n) (complexDomain (N : ℝ) (Nat.cast_nonneg N)) := by
  intro x hx
  have h1 : AnalyticAt ℂ (fun y => scalarBirkhoff b n (ksn019_ppCLM N y)) x :=
    (hSB b n (ksn019_ppCLM N x) hx).comp ((ksn019_ppCLM N).analyticAt x)
  have h2 : AnalyticAt ℂ (fun y => ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (if b then -n else n)).comp
      (ksn019_rawCLM N b)) y) x := ContinuousLinearMap.analyticAt _ x
  have h := h1.add h2
  refine h.congr (Filter.Eventually.of_forall (fun y => ?_))
  simp only [smoothingCoefficient, ksn019_pp_eq, ContinuousLinearMap.comp_apply]
  rfl

theorem KSN019_of (N : ℕ) (hN : 1 ≤ N)
    (h18 :
        (∀ x₀ ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
          ∃ (U : Set (PairScale (N : ℝ))) (C : ℝ),
            IsOpen U ∧ x₀ ∈ U ∧ U ⊆ complexDomain (N : ℝ) (Nat.cast_nonneg N) ∧ 0 ≤ C ∧
            ∀ x ∈ U, Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
              ‖complexSmoothing N x‖ ≤ C) ∧
        (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
          ∀ x : PairScale (N : ℝ), IsRealPair (N : ℝ) x → ‖x‖ ≤ B →
            Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
            ‖complexSmoothing N x‖ ≤ C))
    (hSB : ∀ (b : Bool) (n : ℤ), AnalyticOnNhd ℂ (scalarBirkhoff b n) sourceBetaW) :
  AnalyticOnNhd ℂ (complexSmoothing N) (complexDomain (N : ℝ) (Nat.cast_nonneg N)) ∧
  (∀ x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
    Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
    ∀ b n, rawCoefficient ((N : ℝ) + 1) (complexSmoothing N x) b n =
      smoothingCoefficient N x b n) ∧
  (∀ x₀ ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
    ∃ (U : Set (PairScale (N : ℝ))) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain (N : ℝ) (Nat.cast_nonneg N) ∧ 0 ≤ C ∧
      ∀ x ∈ U, ‖complexSmoothing N x‖ ≤ C) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale (N : ℝ), IsRealPair (N : ℝ) x → ‖x‖ ≤ B →
      ‖complexSmoothing N x‖ ≤ C) := by
  have hopen := ksn019_complexDomain_open N
  have hmem : ∀ x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
      Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 := by
    intro x hx
    obtain ⟨U, C, -, hxU, -, -, hU⟩ := h18.1 x hx
    exact (hU x hxU).1
  have hcs : ∀ (x : PairScale (N : ℝ)) (hx : x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N)),
      complexSmoothing N x = ⟨storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x), hmem x hx⟩ := by
    intro x hx
    unfold complexSmoothing sequenceLift
    rw [dif_pos (hmem x hx)]
  refine ⟨?_, fun x hx => ⟨hmem x hx, fun b n => ?_⟩, fun x₀ hx₀ => ?_, fun B hB => ?_⟩
  · obtain ⟨σ⟩ : Nonempty ((Bool × ℤ) ≃ ℤ) := nonempty_equiv_of_countable
    refine NlsGge.Atomic.G1098Reindex.analyticOnNhd_of_coords_of_locBdd_reindex σ (complexSmoothing N) hopen
      (fun j => ?_) (fun x hx => ?_)
    · have ha : AnalyticOnNhd ℂ (fun x => (scaleWeight ((N : ℝ) + 1) j.2 : ℂ) * smoothingCoefficient N x j.1 j.2)
          (complexDomain (N : ℝ) (Nat.cast_nonneg N)) := fun x hx =>
        analyticAt_const.mul (ksn019_smoothing_analytic N hSB j.1 j.2 x hx)
      refine ha.congr hopen (fun x hx => ?_)
      rw [hcs x hx]
      rfl
    · obtain ⟨U, C, hUo, hxU, -, -, hU⟩ := h18.1 x hx
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo x hxU
      exact ⟨r, hr, C, fun y hy => (hU y (hrU hy)).2⟩
  · unfold rawCoefficient
    rw [hcs x hx]
    show (scaleWeight ((N : ℝ) + 1) n : ℂ) * smoothingCoefficient N x b n / (scaleWeight ((N : ℝ) + 1) n : ℂ) = _
    have h0 : (scaleWeight ((N : ℝ) + 1) n : ℂ) ≠ 0 := by exact_mod_cast (ksn019_sw_pos _ n).ne'
    field_simp
  · obtain ⟨U, C, hUo, hxU, hUs, hC, hU⟩ := h18.1 x₀ hx₀
    exact ⟨U, C, hUo, hxU, hUs, hC, fun x hx => (hU x hx).2⟩
  · obtain ⟨C, hC, hB'⟩ := h18.2 B hB
    exact ⟨C, hC, fun x hxr hx => (hB' x hxr hx).2⟩

end
end NlsGge.ThirdConsultation.KSN
