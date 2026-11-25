import Mathlib
import QuantumNLS.Local003DressedAnalytic
import QuantumNLS.Local003Hermitian
import QuantumNLS.TerraMultiRound27Analytic

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage S3b: real-analyticity of the actual
reduced map `u ↦ B_n(u)` and of its matrix entries `a_n(u) = Re B₀₀`, `b_n(u) = B₁₀` on the common ball.

* `adjR`: the adjoint `A ↦ A†` is a (conjugate-linear isometric, hence) continuous REAL-linear map `B(H,K) → B(K,H)`.
* `invSqrt_analyticAt`: `T ↦ ∑ binom(-1/2,k) T^k` is analytic at every `T₀` with `‖T₀‖ < 1` (power series
  `FormalMultilinearSeries.ofScalars`, radius `≥ 1` since `|binom(-1/2,k)| ≤ 1`).
* `reducedMat_analytic`: with `P(u)` (LOCAL-002 `proj_analytic`), the dressed integral (`Local003DressedAnalytic`),
  the compression (Terra r27) and the inverse square root: `B = p 1 + S† E†(P† D P)E S`, a product in the Banach algebra
  `B(ℂ²)` of analytic factors. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Analytic
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.LocalSpectral.Round27

variable {L κ r : ℝ}

/-- The adjoint as a continuous real-linear map. -/
def adjR (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    (H →L[ℂ] K) →L[ℝ] (K →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun A => ContinuousLinearMap.adjoint A
      map_add' := fun A B => map_add ContinuousLinearMap.adjoint A B
      map_smul' := fun c A => by
        have h1 : (c • A : H →L[ℂ] K) = ((c : ℂ) • A) := (Complex.coe_smul c A).symm
        simp only [RingHom.id_apply]
        rw [h1, map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }
    1 (fun A => by
      have := (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := H) (F := K)).norm_map A
      simpa using this.le)

lemma adjR_apply {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (A : H →L[ℂ] K) :
    adjR H K A = ContinuousLinearMap.adjoint A := rfl

/-- The inverse square root series is analytic on the open unit ball. -/
lemma invSqrt_analyticAt {T0 : E2 →L[ℂ] E2} (h : ‖T0‖ < 1) :
    AnalyticAt ℂ (fun T : E2 →L[ℂ] E2 => ∑' k : ℕ, (invSqrtCoeff k : ℂ) • T ^ k) T0 := by
  let c : ℕ → ℂ := fun k => (invSqrtCoeff k : ℂ)
  let p : FormalMultilinearSeries ℂ (E2 →L[ℂ] E2) (E2 →L[ℂ] E2) :=
    FormalMultilinearSeries.ofScalars (E2 →L[ℂ] E2) c
  have hrad : (1 : ℝ≥0∞) ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun s hs => ?_
    have hs1 : (s : ℝ) < 1 := by exact_mod_cast hs
    refine p.le_radius_of_bound 1 (fun n => ?_)
    rw [FormalMultilinearSeries.ofScalars_norm]
    have h1 : ‖c n‖ ≤ 1 := by
      simp only [c, Complex.norm_real, Real.norm_eq_abs]
      exact abs_invSqrtCoeff_le n
    have h2 : (s : ℝ) ^ n ≤ 1 := pow_le_one₀ s.2 hs1.le
    calc ‖c n‖ * (s : ℝ) ^ n ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hball := p.hasFPowerSeriesOnBall (lt_of_lt_of_le one_pos hrad)
  have hmem : T0 ∈ Metric.eball (0 : E2 →L[ℂ] E2) p.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    have h1 : ‖T0‖ₑ < 1 := by rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_lt_one.2 h
    exact lt_of_lt_of_le h1 hrad
  have han := hball.analyticAt_of_mem hmem
  have hfun : p.sum = fun T : E2 →L[ℂ] E2 => ∑' k : ℕ, (invSqrtCoeff k : ℂ) • T ^ k := by
    have := FormalMultilinearSeries.ofScalarsSum_eq_tsum (E := E2 →L[ℂ] E2) c
    exact this
  rw [← hfun]; exact han


/-- `U'(u) = P(u) E S(u)`, `S(u) = C(u)^{-1/2}` (series, no smallness proof argument). -/
def Uf (L κ : ℝ) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : E2 →L[ℂ] H2 L :=
  (perturbedProj L κ u n r) ∘L (embed L n) ∘L (invSqrtM (compressionMatrix L κ u n r))

/-- `B(u)` without the smallness proof argument. -/
def Bf (L κ : ℝ) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : E2 →L[ℂ] E2 :=
  (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2 +
    (ContinuousLinearMap.adjoint (Uf L κ u n r)) ∘L (dressedIntegral L κ u n r) ∘L (Uf L κ u n r)

lemma reducedMatrix2_eq {u : ℝ → ℂ} {n : ℤ} (h : SmallCompression L κ u n r) :
    reducedMatrix2 L κ u n r h = Bf L κ u n r := rfl

/-- The fixed conjugation `X ↦ E† X E`. -/
def Fm (L : ℝ) (n : ℤ) : (H2 L →L[ℂ] H2 L) →L[ℂ] (E2 →L[ℂ] E2) :=
  (ContinuousLinearMap.compL ℂ E2 (H2 L) E2 (ContinuousLinearMap.adjoint (embed L n))).comp
    ((ContinuousLinearMap.compL ℂ E2 (H2 L) (H2 L)).flip (embed L n))

lemma Bf_eq (u : ℝ → ℂ) (n : ℤ) (r : ℝ) :
    Bf L κ u n r = (pm L n : ℂ) • (1 : E2 →L[ℂ] E2) +
      (ContinuousLinearMap.adjoint (invSqrtM (compressionMatrix L κ u n r))) *
        (Fm L n ((ContinuousLinearMap.adjoint (perturbedProj L κ u n r)) *
          dressedIntegral L κ u n r * perturbedProj L κ u n r)) *
        invSqrtM (compressionMatrix L κ u n r) := by
  unfold Bf Uf
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
  ext v
  simp [Fm, ContinuousLinearMap.mul_apply]

/-- **Real-analyticity of the actual reduced map** on a ball where the compression stays within the radius of
convergence of the inverse square root series. -/
theorem Bf_analytic (hyp : FreeResolventHyp L κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) {ρ : ℝ}
    (hρ : 2 * Real.sqrt κ * Cconst L r * ρ ≤ 1)
    (hsmall : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ < 1) :
    AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) => Bf L κ (u : ℝ → ℂ) n r) (ball 0 ρ) := by
  intro u hu
  have hP := proj_analytic hyp hr hr2 n hρ u hu
  have hD := Local003DressedAnalytic.dressed_analytic hyp hr hr2 n hρ u hu
  have hC := compression_analytic hyp hr hr2 n hρ u hu
  have hS : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) => invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r)) u := by
    have h1 : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) => compressionMatrix L κ (u : ℝ → ℂ) n r - 1) u :=
      hC.sub analyticAt_const
    have h2 := (invSqrt_analyticAt (hsmall u hu)).restrictScalars (𝕜 := ℝ)
    exact AnalyticAt.comp (f := fun u : Lp ℂ 2 (μI L) => compressionMatrix L κ (u : ℝ → ℂ) n r - 1)
      (x := u) h2 h1
  have hPa : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) => adjR (H2 L) (H2 L) (perturbedProj L κ (u : ℝ → ℂ) n r)) u :=
    ((adjR (H2 L) (H2 L)).analyticAt _).comp hP
  have hSa : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) =>
      adjR E2 E2 (invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r))) u :=
    ((adjR E2 E2).analyticAt _).comp hS
  have hmid : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) =>
      Fm L n (adjR (H2 L) (H2 L) (perturbedProj L κ (u : ℝ → ℂ) n r) *
        dressedIntegral L κ (u : ℝ → ℂ) n r * perturbedProj L κ (u : ℝ → ℂ) n r)) u :=
    (((Fm L n).restrictScalars ℝ).analyticAt _).comp ((hPa.mul hD).mul hP)
  have hall := (analyticAt_const (v := (pm L n : ℂ) • (1 : E2 →L[ℂ] E2))).add ((hSa.mul hmid).mul hS)
  refine hall.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [Pi.add_apply, Pi.mul_apply]
  exact (Bf_eq _ n r).symm

/-- The entries `(B e₀)ⱼ` are real-analytic on the ball. -/
theorem entry_analytic (hyp : FreeResolventHyp L κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) {ρ : ℝ}
    (hρ : 2 * Real.sqrt κ * Cconst L r * ρ ≤ 1)
    (hsmall : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ < 1)
    (j : Fin 2) :
    AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) => (Bf L κ (u : ℝ → ℂ) n r (vec2 1 0)) j) (ball 0 ρ) := by
  intro u hu
  let Λ : (E2 →L[ℂ] E2) →L[ℂ] ℂ :=
    (EuclideanSpace.proj j : E2 →L[ℂ] ℂ).comp (ContinuousLinearMap.apply ℂ E2 (vec2 1 0))
  exact ((Λ.restrictScalars ℝ).analyticAt _).comp (Bf_analytic hyp hr hr2 n hρ hsmall u hu)

/-- **LOCAL-003, analytic part of the matrix form**: on the single ball `‖u‖ < compressionRadius κ L r` (independent of
`n`), the reduced map is `[[a_n(u), conj b_n(u)],[b_n(u), a_n(u)]]` with `a_n : L² → ℝ` and `b_n : L² → ℂ` real-analytic
(Hermiticity and swap symmetry: `Local003Hermitian.reducedMatrix_form`). -/
theorem reducedMatrix_form_analytic (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, ∃ (a : Lp ℂ 2 (μI L) → ℝ) (b : Lp ℂ 2 (μI L) → ℂ),
      AnalyticOnNhd ℝ a (ball 0 ρ) ∧ AnalyticOnNhd ℝ b (ball 0 ρ) ∧
      ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, ∀ h : SmallCompression L κ (u : ℝ → ℂ) n r, ∀ v : E2,
        reducedMatrix2 L κ (u : ℝ → ℂ) n r h v =
          vec2 ((a u : ℂ) * v 0 + conj (b u) * v 1) (b u * v 0 + (a u : ℂ) * v 1) := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  refine ⟨compressionRadius κ L r, compressionRadius_pos κ L r, fun n => ?_⟩
  have hρ : 2 * Real.sqrt κ * Cconst L r * compressionRadius κ L r ≤ 1 := by
    unfold compressionRadius
    have h0 := Cconst_nonneg L r
    set c : ℝ := 2 * Real.sqrt κ * Cconst L r with hc
    have hc0 : 0 ≤ c := by positivity
    rw [show c * (2 * (1 + 2 * Real.sqrt κ * Cconst L r))⁻¹ = c * (2 * (1 + c))⁻¹ by rw [hc]]
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    nlinarith
  have hsmall : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) (compressionRadius κ L r),
      ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ < 1 := fun u hu =>
    (smallCompression_on_ball hL hyp hr hr2 u (by simpa using hu) n).1
  refine ⟨fun u => (Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 0).re,
    fun u => Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 1, ?_, ?_, ?_⟩
  · intro u hu
    exact ((Complex.reCLM.analyticAt _).comp (entry_analytic hyp hr hr2 n hρ hsmall 0 u hu))
  · exact entry_analytic hyp hr hr2 n hρ hsmall 1
  · intro u hu h v
    obtain ⟨a', b', hform⟩ := QuantumNLS.Local003Hermitian.reducedMatrix_form hL hr hr2 n u
      (by simpa using hu) h
    have e0 := hform (vec2 1 0)
    rw [reducedMatrix2_eq h] at e0
    have ha : Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 0 = (a' : ℂ) := by
      have := congrArg (fun w : E2 => w 0) e0
      simpa [vec2] using this
    have hb : Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 1 = b' := by
      have := congrArg (fun w : E2 => w 1) e0
      simpa [vec2] using this
    simp only [ha, hb, Complex.ofReal_re]
    exact hform v

end QuantumNLS.Local003Analytic
#print axioms QuantumNLS.Local003Analytic.invSqrt_analyticAt
#print axioms QuantumNLS.Local003Analytic.Bf_analytic
#print axioms QuantumNLS.Local003Analytic.reducedMatrix_form_analytic
