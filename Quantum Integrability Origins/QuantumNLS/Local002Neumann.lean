import Mathlib
import QuantumNLS.LocalSpectralOperator

/-! LOCAL-002 `lem:reset-analytic-projections` (spectral_reduction.tex:57), stage A: the Neumann
resolvent of `𝓛_u` on `D_σ` in the frozen DEF-049 encoding.

Abstract statement (`resolvent_of_neumann`): let `R0` be the resolvent of `𝓛_0` at `z` in the sense of
`LocalSpectral.IsResolvent` and let `T` be a bounded operator with `‖T‖ < 1` acting as `T φ = V_u (R0 φ)`
almost everywhere (`V_u(x) = [[0, -2i√κ ū],[2i√κ u, 0]]`).  Then `R = R0 (1 - T)^{-1}` is the resolvent of
`𝓛_u` at `z` in the sense of `IsResolvent`, with `‖R‖ ≤ ‖R0‖/(1-‖T‖)` and `‖R - R0‖ ≤ ‖R0‖ ‖T‖/(1-‖T‖)`.
No property of `u` beyond the representation of `T` is used (no relative-boundedness theorem). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local002
open QuantumNLS.LocalSpectral

/-- `V_u(x) g`: the potential matrix acting on `g ∈ ℂ²` (`lopPt` with zero derivative). -/
def Vpt (κ : ℝ) (w : ℂ) (g : E2) : E2 := lopPt κ w 0 g

lemma Jm_zero : Jm (0 : E2) = 0 := by
  ext i; fin_cases i <;> simp [Jm, vec2]

lemma lopPt_split (κ : ℝ) (w : ℂ) (d g : E2) :
    lopPt κ w d g = (2 * Complex.I) • Jm d + Vpt κ w g := by
  unfold Vpt lopPt
  rw [Jm_zero]; simp

lemma Vpt_zero_pot (κ : ℝ) (g : E2) : Vpt κ 0 g = 0 := by
  ext i; fin_cases i <;> simp [Vpt, lopPt, Jm, vec2]

lemma lopPt_zero_pot (κ : ℝ) (d g : E2) : lopPt κ 0 d g = (2 * Complex.I) • Jm d := by
  rw [lopPt_split, Vpt_zero_pot, add_zero]

/-- `J` as a continuous linear map of `ℂ²`. -/
def Jcl : E2 →L[ℂ] E2 :=
  LinearMap.toContinuousLinearMap
    { toFun := Jm
      map_add' := fun a b => by ext i; fin_cases i <;> simp [Jm, vec2] <;> ring
      map_smul' := fun c a => by ext i; fin_cases i <;> simp [Jm, vec2] }

lemma Jcl_apply (v : E2) : Jcl v = Jm v := rfl

/-- `(1 - T)^{-1}` for `‖T‖ < 1`, with its norm bound. -/
lemma exists_inv_one_sub {A : Type*} [NormedRing A] [CompleteSpace A] (h1n : ‖(1 : A)‖ ≤ 1) (T : A)
    (hT : ‖T‖ < 1) :
    ∃ S : A, (1 - T) * S = 1 ∧ S * (1 - T) = 1 ∧ ‖S‖ ≤ (1 - ‖T‖)⁻¹ := by
  refine ⟨↑(Units.oneSub T hT)⁻¹, ?_, ?_, ?_⟩
  · have := (Units.oneSub T hT).mul_inv
    simpa using this
  · have := (Units.oneSub T hT).inv_mul
    simpa using this
  · set S : A := ↑(Units.oneSub T hT)⁻¹ with hS
    have h1 : (1 - T) * S = 1 := by
      have := (Units.oneSub T hT).mul_inv
      rwa [Units.val_oneSub] at this
    have h2 : S = 1 + T * S := by
      have : S - T * S = 1 := by rw [← h1, sub_mul, one_mul]
      rw [← this]; abel
    have h3 : ‖S‖ ≤ 1 + ‖T‖ * ‖S‖ := by
      calc ‖S‖ = ‖1 + T * S‖ := by rw [← h2]
        _ ≤ ‖(1 : A)‖ + ‖T * S‖ := norm_add_le _ _
        _ ≤ 1 + ‖T‖ * ‖S‖ := by gcongr; exact norm_mul_le _ _
    have hpos : 0 < 1 - ‖T‖ := by linarith
    rw [← one_div, le_div_iff₀ hpos]
    nlinarith

section Neumann

variable {L κ : ℝ}

lemma coe_zsub (z : ℂ) (F φ : H2 L) :
    ((z • F - φ : H2 L) : ℝ → E2) =ᵐ[μI L] fun x => z • (F : ℝ → E2) x - (φ : ℝ → E2) x := by
  filter_upwards [Lp.coeFn_sub (z • F) φ, Lp.coeFn_smul z F] with x h1 h2
  rw [h1]
  simp [h2]

/-- **Neumann resolvent.** -/
theorem resolvent_of_neumann {u : ℝ → ℂ} {σ : ℤˣ} {z : ℂ} {R0 T : H2 L →L[ℂ] H2 L}
    (h0 : IsResolvent L κ (fun _ => 0) σ z R0)
    (hT : ∀ φ : H2 L, (T φ : ℝ → E2) =ᵐ[μI L] fun x => Vpt κ (u x) ((R0 φ : ℝ → E2) x))
    (hq : ‖T‖ < 1) :
    ∃ S R : H2 L →L[ℂ] H2 L, (1 - T) * S = 1 ∧ S * (1 - T) = 1 ∧ R = R0 * S ∧
      IsResolvent L κ u σ z R ∧ ‖R‖ ≤ ‖R0‖ * (1 - ‖T‖)⁻¹ ∧
      ‖R - R0‖ ≤ ‖R0‖ * ‖T‖ * (1 - ‖T‖)⁻¹ := by
  obtain ⟨S, hS1, hS2, hSn⟩ := exists_inv_one_sub ContinuousLinearMap.norm_id_le T hq
  have hS1' : ∀ φ : H2 L, S φ - T (S φ) = φ := fun φ => by
    have h := congrArg (fun A : H2 L →L[ℂ] H2 L => A φ) hS1
    simpa [sub_mul] using h
  have hS2' : ∀ φ : H2 L, S (φ - T φ) = φ := fun φ => by
    have h := congrArg (fun A : H2 L →L[ℂ] H2 L => A φ) hS2
    simpa [mul_sub] using h
  have hSm : S - 1 = T * S := by
    have : S - T * S = 1 := by rw [← hS1, sub_mul, one_mul]
    rw [← this]; abel
  refine ⟨S, R0 * S, hS1, hS2, rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro φ
    obtain ⟨g, h, hrep, hbd, hae⟩ := h0.1 (S φ)
    refine ⟨g, h, hrep, hbd, ?_⟩
    have hφ : (φ : ℝ → E2) =ᵐ[μI L] fun x => (S φ : ℝ → E2) x - (T (S φ) : ℝ → E2) x := by
      have := Lp.coeFn_sub (S φ) (T (S φ))
      rwa [hS1' φ] at this
    filter_upwards [coe_zsub z (R0 (S φ)) φ, coe_zsub z (R0 (S φ)) (S φ), hφ, hae, hT (S φ),
      hrep.1] with x e1 e2 e3 e4 e5 e6
    change ((z • R0 (S φ) - φ : H2 L) : ℝ → E2) x = lopPt κ (u x) (h x) (g x)
    simp only [lopPt_zero_pot] at e4
    have e7 : z • (R0 (S φ) : ℝ → E2) x - (φ : ℝ → E2) x =
        (z • (R0 (S φ) : ℝ → E2) x - (S φ : ℝ → E2) x) + (T (S φ) : ℝ → E2) x := by
      rw [e3]; abel
    rw [e1, e7, ← e2, e4, e5, e6, lopPt_split]
  · rintro ⟨f, φ⟩ ⟨g, h, hrep, hbd, hae⟩
    have hmem : MemLp (fun x => (2 * Complex.I) • Jm (h x)) 2 (μI L) := by
      have := (Jcl.comp_memLp' hrep.2.1).const_smul (2 * Complex.I)
      convert this using 1
      funext x
      simp [Jcl_apply]
    set ψ₁ : H2 L := hmem.toLp _ with hψ₁
    have hpsi1 : (f, ψ₁) ∈ LuGraph L κ (fun _ => 0) σ := by
      refine ⟨g, h, hrep, hbd, ?_⟩
      filter_upwards [hmem.coeFn_toLp] with x hx
      simp only [lopPt_zero_pot]
      exact hx
    have hψ' : R0 (z • f - ψ₁) = f := h0.2 (f, ψ₁) hpsi1
    have hTψ := hT (z • f - ψ₁)
    rw [hψ'] at hTψ
    have key : (z • f - ψ₁) - T (z • f - ψ₁) = z • f - φ := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (z • f - ψ₁) (T (z • f - ψ₁)), coe_zsub z f ψ₁, hTψ,
        coe_zsub z f φ, hae, hrep.1, hmem.coeFn_toLp] with x a1 a2 a3 a4 a5 a6 a7
      rw [a1, Pi.sub_apply, a2, a3, a4, a5, lopPt_split, ← a6, ← a7]
      simp only [hψ₁]
      abel
    show R0 (S (z • f - φ)) = f
    rw [← key, hS2', hψ']
  · calc ‖R0 * S‖ ≤ ‖R0‖ * ‖S‖ := norm_mul_le _ _
      _ ≤ ‖R0‖ * (1 - ‖T‖)⁻¹ := by gcongr
  · have : R0 * S - R0 = R0 * (T * S) := by rw [← hSm, mul_sub, mul_one]
    rw [this]
    calc ‖R0 * (T * S)‖ ≤ ‖R0‖ * ‖T * S‖ := norm_mul_le _ _
      _ ≤ ‖R0‖ * (‖T‖ * ‖S‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖R0‖ * (‖T‖ * (1 - ‖T‖)⁻¹) := by gcongr
      _ = ‖R0‖ * ‖T‖ * (1 - ‖T‖)⁻¹ := by ring

end Neumann

end QuantumNLS.Local002

#print axioms QuantumNLS.Local002.resolvent_of_neumann
#print axioms QuantumNLS.Local002.exists_inv_one_sub
