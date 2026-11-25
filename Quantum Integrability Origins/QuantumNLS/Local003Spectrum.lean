import Mathlib
import QuantumNLS.Local003Inst
import QuantumNLS.Local003Mult

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage R2b: the spectrum of `𝓛_u` inside `Γ_n`
consists only of the eigenvalues `a ± |b|`.

For `λ` with `|λ - p_n| < r` that is not a root of the characteristic polynomial of `B_n = [[a, b̄],[b, a]]`, `𝓛_u - λ` has a bounded
inverse (`IsResolvent`).  Riesz decomposition: on `ran P` the inverse is `U (λ - B)⁻¹ U*`; on `ker P` it is minus the reduced
resolvent `S_λ = -(2πi)⁻¹ ∮ (z-λ)⁻¹ R(z) dz`, for which `(S_λ φ, λ S_λ φ + (1-P)φ) ∈ Graph 𝓛_u` (self-adjointness and a scalar
contour computation) and `S_λ (𝓛_u - λ) f = (1-P) f` (resolvent identity). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Spectrum
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local002Rank
  QuantumNLS.Local002Free QuantumNLS.Local003Hermitian QuantumNLS.Local003Proj QuantumNLS.Local003Range
  QuantumNLS.Local003Analytic QuantumNLS.Local003Isometry QuantumNLS.Local003Mult
  QuantumNLS.LocalSpectral.Round27

variable {L κ r : ℝ}

/-- The reduced resolvent `S_λ = -(2πi)⁻¹ ∮ (z-λ)⁻¹ R(z) dz`. -/
def Sred (L κ : ℝ) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) (lam : ℂ) : H2 L →L[ℂ] H2 L :=
  -(((2 * Real.pi * Complex.I)⁻¹ : ℂ) •
    circleIntegral (fun z => (z - lam)⁻¹ • resolvent L κ u (parity n) z) (center L n) r)

lemma ne_lam {n : ℤ} {lam z : ℂ} (hlam : ‖lam - center L n‖ < r) (hz : z ∈ sphere (center L n) r) : z - lam ≠ 0 := by
  intro h
  have h1 := mem_sphere_iff_norm.mp hz
  have : z = lam := sub_eq_zero.mp h
  rw [this] at h1
  linarith

lemma cont_inv {n : ℤ} {lam : ℂ} (hlam : ‖lam - center L n‖ < r) :
    ContinuousOn (fun z : ℂ => (z - lam)⁻¹) (sphere (center L n) r) :=
  (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => ne_lam hlam hz)

lemma two_pi_I_inv : ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * (2 * Real.pi * Complex.I) = 1 :=
  inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])

/-- The scalar contour computation behind both `S_λ` identities. -/
lemma scalar_core (hr : 0 < r) {n : ℤ} {lam : ℂ} (hlam : ‖lam - center L n‖ < r) {g : ℂ → ℂ}
    (hg : ContinuousOn g (sphere (center L n) r)) (c0 : ℂ) :
    -(((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(center L n, r), (z - lam)⁻¹ * (z * g z - c0)) =
      -(((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(center L n, r), g z) +
        lam * (-(((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(center L n, r), (z - lam)⁻¹ * g z)) + c0 := by
  have hinv := cont_inv (L := L) (r := r) (n := n) hlam
  have i1 : CircleIntegrable g (center L n) r := hg.circleIntegrable hr.le
  have i2 : CircleIntegrable (fun z => (z - lam)⁻¹ * g z) (center L n) r :=
    (hinv.mul hg).circleIntegrable hr.le
  have i3 : CircleIntegrable (fun z => (z - lam)⁻¹) (center L n) r := hinv.circleIntegrable hr.le
  have i2' : CircleIntegrable (fun z => lam * ((z - lam)⁻¹ * g z)) (center L n) r :=
    (continuousOn_const.mul (hinv.mul hg)).circleIntegrable hr.le
  have i3' : CircleIntegrable (fun z => c0 * (z - lam)⁻¹) (center L n) r :=
    (continuousOn_const.mul hinv).circleIntegrable hr.le
  have i12 : CircleIntegrable (fun z => g z + lam * ((z - lam)⁻¹ * g z)) (center L n) r :=
    (hg.add (continuousOn_const.mul (hinv.mul hg))).circleIntegrable hr.le
  have hpt : ∀ z ∈ sphere (center L n) r, (z - lam)⁻¹ * (z * g z - c0) =
      g z + lam * ((z - lam)⁻¹ * g z) - c0 * (z - lam)⁻¹ := by
    intro z hz
    have hne := ne_lam hlam hz
    field_simp
    ring
  have hlamb : lam ∈ ball (center L n) r := mem_ball_iff_norm.mpr hlam
  have hcau := circleIntegral.integral_sub_inv_of_mem_ball hlamb
  rw [circleIntegral.integral_congr hr.le hpt, circleIntegral.integral_sub i12 i3',
    circleIntegral.integral_add i1 i2']
  have e1 : ∮ z in C(center L n, r), lam * ((z - lam)⁻¹ * g z) =
      lam * ∮ z in C(center L n, r), (z - lam)⁻¹ * g z := by
    have := circleIntegral.integral_smul lam (fun z => (z - lam)⁻¹ * g z) (center L n) r
    simpa [smul_eq_mul] using this
  have e2 : ∮ z in C(center L n, r), c0 * (z - lam)⁻¹ = c0 * ∮ z in C(center L n, r), (z - lam)⁻¹ := by
    have := circleIntegral.integral_smul c0 (fun z => (z - lam)⁻¹) (center L n) r
    simpa [smul_eq_mul] using this
  rw [e1, e2, hcau]
  have h2 := two_pi_I_inv
  have : ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * (c0 * (2 * Real.pi * Complex.I)) = c0 := by
    rw [mul_comm c0, ← mul_assoc, h2, one_mul]
  linear_combination (-1 : ℂ) * ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * 0 + this

section Main

variable {n : ℤ} {u : Lp ℂ 2 (μI L)}

local notation "RR" => resolvent L κ (u : ℝ → ℂ) (parity n)

/-- Inner-product form of `S_λ`. -/
lemma S_inner (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hq : qpar κ L r u < 1) {lam : ℂ}
    (hlam : ‖lam - center L n‖ < r) (w φ : H2 L) :
    ⟪w, Sred L κ (u : ℝ → ℂ) n r lam φ⟫_ℂ =
      -(((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(center L n, r), (z - lam)⁻¹ * ⟪w, RR z φ⟫_ℂ) := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hcont := res_cont hyp hr hr2 n u hq
  have hF : ContinuousOn (fun z => (z - lam)⁻¹ • RR z) (sphere (center L n) r) :=
    (cont_inv hlam).smul hcont
  unfold Sred
  rw [ContinuousLinearMap.neg_apply, inner_neg_right, inner_circle _ hr.le hF w φ]
  congr 2
  refine circleIntegral.integral_congr hr.le (fun z _ => ?_)
  simp [inner_smul_right]

lemma P_inner (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hq : qpar κ L r u < 1) (w φ : H2 L) :
    ⟪w, perturbedProj L κ (u : ℝ → ℂ) n r φ⟫_ℂ =
      ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(center L n, r), ⟪w, RR z φ⟫_ℂ := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hcont := res_cont hyp hr hr2 n u hq
  rw [proj_unfold]
  exact inner_circle _ hr.le hcont w φ

local notation "PP" => perturbedProj L κ (u : ℝ → ℂ) n r
local notation "GG" => LuGraph L κ (u : ℝ → ℂ) (parity n)

lemma cont_inner_res (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hq : qpar κ L r u < 1) (w φ : H2 L) :
    ContinuousOn (fun z => ⟪w, RR z φ⟫_ℂ) (sphere (center L n) r) := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hcont := res_cont hyp hr hr2 n u hq
  exact ContinuousOn.inner continuousOn_const (hcont.clm_apply continuousOn_const)

/-- `S_λ ψ = λ S_λ w + w - P w` for `(w, ψ) ∈ Graph 𝓛_u`: `S_λ (𝓛_u - λ) w = (1 - P) w` (up to sign). -/
lemma S_graph (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hq : qpar κ L r u < 1) {lam : ℂ}
    (hlam : ‖lam - center L n‖ < r) {w ψ : H2 L} (hp : (w, ψ) ∈ GG) :
    Sred L κ (u : ℝ → ℂ) n r lam ψ = lam • Sred L κ (u : ℝ → ℂ) n r lam w + w - PP w := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  refine ext_inner_left ℂ fun x => ?_
  have hpt : ∀ z ∈ sphere (center L n) r, ⟪x, RR z ψ⟫_ℂ = z * ⟪x, RR z w⟫_ℂ - ⟪x, w⟫_ℂ := by
    intro z hz
    have := (res_isRes hyp hr hr2 n u hq hz).2 (w, ψ) hp
    simp only at this
    rw [map_sub, map_smul] at this
    have h2 : RR z ψ = z • RR z w - w := by
      rw [eq_sub_iff_add_eq, add_comm]; exact (sub_eq_iff_eq_add.mp this).symm
    rw [h2, inner_sub_right, inner_smul_right]
  rw [S_inner hr hr2 hq hlam,
    circleIntegral.integral_congr hr.le (fun z hz => by rw [hpt z hz]),
    scalar_core hr hlam (cont_inner_res hr hr2 hq x w) ⟪x, w⟫_ℂ]
  rw [inner_sub_right, inner_add_right, inner_smul_right, S_inner hr hr2 hq hlam, P_inner hr hr2 hq]
  ring

/-- `(S_λ φ, λ S_λ φ + (1 - P) φ) ∈ Graph 𝓛_u` (self-adjointness). -/
lemma S_pair (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hq : qpar κ L r u < 1)
    (hSA : IsSelfAdjointGraph GG) {lam : ℂ} (hlam : ‖lam - center L n‖ < r) (φ : H2 L) :
    (Sred L κ (u : ℝ → ℂ) n r lam φ,
      lam • Sred L κ (u : ℝ → ℂ) n r lam φ + φ - PP φ) ∈ GG := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  rw [hSA.eq]
  intro p hp
  obtain ⟨w, ψ⟩ := p
  simp only
  have hpt : ∀ z ∈ sphere (center L n) r, ⟪ψ, RR z φ⟫_ℂ = z * ⟪w, RR z φ⟫_ℂ - ⟪w, φ⟫_ℂ := by
    intro z hz
    have hq' := (res_isRes hyp hr hr2 n u hq hz).1 φ
    have := graph_symm (κ := κ) hL hr hr2 n (u : ℝ → ℂ) hp hq'
    simp only at this
    rw [inner_sub_right, inner_smul_right] at this
    rw [← this]
  have key : ⟪ψ, Sred L κ (u : ℝ → ℂ) n r lam φ⟫_ℂ =
      ⟪w, lam • Sred L κ (u : ℝ → ℂ) n r lam φ + φ - PP φ⟫_ℂ := by
    rw [S_inner hr hr2 hq hlam,
      circleIntegral.integral_congr hr.le (fun z hz => by rw [hpt z hz]),
      scalar_core hr hlam (cont_inner_res hr hr2 hq w φ) ⟪w, φ⟫_ℂ]
    rw [inner_sub_right, inner_add_right, inner_smul_right, S_inner hr hr2 hq hlam, P_inner hr hr2 hq]
    ring
  have := congrArg conj key
  rw [inner_conj_symm, inner_conj_symm] at this
  exact this

lemma exists_inv (A : E2 →L[ℂ] E2) (h : Function.Injective A) :
    ∃ T : E2 →L[ℂ] E2, (∀ v, A (T v) = v) ∧ (∀ v, T (A v) = v) := by
  have hsurj : Function.Surjective (A : E2 →ₗ[ℂ] E2) := LinearMap.injective_iff_surjective.mp h
  let e : E2 ≃ₗ[ℂ] E2 := LinearEquiv.ofBijective (A : E2 →ₗ[ℂ] E2) ⟨h, hsurj⟩
  refine ⟨LinearMap.toContinuousLinearMap e.symm.toLinearMap, fun v => ?_, fun v => ?_⟩
  · show A (e.symm v) = v
    exact e.apply_symm_apply v
  · show e.symm (A v) = v
    exact e.symm_apply_apply v

/-- Facts on `U`, `U*`, `P`, `D`, `B` on the good ball. -/
structure UData (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (c : Ctx L κ r n u) : Prop where
  UUs : ∀ x, Uf L κ (u : ℝ → ℂ) n r (ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) x) = PP x
  UsU : ∀ v, ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) (Uf L κ (u : ℝ → ℂ) n r v) = v
  UsP : ∀ x, ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) (PP x) =
    ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) x
  PU : ∀ v, PP (Uf L κ (u : ℝ → ℂ) n r v) = Uf L κ (u : ℝ → ℂ) n r v
  PD : ∀ y, PP (dressedIntegral L κ (u : ℝ → ℂ) n r y) = dressedIntegral L κ (u : ℝ → ℂ) n r (PP y)
  UB : ∀ v, Uf L κ (u : ℝ → ℂ) n r (reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall v) =
    dressedIntegral L κ (u : ℝ → ℂ) n r (Uf L κ (u : ℝ → ℂ) n r v) +
      (pm L n : ℂ) • Uf L κ (u : ℝ → ℂ) n r v
  UBmem : ∀ v, (Uf L κ (u : ℝ → ℂ) n r v,
    Uf L κ (u : ℝ → ℂ) n r (reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall v)) ∈ GG
  UsG : ∀ {f g : H2 L}, (f, g) ∈ GG →
    ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) g =
      reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall (ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) f)

lemma uData (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (c : Ctx L κ r n u) :
    UData hL hr hr2 c := by
  set U := Uf L κ (u : ℝ → ℂ) n r with hU
  have hUU := UUstar c
  have hU1 := UU_one c
  have hUUx : ∀ x, U (ContinuousLinearMap.adjoint U x) = PP x := fun x =>
    congrArg (fun T : H2 L →L[ℂ] H2 L => T x) hUU
  have hU1x : ∀ w, ContinuousLinearMap.adjoint U (U w) = w := fun w =>
    congrArg (fun T : E2 →L[ℂ] E2 => T w) hU1
  have hPU : ∀ v, PP (U v) = U v := fun v => by
    have := hUUx (U v)
    rw [hU1x] at this
    exact this.symm
  have hUsP : ∀ x, ContinuousLinearMap.adjoint U (PP x) = ContinuousLinearMap.adjoint U x := fun x => by
    rw [adjU c]
    simp only [ContinuousLinearMap.comp_apply, PP_apply c]
  have hPsa : ∀ x y, ⟪PP x, y⟫_ℂ = ⟪x, PP y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_left, c.hP]
  have hDsa : ∀ x y, ⟪dressedIntegral L κ (u : ℝ → ℂ) n r x, y⟫_ℂ =
      ⟪x, dressedIntegral L κ (u : ℝ → ℂ) n r y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_left, c.hD]
  have hXi : ∀ f, PP (PP f) = PP f → PP (dressedIntegral L κ (u : ℝ → ℂ) n r (PP f)) =
      dressedIntegral L κ (u : ℝ → ℂ) n r (PP f) := fun f _ => by
    have h := X_inv hr hr2 c hL (f := PP f) (PP_apply c f)
    rw [map_add, map_smul, PP_apply c] at h
    exact add_right_cancel h
  have hPD : ∀ y, PP (dressedIntegral L κ (u : ℝ → ℂ) n r y) = dressedIntegral L κ (u : ℝ → ℂ) n r (PP y) := by
    intro y
    refine ext_inner_left ℂ fun x => ?_
    have hx := hXi x (PP_apply c x)
    have hy := hXi y (PP_apply c y)
    calc ⟪x, PP (dressedIntegral L κ (u : ℝ → ℂ) n r y)⟫_ℂ
        = ⟪PP x, dressedIntegral L κ (u : ℝ → ℂ) n r y⟫_ℂ := (hPsa _ _).symm
      _ = ⟪dressedIntegral L κ (u : ℝ → ℂ) n r (PP x), y⟫_ℂ := (hDsa _ _).symm
      _ = ⟪PP (dressedIntegral L κ (u : ℝ → ℂ) n r (PP x)), y⟫_ℂ := by rw [hx]
      _ = ⟪dressedIntegral L κ (u : ℝ → ℂ) n r (PP x), PP y⟫_ℂ := hPsa _ _
      _ = ⟪PP x, dressedIntegral L κ (u : ℝ → ℂ) n r (PP y)⟫_ℂ := hDsa _ _
      _ = ⟪x, PP (dressedIntegral L κ (u : ℝ → ℂ) n r (PP y))⟫_ℂ := hPsa _ _
      _ = ⟪x, dressedIntegral L κ (u : ℝ → ℂ) n r (PP y)⟫_ℂ := by rw [hy]
  have hB : ∀ v, reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall v =
      (pm L n : ℂ) • v + ContinuousLinearMap.adjoint U (dressedIntegral L κ (u : ℝ → ℂ) n r (U v)) :=
    fun v => rfl
  have hUB : ∀ v, U (reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall v) =
      dressedIntegral L κ (u : ℝ → ℂ) n r (U v) + (pm L n : ℂ) • U v := by
    intro v
    rw [hB, map_add, map_smul, hUUx, hPD, hPU, add_comm]
  have hUBmem : ∀ v, (U v, U (reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall v)) ∈ GG := by
    intro v
    have h := pair_mem hL hr hr2 n u c.hq c.hSA (U v)
    rw [hPU] at h
    rw [hUB]
    exact h
  have hUsG : ∀ {f g : H2 L}, (f, g) ∈ GG →
      ContinuousLinearMap.adjoint U g =
        reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall (ContinuousLinearMap.adjoint U f) := by
    intro f g hfg
    have hPg := P_Lu hr hr2 n u c.hq hfg
    have h1 : ContinuousLinearMap.adjoint U g = ContinuousLinearMap.adjoint U (PP g) := (hUsP g).symm
    rw [h1, hPg, map_add, map_smul, hUsP, hB, hUUx]
    -- `U* (D f) = U* (D (P f))`
    have hDPf : ContinuousLinearMap.adjoint U (dressedIntegral L κ (u : ℝ → ℂ) n r f) =
        ContinuousLinearMap.adjoint U (dressedIntegral L κ (u : ℝ → ℂ) n r (PP f)) := by
      rw [← hUsP (dressedIntegral L κ (u : ℝ → ℂ) n r f), hPD]
    rw [hDPf, add_comm]
  exact ⟨hUUx, hU1x, hUsP, hPU, hPD, hUB, hUBmem, hUsG⟩

/-- **R2b.** For `λ` inside `Γ_n` that is not one of `a ± |b|`, `𝓛_u - λ` has a bounded inverse. -/
theorem spectrum_resolvent (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (hu : ‖u‖ < goodRadius κ L r) (a : ℝ) (b : ℂ)
    (hab : ∀ v : E2, reducedMatrix2 L κ (u : ℝ → ℂ) n r (ctx_of_ball hL hr hr2 n u hu).hsmall v =
      vec2 ((a : ℂ) * v 0 + conj b * v 1) (b * v 0 + (a : ℂ) * v 1))
    (lam : ℂ) (hlam : ‖lam - (pm L n : ℂ)‖ < r) (h1 : lam ≠ ((a + ‖b‖ : ℝ) : ℂ)) (h2 : lam ≠ ((a - ‖b‖ : ℝ) : ℂ)) :
    ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (u : ℝ → ℂ) (parity n) lam R := by
  have c := ctx_of_ball hL hr hr2 n u hu
  have hlam' : ‖lam - center L n‖ < r := hlam
  have hd := uData hL hr hr2 c
  set U := Uf L κ (u : ℝ → ℂ) n r with hU
  set B := reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall with hBdef
  have hherm : ∀ v w, ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ := fun v w =>
    reducedMatrix2_hermitian hL hr hr2 n u c.hq c.hsmall v w
  have hcount := finrank_eigenspace_form a b B hherm hab lam
  have hz : Multiset.count lam {((a + ‖b‖ : ℝ) : ℂ), ((a - ‖b‖ : ℝ) : ℂ)} = 0 := by
    rw [Multiset.count_eq_zero, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
    exact ⟨h1, h2⟩
  rw [hz] at hcount
  let A : E2 →L[ℂ] E2 := lam • ContinuousLinearMap.id ℂ E2 - B
  have hinj : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hBx : B x = lam • x := by
      have : lam • x - B x = 0 := hx
      exact (sub_eq_zero.mp this).symm
    have hmem : x ∈ Module.End.eigenspace (B : E2 →ₗ[ℂ] E2) lam := by
      rw [Module.End.mem_eigenspace_iff]; exact hBx
    have hbot : Module.End.eigenspace (B : E2 →ₗ[ℂ] E2) lam = ⊥ := Submodule.finrank_eq_zero.mp hcount
    rw [hbot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  obtain ⟨T, hAT, hTA⟩ := exists_inv A hinj
  have hAv : ∀ v, A v = lam • v - B v := fun v => rfl
  refine ⟨U ∘L T ∘L ContinuousLinearMap.adjoint U - Sred L κ (u : ℝ → ℂ) n r lam, ?_, ?_⟩
  · intro φ
    set v := T (ContinuousLinearMap.adjoint U φ) with hv
    have hAvφ : lam • v - B v = ContinuousLinearMap.adjoint U φ := by rw [← hAv]; exact hAT _
    have hUBv : U (B v) = lam • U v - PP φ := by
      have := congrArg U hAvφ
      rw [map_sub, map_smul, hd.UUs] at this
      rw [← this]; abel
    have hm1 := hd.UBmem v
    have hm2 := S_pair hL hr hr2 c.hq c.hSA hlam' φ
    have hG := c.hSA.eq
    have hdiff := graph_add hG hm1 (graph_smul hG (-1 : ℂ) hm2)
    simp only [Prod.smul_mk, Prod.mk_add_mk] at hdiff
    have e1 : lam • (U v - Sred L κ (u : ℝ → ℂ) n r lam φ) - φ =
        U (B v) + (-1 : ℂ) • (lam • Sred L κ (u : ℝ → ℂ) n r lam φ + φ - PP φ) := by
      rw [hUBv]; module
    have e0 : U v - Sred L κ (u : ℝ → ℂ) n r lam φ = U v + (-1 : ℂ) • Sred L κ (u : ℝ → ℂ) n r lam φ := by
      module
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    rw [← hv, e1, e0]
    exact hdiff
  · rintro ⟨f, g⟩ hp
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    have hSg := S_graph hr hr2 c.hq hlam' hp
    have hUg := hd.UsG hp
    have hSφ : Sred L κ (u : ℝ → ℂ) n r lam (lam • f - g) = PP f - f := by
      rw [map_sub, map_smul, hSg]; abel
    have hUφ : ContinuousLinearMap.adjoint U (lam • f - g) = A (ContinuousLinearMap.adjoint U f) := by
      rw [map_sub, map_smul, hUg, hAv]
    rw [hSφ, hUφ, hTA, hd.UUs]
    abel

end Main

end QuantumNLS.Local003Spectrum
#print axioms QuantumNLS.Local003Spectrum.scalar_core
#print axioms QuantumNLS.Local003Spectrum.S_graph
#print axioms QuantumNLS.Local003Spectrum.S_pair
#print axioms QuantumNLS.Local003Spectrum.uData
#print axioms QuantumNLS.Local003Spectrum.spectrum_resolvent
