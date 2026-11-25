import Mathlib
import QuantumNLS.RB01SpecForm
import QuantumNLS.RB01RootCount

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-25: the eigenvalue correspondence between `𝓛_u` near `p_n`
and RB01Matrix's `B_n`, and the identification `α_n = a_n − p_n`, `τ_n = |b_n|²` (source
`collective_actions.tex:375-386`: "For real fields the boundary determinant criterion and self-adjointness identify
these zeros with the eigenvalues of the rank-two restriction.  If they are distinct, each is simple ... and must
occur in that restriction.  If they coalesce, the restriction has no other possible eigenvalue, and its two
eigenvalues coincide.  Hence `α_n = a_n − p_n`, `τ_n = b_n b_n^♯` on the real slice").

Square-small labels, `S = E^*PE` with `‖S − 1‖ < 1`, `B = S^{-1/2}(E^*DE)S^{-1/2}` (`RB01SpecForm.Bmat`):
* `range_PE` (`PE : ℂ² → ran P` is onto: injective since `E^*PE = S` is, and `rank P = 2`);
* `eigen_inside'`: an eigenvector in `ran P` has its eigenvalue strictly inside the contour;
* **`matrix_of_graph'`**: an eigenvector of `𝓛_u` with `|λ − p_n| < r` gives `B w = (λ − p_n) w`, `w ≠ 0`
  (uses `D P = D`, RB01SpecIdem);
* **`graph_of_matrix'`**: `B w = μ w`, `w ≠ 0` gives an eigenvector of `𝓛_u` with eigenvalue `p_n + μ`, `|μ| < r`
  (uses `P D = D`, `pair_mem'`);
* `doublet_eig`, `doublet_vec`: the eigenvalues of `[[a, b̄],[b, a]]` are exactly `a ± |b|`;
* **`ident`**: with the RB01RootCount data at a label (zeros of `f_n` in `|w| ≤ 4d` are exactly `b^± − p_n`) and
  `|Δ + 2(−1)^n| ≥ 1` (RB01RootPrep), contour radius `r = d`: `α_n = a`, `τ_n = |b|²` where `B_n − p_n = [[a, b̄],[b, a]]`
  (via the boundary determinant criterion `RB01Det.eigen_iff_disc`). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace QuantumNLS.RB01SpecEig

open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local002Circle
  QuantumNLS.Local003InvSqrt QuantumNLS.LocalSpectral.Round23
open QuantumNLS.RB01Resolvent (SqSmall resolvent_exists idem_of_sqSmall rank_two_of_sqSmall)
open QuantumNLS.RB01SpecForm (Kmat Bmat hres res_isRes' eigen_P' eigen_D' pair_mem' res_eig P_apply' Bmat_form)

/-! ## The doublet matrix -/

theorem doublet_eig {B : E2 →L[ℂ] E2} {a : ℝ} {b : ℂ}
    (hB : ∀ v : E2, B v = vec2 ((a : ℂ) * v 0 + conj b * v 1) (b * v 0 + (a : ℂ) * v 1))
    {w : E2} (hw : w ≠ 0) {μ : ℂ} (hμ : B w = μ • w) :
    μ = ((a + ‖b‖ : ℝ) : ℂ) ∨ μ = ((a - ‖b‖ : ℝ) : ℂ) := by
  have h0 := congrArg (fun v : E2 => v 0) hμ
  have h1 := congrArg (fun v : E2 => v 1) hμ
  simp only [hB, vec2_zero, vec2_one, PiLp.smul_apply, smul_eq_mul] at h0 h1
  have hbb : conj b * b = ((‖b‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have e0 : ((μ - a) ^ 2 - ((‖b‖ : ℝ) : ℂ) ^ 2) * w 0 = 0 := by
    rw [← hbb]; linear_combination (-(μ - a)) * h0 + (-(conj b)) * h1
  have e1 : ((μ - a) ^ 2 - ((‖b‖ : ℝ) : ℂ) ^ 2) * w 1 = 0 := by
    rw [← hbb]; linear_combination (-(μ - a)) * h1 + (-b) * h0
  have hq : (μ - a) ^ 2 - ((‖b‖ : ℝ) : ℂ) ^ 2 = 0 := by
    by_contra hne
    apply hw
    have z0 := (mul_eq_zero.1 e0).resolve_left hne
    have z1 := (mul_eq_zero.1 e1).resolve_left hne
    ext i; fin_cases i
    · exact z0
    · exact z1
  have hf : (μ - ((a + ‖b‖ : ℝ) : ℂ)) * (μ - ((a - ‖b‖ : ℝ) : ℂ)) = 0 := by
    push_cast; linear_combination hq
  rcases mul_eq_zero.1 hf with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

theorem doublet_vec {B : E2 →L[ℂ] E2} {a : ℝ} {b : ℂ}
    (hB : ∀ v : E2, B v = vec2 ((a : ℂ) * v 0 + conj b * v 1) (b * v 0 + (a : ℂ) * v 1))
    {s : ℝ} (hs : s = 1 ∨ s = -1) : ∃ w : E2, w ≠ 0 ∧ B w = ((a + s * ‖b‖ : ℝ) : ℂ) • w := by
  have hs2 : (s : ℂ) ^ 2 = 1 := by rcases hs with h | h <;> simp [h]
  have hbb : b * conj b = ((‖b‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  by_cases hb : b = 0
  · refine ⟨vec2 1 0, fun h => by simpa [vec2] using congrArg (fun v : E2 => v 0) h, ?_⟩
    rw [hB]
    ext i; fin_cases i <;> simp [vec2, hb]
  · refine ⟨vec2 (conj b) ((s * ‖b‖ : ℝ) : ℂ), fun h => ?_, ?_⟩
    · have := congrArg (fun v : E2 => v 0) h
      simp only [vec2_zero] at this
      exact hb (by simpa using congrArg conj this)
    · rw [hB]
      ext i; fin_cases i
      · simp only [vec2_zero, vec2_one, Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
        push_cast; ring
      · simp only [vec2_zero, vec2_one, Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
        push_cast
        linear_combination hbb - (((‖b‖ : ℝ) : ℂ) ^ 2) * hs2

/-! ## The eigenvalue correspondence -/

variable {L κ r : ℝ} {n : ℤ} {u : Lp ℂ 2 (μI L)}

section Corr

variable (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hu : SqSmall L κ r n u)
  (hS : ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ < 1)
include hL hr hr2 hu hS

theorem S_inj {v : E2} (h : compressionMatrix L κ (u : ℝ → ℂ) n r v = 0) : v = 0 := by
  set S := compressionMatrix L κ (u : ℝ → ℂ) n r
  set I := invSqrtM S
  have h1 : I * S * I = 1 := invSqrtM_mul_mul hS
  have hc : I * S = S * I := (invSqrtM_commute hS).eq
  have h2 : I * I * S = 1 := by rw [mul_assoc, hc, ← mul_assoc]; exact h1
  have e : (I * I * S) v = v := by rw [h2]; rfl
  have e' : (I * I) (S v) = v := e
  rw [h, map_zero] at e'
  exact e'.symm

theorem range_PE {f : H2 L} (hf : perturbedProj L κ (u : ℝ → ℂ) n r f = f) :
    ∃ v : E2, perturbedProj L κ (u : ℝ → ℂ) n r (embed L n v) = f := by
  set P := perturbedProj L κ (u : ℝ → ℂ) n r
  let T : E2 →ₗ[ℂ] H2 L := ((P ∘L embed L n : E2 →L[ℂ] H2 L) : E2 →ₗ[ℂ] H2 L)
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun v hv => ?_
    apply S_inj hL hr hr2 hu hS
    change (ContinuousLinearMap.adjoint (embed L n)) (P (embed L n v)) = 0
    have : P (embed L n v) = 0 := hv
    rw [this, map_zero]
  have hrank := rank_two_of_sqSmall hL hr hr2 hu
  have hfd : FiniteDimensional ℂ (LinearMap.range (P : H2 L →ₗ[ℂ] H2 L)) := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  have hle : LinearMap.range T ≤ LinearMap.range (P : H2 L →ₗ[ℂ] H2 L) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨embed L n v, rfl⟩
  have hfin : Module.finrank ℂ (LinearMap.range T) = Module.finrank ℂ (LinearMap.range (P : H2 L →ₗ[ℂ] H2 L)) := by
    rw [LinearMap.finrank_range_of_inj hinj, hrank, finrank_euclideanSpace_fin]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  have hfm : f ∈ LinearMap.range (P : H2 L →ₗ[ℂ] H2 L) := LinearMap.mem_range.2 ⟨f, hf⟩
  rw [← heq] at hfm
  obtain ⟨v, hv⟩ := hfm
  exact ⟨v, hv⟩

/-- An eigenvector in `ran P` has its eigenvalue strictly inside the contour. -/
theorem eigen_inside' {f : H2 L} {lam : ℂ} (hf : (f, lam • f) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n))
    (hPf : perturbedProj L κ (u : ℝ → ℂ) n r f = f) (hf0 : f ≠ 0) : ‖lam - center L n‖ < r := by
  by_contra hcon
  push_neg at hcon
  rcases hcon.lt_or_eq with hlt | heq
  · have hne : ∀ z ∈ sphere (center L n) r, z - lam ≠ 0 := by
      intro z hz h0
      rw [sub_eq_zero] at h0
      rw [h0, mem_sphere_iff_norm] at hz
      linarith
    have hpt : ∀ z ∈ sphere (center L n) r,
        resolvent L κ (u : ℝ → ℂ) (parity n) z f = (z - lam)⁻¹ • f := by
      intro z hz
      have := (res_isRes' hL hr hr2 hu hz).2 (f, lam • f) hf
      simp only at this
      rw [← sub_smul, map_smul] at this
      calc resolvent L κ (u : ℝ → ℂ) (parity n) z f
          = (z - lam)⁻¹ • ((z - lam) • resolvent L κ (u : ℝ → ℂ) (parity n) z f) := by
            rw [smul_smul, inv_mul_cancel₀ (hne z hz), one_smul]
        _ = (z - lam)⁻¹ • f := by rw [this]
    have h0 := QuantumNLS.Local002Idem.scalar_inv_zero (c := center L n) hr hlt
    apply hf0
    rw [← hPf, P_apply' hL hr hr2 hu, circleIntegral.integral_congr hr.le hpt,
      circleIntegral.integral_smul_const, h0, zero_smul, smul_zero]
  · have hz : lam ∈ sphere (center L n) r := by rw [mem_sphere_iff_norm]; exact heq.symm
    obtain ⟨R, hR, -⟩ := hres hL hr hr2 hu lam hz
    have := hR.2 (f, lam • f) hf
    simp only [sub_self, map_zero] at this
    exact hf0 this.symm

/-- **Operator eigenvector ⇒ matrix eigenvector.** -/
theorem matrix_of_graph' {f : H2 L} {lam : ℂ} (hf : (f, lam • f) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n))
    (hf0 : f ≠ 0) (hlam : ‖lam - center L n‖ < r) :
    ∃ w : E2, w ≠ 0 ∧ Bmat L κ (u : ℝ → ℂ) n r w = (lam - center L n) • w := by
  set P := perturbedProj L κ (u : ℝ → ℂ) n r with hPdef
  set D := dressedIntegral L κ (u : ℝ → ℂ) n r with hDdef
  set S := compressionMatrix L κ (u : ℝ → ℂ) n r with hSdef
  set I := invSqrtM S with hIdef
  have hPf := eigen_P' hL hr hr2 hu hf hlam
  have hDf := eigen_D' hL hr hr2 hu hf hlam
  obtain ⟨v, hv⟩ := range_PE hL hr hr2 hu hS hPf
  have hDP := (QuantumNLS.RB01SpecIdem.dressed_proj hL hr hr2 hu).1
  have hKv : Kmat L κ (u : ℝ → ℂ) n r v = (lam - center L n) • S v := by
    change (ContinuousLinearMap.adjoint (embed L n)) (D (embed L n v)) =
      (lam - center L n) • (ContinuousLinearMap.adjoint (embed L n)) (P (embed L n v))
    have h1 : D (P (embed L n v)) = D (embed L n v) :=
      congrArg (fun T : H2 L →L[ℂ] H2 L => T (embed L n v)) hDP
    rw [← h1, hv, hDf, map_smul]
  have hc : I * S = S * I := (invSqrtM_commute hS).eq
  have h1 : I * S * I = 1 := invSqrtM_mul_mul hS
  have hISI : I (S (I v)) = v := by
    have e : (I * S * I) v = v := by rw [h1]; rfl
    exact e
  refine ⟨S (I v), fun h0 => ?_, ?_⟩
  · have hv0 : v = 0 := by rw [← hISI, h0, map_zero]
    apply hf0
    rw [← hv, hv0, map_zero, map_zero]
  · change I (Kmat L κ (u : ℝ → ℂ) n r (I (S (I v)))) = (lam - center L n) • S (I v)
    rw [hISI, hKv, map_smul]
    congr 1
    exact congrArg (fun T : E2 →L[ℂ] E2 => T v) hc

/-- **Matrix eigenvector ⇒ operator eigenvector**, with the eigenvalue inside the contour. -/
theorem graph_of_matrix' {w : E2} (hw : w ≠ 0) {μ : ℂ} (hμ : Bmat L κ (u : ℝ → ℂ) n r w = μ • w) :
    (∃ f : H2 L, f ≠ 0 ∧ (f, (center L n + μ) • f) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n)) ∧ ‖μ‖ < r := by
  set P := perturbedProj L κ (u : ℝ → ℂ) n r with hPdef
  set D := dressedIntegral L κ (u : ℝ → ℂ) n r with hDdef
  set S := compressionMatrix L κ (u : ℝ → ℂ) n r with hSdef
  set I := invSqrtM S with hIdef
  set E := embed L n with hEdef
  have hPD := (QuantumNLS.RB01SpecIdem.dressed_proj hL hr hr2 hu).2
  have hP2 := idem_of_sqSmall hL hr hr2 hu
  have h1 : I * S * I = 1 := invSqrtM_mul_mul hS
  have hc : I * S = S * I := (invSqrtM_commute hS).eq
  have hSII : S * I * I = 1 := by rw [← hc]; exact h1
  set v := I w with hvdef
  have hKv : Kmat L κ (u : ℝ → ℂ) n r v = μ • S v := by
    have hB : I (Kmat L κ (u : ℝ → ℂ) n r v) = μ • w := hμ
    have e1 : (S * I * I) (Kmat L κ (u : ℝ → ℂ) n r v) = Kmat L κ (u : ℝ → ℂ) n r v := by rw [hSII]; rfl
    have e2 : (S * I * I) (Kmat L κ (u : ℝ → ℂ) n r v) = S (I (I (Kmat L κ (u : ℝ → ℂ) n r v))) := rfl
    rw [← e1, e2, hB, map_smul, map_smul]
  have hy : D (E v) = μ • P (E v) := by
    set y := D (E v) - μ • P (E v) with hydef
    have hPy : P y = y := by
      rw [hydef, map_sub, map_smul]
      have a1 : P (D (E v)) = D (E v) := congrArg (fun T : H2 L →L[ℂ] H2 L => T (E v)) hPD
      have a2 : P (P (E v)) = P (E v) := congrArg (fun T : H2 L →L[ℂ] H2 L => T (E v)) hP2
      rw [a1, a2]
    have hEy : (ContinuousLinearMap.adjoint E) y = 0 := by
      have hk : (ContinuousLinearMap.adjoint E) (D (E v)) = μ • (ContinuousLinearMap.adjoint E) (P (E v)) := hKv
      rw [hydef, map_sub, map_smul, hk, sub_self]
    obtain ⟨v', hv'⟩ := range_PE hL hr hr2 hu hS hPy
    have hS0 : S v' = 0 := by
      change (ContinuousLinearMap.adjoint E) (P (E v')) = 0
      rw [hv', hEy]
    have hv0 := S_inj hL hr hr2 hu hS hS0
    have hy0 : y = 0 := by rw [← hv', hv0, map_zero, map_zero]
    exact sub_eq_zero.1 hy0
  have hf0 : P (E v) ≠ 0 := by
    intro h0
    have hS0 : S v = 0 := by
      change (ContinuousLinearMap.adjoint E) (P (E v)) = 0
      rw [h0, map_zero]
    have hv0 := S_inj hL hr hr2 hu hS hS0
    apply hw
    have e : (S * I * I) w = w := by rw [hSII]; rfl
    have e2 : (S * I * I) w = S (I v) := rfl
    rw [← e, e2, hv0, map_zero, map_zero]
  have hgraph := pair_mem' hL hr hr2 hu (E v)
  have hPPf : P (P (E v)) = P (E v) := congrArg (fun T : H2 L →L[ℂ] H2 L => T (E v)) hP2
  have hpair : (P (E v), (center L n + μ) • P (E v)) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n) := by
    have e : D (E v) + (pm L n : ℂ) • P (E v) = (center L n + μ) • P (E v) := by
      rw [hy, add_smul, add_comm]; rfl
    rw [← e]; exact hgraph
  refine ⟨⟨P (E v), hf0, hpair⟩, ?_⟩
  have := eigen_inside' hL hr hr2 hu hS hpair hPPf hf0
  simpa using this

end Corr

/-! ## The identification `α_n = a_n − p_n`, `τ_n = |b_n|²` -/

theorem parity_cast (n : ℤ) : (((parity n : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ n := by
  unfold parity
  by_cases h : Even n
  · simp [h, h.neg_one_zpow]
  · have ho : Odd n := Int.not_even_iff_odd.1 h
    simp [h, ho.neg_one_zpow]

theorem dd_lt [Fact (0 < L)] : QuantumNLS.RB01RootPrep.dd L < 2 * Real.pi / L := by
  have hL : 0 < L := Fact.out
  have h1 : 0 < 1 / L := by positivity
  have e1 : QuantumNLS.RB01RootPrep.dd L = 1 / 4 * (1 / L) := by unfold QuantumNLS.RB01RootPrep.dd; field_simp
  have e2 : 2 * Real.pi / L = 2 * Real.pi * (1 / L) := by ring
  rw [e1, e2]
  nlinarith [Real.pi_gt_three]

open QuantumNLS.RB01RootPrep (fn dd dd_pos) in
open QuantumNLS.RB01RootCount (bm bp alpha tau) in
/-- **Identification** (source :375-386): with contour radius `r = d`, at a label where the RB01RootCount zero data
and the RB01RootPrep sign bound hold, `B_n − p_n = [[a, b̄],[b, a]]` with `a = α_n`, `|b|² = τ_n`. -/
theorem ident [Fact (0 < L)] (hκ : 0 < κ) (v : QuantumNLS.PhysicalTensor.L2T L) (n : ℤ)
    (hu : SqSmall L κ (dd L) n (QuantumNLS.Local002Bridge.toInterval L v))
    (hS : ‖compressionMatrix L κ (circleRep v) n (dd L) - 1‖ < 1)
    (hz : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L → (fn κ v n w = 0 ↔
      w = ((bm hκ v n - pm L n : ℝ) : ℂ) ∨ w = ((bp hκ v n - pm L n : ℝ) : ℂ)))
    (hb1 : |bm hκ v n - pm L n| < dd L / 8) (hb2 : |bp hκ v n - pm L n| < dd L / 8)
    (hΔ : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L →
      1 ≤ ‖QuantumNLS.L2SpatialTransfer.discriminant κ v ((pm L n : ℂ) + w) + 2 * (-1 : ℂ) ^ n‖) :
    ∃ (a : ℝ) (b : ℂ), (∀ w : E2, Bmat L κ (circleRep v) n (dd L) w =
        vec2 ((a : ℂ) * w 0 + conj b * w 1) (b * w 0 + (a : ℂ) * w 1)) ∧
      alpha hκ v n = a ∧ tau hκ v n = ‖b‖ ^ 2 := by
  have hL : 0 < L := Fact.out
  have hd := dd_pos (L := L)
  have hr2 := dd_lt (L := L)
  set u := QuantumNLS.Local002Bridge.toInterval L v with hudef
  have e := QuantumNLS.Local002Bridge.toInterval_coe L v
  have hSeq : compressionMatrix L κ (circleRep v) n (dd L) = compressionMatrix L κ (u : ℝ → ℂ) n (dd L) :=
    (QuantumNLS.RB01Bridge.compressionMatrix_congr (κ := κ) e n (dd L)).symm
  have hDeq : dressedIntegral L κ (circleRep v) n (dd L) = dressedIntegral L κ (u : ℝ → ℂ) n (dd L) :=
    (QuantumNLS.RB01Bridge.dressedIntegral_congr (κ := κ) e n (dd L)).symm
  have hBeq : Bmat L κ (circleRep v) n (dd L) = Bmat L κ (u : ℝ → ℂ) n (dd L) := by
    unfold Bmat Kmat; rw [hSeq, hDeq]
  have hGeq : LuGraph L κ (circleRep v) (parity n) = LuGraph L κ (u : ℝ → ℂ) (parity n) :=
    (QuantumNLS.Local002Bridge.LuGraph_congr e (parity n)).symm
  have hS' : ‖compressionMatrix L κ (u : ℝ → ℂ) n (dd L) - 1‖ < 1 := by rwa [← hSeq]
  obtain ⟨a, b, hab⟩ := Bmat_form hL hd hr2 hu hS'
  have hab' : ∀ w : E2, Bmat L κ (u : ℝ → ℂ) n (dd L) w =
      vec2 ((a : ℂ) * w 0 + conj b * w 1) (b * w 0 + (a : ℂ) * w 1) := hab
  set σ : ℂ := (((parity n : ℤˣ) : ℤ) : ℂ) with hσdef
  have hσ : σ = (-1 : ℂ) ^ n := parity_cast n
  have hσ2 : σ ^ 2 = 1 := QuantumNLS.RB01Det.sigma_sq (parity n)
  have hcen : center L n = (pm L n : ℂ) := rfl
  -- zeros ⇒ matrix eigenvalues
  have zero_to_eig : ∀ β : ℝ, |β| < dd L / 8 → fn κ v n (β : ℂ) = 0 →
      ((β : ℂ) = ((a + ‖b‖ : ℝ) : ℂ) ∨ (β : ℂ) = ((a - ‖b‖ : ℝ) : ℂ)) := by
    intro β hβ hz0
    have hβn : ‖(β : ℂ)‖ ≤ 4 * dd L := by
      rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have hne := hΔ (β : ℂ) hβn
    have hdisc : QuantumNLS.L2SpatialTransfer.discriminant κ v ((pm L n : ℂ) + β) = 2 * σ := by
      have hz1 : (QuantumNLS.L2SpatialTransfer.discriminant κ v ((pm L n : ℂ) + β) - 2 * σ) *
          (QuantumNLS.L2SpatialTransfer.discriminant κ v ((pm L n : ℂ) + β) + 2 * σ) = 0 := by
        have : fn κ v n (β : ℂ) = 0 := hz0
        unfold fn at this
        linear_combination this - 4 * hσ2
      have hnz : QuantumNLS.L2SpatialTransfer.discriminant κ v ((pm L n : ℂ) + β) + 2 * σ ≠ 0 := by
        intro h0; rw [hσ] at h0; rw [h0, norm_zero] at hne; linarith
      exact sub_eq_zero.1 ((mul_eq_zero.1 hz1).resolve_right hnz)
    obtain ⟨f, hf0, hf⟩ := (QuantumNLS.RB01Det.eigen_iff_disc κ v (parity n) ((pm L n : ℂ) + β)).2 hdisc
    rw [hGeq] at hf
    have hlam : ‖((pm L n : ℂ) + β) - center L n‖ < dd L := by
      rw [hcen, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]; linarith
    obtain ⟨w, hw0, hw⟩ := matrix_of_graph' hL hd hr2 hu hS' hf hf0 hlam
    rw [hcen, add_sub_cancel_left] at hw
    exact doublet_eig hab' hw0 hw
  -- matrix eigenvalues ⇒ zeros
  have eig_to_zero : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      (((a + s * ‖b‖ : ℝ) : ℂ) = ((bm hκ v n - pm L n : ℝ) : ℂ) ∨
        ((a + s * ‖b‖ : ℝ) : ℂ) = ((bp hκ v n - pm L n : ℝ) : ℂ)) := by
    intro s hs
    obtain ⟨w, hw0, hw⟩ := doublet_vec hab' hs
    obtain ⟨⟨f, hf0, hf⟩, hμ⟩ := graph_of_matrix' hL hd hr2 hu hS' hw0 hw
    rw [← hGeq] at hf
    have hdisc := (QuantumNLS.RB01Det.eigen_iff_disc κ v (parity n) _).1 ⟨f, hf0, hf⟩
    have hzero : fn κ v n ((a + s * ‖b‖ : ℝ) : ℂ) = 0 := by
      unfold fn
      rw [← hcen, hdisc]
      linear_combination 4 * hσ2
    exact (hz _ (by linarith)).1 hzero
  refine ⟨a, b, fun w => by rw [hBeq]; exact hab' w, ?_⟩
  set β₁ := bm hκ v n - pm L n with hβ1
  set β₂ := bp hκ v n - pm L n with hβ2
  set t := ‖b‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hz1 : fn κ v n (β₁ : ℂ) = 0 := (hz _ (by rw [Complex.norm_real, Real.norm_eq_abs]; linarith)).2 (Or.inl rfl)
  have hz2 : fn κ v n (β₂ : ℂ) = 0 := (hz _ (by rw [Complex.norm_real, Real.norm_eq_abs]; linarith)).2 (Or.inr rfl)
  have c1 := zero_to_eig β₁ hb1 hz1
  have c2 := zero_to_eig β₂ hb2 hz2
  have c3 := eig_to_zero 1 (Or.inl rfl)
  have c4 := eig_to_zero (-1) (Or.inr rfl)
  simp only [Complex.ofReal_inj] at c1 c2 c3 c4
  have ha : alpha hκ v n = (β₁ + β₂) / 2 := by
    simp only [alpha, hβ1, hβ2]; ring
  have htau : tau hκ v n = ((β₂ - β₁) / 2) ^ 2 := by
    simp only [tau, hβ1, hβ2]; ring
  rw [ha, htau]
  rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;> rcases c3 with c3 | c3 <;>
    rcases c4 with c4 | c4 <;> constructor <;> nlinarith

end QuantumNLS.RB01SpecEig

#print axioms QuantumNLS.RB01SpecEig.doublet_eig
#print axioms QuantumNLS.RB01SpecEig.matrix_of_graph'
#print axioms QuantumNLS.RB01SpecEig.graph_of_matrix'
#print axioms QuantumNLS.RB01SpecEig.ident
