import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local002Hyp
import QuantumNLS.Local002Basis

/-! LOCAL-002, stage D: free spectral facts from the proved ONB `{χ_{m,j}}` (`Local002Basis`).

For an `IsResolvent` `R` of `𝓛_0` on `D_{(-1)^n}` at `z` (not a free eigenvalue), `R χ_{m,j} = (z-p_m)⁻¹ χ_{m,j}`;
`R(z)^† = R(z̄)` for non-real `z`; `𝓛_0` is symmetric; and `P_n(0) = E E^†` for `E = (χ_{n,1}, χ_{n,2})`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local002Free
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Basis

variable {L κ : ℝ}

/-- The free eigenfunctions of the parity sector of `n`. -/
def chiSet (L : ℝ) (n : ℤ) : Set (H2 L) := {v | ∃ m j, parity m = parity n ∧ v = chi L m j}

lemma dense_span_chi (hL : 0 < L) (n : ℤ) : Dense (Submodule.span ℂ (chiSet L n) : Set (H2 L)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro f hf
  apply chi_complete hL n f
  intro m j hm
  exact (Submodule.mem_orthogonal _ _).1 hf _ (Submodule.subset_span ⟨m, j, hm, rfl⟩)

lemma res_chi (hL : 0 < L) {n m : ℤ} (j : Fin 2) {z : ℂ} {R : H2 L →L[ℂ] H2 L}
    (hR : IsResolvent L κ (fun _ => 0) (parity n) z R) (hm : parity m = parity n)
    (hz : z ≠ (pm L m : ℂ)) : R (chi L m j) = ((z - (pm L m : ℂ))⁻¹ : ℂ) • chi L m j := by
  have hE := free_eigen hL κ m j
  rw [hm] at hE
  have h := hR.2 (chi L m j, (pm L m : ℂ) • chi L m j) hE
  simp only at h
  rw [← sub_smul, map_smul] at h
  have hne : z - (pm L m : ℂ) ≠ 0 := sub_ne_zero.2 hz
  calc R (chi L m j) = ((z - (pm L m : ℂ))⁻¹ : ℂ) • ((z - (pm L m : ℂ)) • R (chi L m j)) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = _ := by rw [h]

lemma ne_pm_of_im {z : ℂ} (hz : z.im ≠ 0) (L : ℝ) (m : ℤ) : z ≠ (pm L m : ℂ) := by
  intro h
  apply hz
  rw [h]; simp

lemma R_adjoint (hL : 0 < L) {n : ℤ} {z : ℂ} (hz : z.im ≠ 0) {R R' : H2 L →L[ℂ] H2 L}
    (hR : IsResolvent L κ (fun _ => 0) (parity n) z R)
    (hR' : IsResolvent L κ (fun _ => 0) (parity n) (conj z) R') :
    ContinuousLinearMap.adjoint R = R' := by
  have hz' : (conj z).im ≠ 0 := by simpa using hz
  apply ContinuousLinearMap.ext_on (dense_span_chi hL n)
  rintro v ⟨b, j, hb, rfl⟩
  have h0 : ContinuousLinearMap.adjoint R (chi L b j) - R' (chi L b j) = 0 := by
    apply chi_complete hL n
    intro a i ha
    rw [inner_sub_right, ContinuousLinearMap.adjoint_inner_right,
      res_chi hL i hR ha (ne_pm_of_im hz L a), res_chi hL j hR' hb (ne_pm_of_im hz' L b),
      inner_smul_left, inner_smul_right, inner_chi_general hL (ha.trans hb.symm)]
    by_cases hab : a = b ∧ i = j
    · obtain ⟨rfl, rfl⟩ := hab
      simp [map_inv₀, map_sub, Complex.conj_ofReal]
    · simp [hab]
  exact sub_eq_zero.mp h0

lemma free_symm (hL : 0 < L) {n : ℤ} {z : ℂ} (hz : z.im ≠ 0) {R R' : H2 L →L[ℂ] H2 L}
    (hR : IsResolvent L κ (fun _ => 0) (parity n) z R)
    (hR' : IsResolvent L κ (fun _ => 0) (parity n) (conj z) R')
    {p q : H2 L × H2 L} (hp : p ∈ LuGraph L κ (fun _ => 0) (parity n))
    (hq : q ∈ LuGraph L κ (fun _ => 0) (parity n)) : ⟪p.1, q.2⟫_ℂ = ⟪p.2, q.1⟫_ℂ := by
  have hadj := R_adjoint hL hz hR hR'
  have h1 : R (z • p.1 - p.2) = p.1 := hR.2 p hp
  have h2 : R' (conj z • q.1 - q.2) = q.1 := hR'.2 q hq
  obtain ⟨f', hf'⟩ : ∃ f', f' = z • p.1 - p.2 := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g', g' = conj z • q.1 - q.2 := ⟨_, rfl⟩
  rw [← hf'] at h1
  rw [← hg'] at h2
  have e1 : q.2 = conj z • q.1 - g' := by rw [hg']; abel
  have e2 : p.2 = z • p.1 - f' := by rw [hf']; abel
  have h3 : ⟪f', q.1⟫_ℂ = ⟪p.1, g'⟫_ℂ := by
    calc ⟪f', q.1⟫_ℂ = ⟪f', R' g'⟫_ℂ := by rw [h2]
      _ = ⟪f', ContinuousLinearMap.adjoint R g'⟫_ℂ := by rw [hadj]
      _ = ⟪R f', g'⟫_ℂ := ContinuousLinearMap.adjoint_inner_right R f' g'
      _ = ⟪p.1, g'⟫_ℂ := by rw [h1]
  have k1 : ⟪p.1, q.2⟫_ℂ = conj z * ⟪p.1, q.1⟫_ℂ - ⟪p.1, g'⟫_ℂ := by
    conv_lhs => rw [e1]
    rw [inner_sub_right, inner_smul_right]
  have k2 : ⟪p.2, q.1⟫_ℂ = conj z * ⟪p.1, q.1⟫_ℂ - ⟪f', q.1⟫_ℂ := by
    conv_lhs => rw [e2]
    rw [inner_sub_left, inner_smul_left]
  rw [k1, k2, h3]

/-! ### The free Riesz projection -/

lemma circleIntegral_apply {c : ℂ} {r : ℝ} (F : ℂ → H2 L →L[ℂ] H2 L) (hF : CircleIntegrable F c r)
    (v : H2 L) : (∮ z in C(c, r), F z) v = ∮ z in C(c, r), F z v := by
  unfold circleIntegral
  have := (ContinuousLinearMap.apply ℂ (H2 L) v).intervalIntegral_comp_comm hF.out
  simp only [ContinuousLinearMap.apply_apply] at this
  show (∫ θ in (0 : ℝ)..2 * Real.pi, deriv (circleMap c r) θ • F (circleMap c r θ)) v =
    ∫ θ in (0 : ℝ)..2 * Real.pi, deriv (circleMap c r) θ • (F (circleMap c r θ) v)
  rw [← this]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp

lemma EEadj_chi (hL : 0 < L) {n m : ℤ} (hm : parity m = parity n) (j : Fin 2) :
    embed L n (ContinuousLinearMap.adjoint (embed L n) (chi L m j)) =
      if m = n then chi L n j else 0 := by
  have hu : ∀ i : Fin 2, (ContinuousLinearMap.adjoint (embed L n) (chi L m j)) i =
      ⟪chi L n i, chi L m j⟫_ℂ := by
    intro i
    have h1 : (ContinuousLinearMap.adjoint (embed L n) (chi L m j)) i =
        ⟪EuclideanSpace.single i (1 : ℂ), ContinuousLinearMap.adjoint (embed L n) (chi L m j)⟫_ℂ := by
      simp [EuclideanSpace.inner_single_left]
    rw [h1, ContinuousLinearMap.adjoint_inner_right]
    congr 1
    rw [embed_apply]
    fin_cases i <;> simp
  rw [embed_apply, hu 0, hu 1, inner_chi_general hL hm.symm, inner_chi_general hL hm.symm]
  by_cases hmn : m = n
  · subst hmn
    fin_cases j <;> simp
  · have : ¬ n = m := fun h => hmn h.symm
    simp [hmn, this]

lemma far_pm (hL : 0 < L) {m n : ℤ} (hm : parity m = parity n) (hmn : m ≠ n) {r : ℝ}
    (hr2 : r < 2 * Real.pi / L) : r < ‖(pm L m : ℂ) - (pm L n : ℂ)‖ := by
  obtain ⟨k, hk⟩ := parity_eq_iff_even hm.symm
  have hk0 : k ≠ 0 := by
    rintro rfl; apply hmn; omega
  have h1 : (pm L m : ℂ) - (pm L n : ℂ) = ((2 * Real.pi * ((m : ℝ) - n) / L : ℝ) : ℂ) := by
    unfold pm; push_cast; ring
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hL,
    abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have hmn' : (2 : ℝ) ≤ |(m : ℝ) - n| := by
    have : (m : ℝ) - n = 2 * k := by exact_mod_cast (by omega : m - n = 2 * k)
    rw [this, abs_mul]
    have : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      exact_mod_cast this
    norm_num
    linarith
  calc r < 2 * Real.pi / L := hr2
    _ ≤ 2 * Real.pi * |(m : ℝ) - n| / L := by
      rw [div_le_div_iff_of_pos_right hL]
      nlinarith [Real.pi_pos]

theorem freeProj_eq (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (hres : ∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r → ∃ R : H2 L →L[ℂ] H2 L,
      IsResolvent L κ (fun _ => 0) (parity n) z R ∧ ‖R‖ ≤ 1 / r) :
    freeProj L κ n r = embed L n ∘L ContinuousLinearMap.adjoint (embed L n) := by
  have hsph : ∀ z ∈ sphere (QuantumNLS.LocalSpectral.center L n) r, ‖z - (pm L n : ℂ)‖ = r := fun z hz => by
    simpa [QuantumNLS.LocalSpectral.center, mem_sphere_iff_norm] using hz
  have hRf : ∀ z ∈ sphere (QuantumNLS.LocalSpectral.center L n) r,
      IsResolvent L κ (fun _ => 0) (parity n) z (resolvent L κ (fun _ => 0) (parity n) z) ∧
        ‖resolvent L κ (fun _ => 0) (parity n) z‖ ≤ 1 / r := fun z hz => by
    obtain ⟨R, hR, hn⟩ := hres z (hsph z hz)
    rw [resolvent_eq hR]; exact ⟨hR, hn⟩
  have hcont : ContinuousOn (fun z => resolvent L κ (fun _ => 0) (parity n) z)
      (sphere (QuantumNLS.LocalSpectral.center L n) r) :=
    continuousOn_resolvent _ (M := 1 / r) (by positivity)
      (fun z hz => ⟨_, (hRf z hz).1, (hRf z hz).2⟩)
  have hint := hcont.circleIntegrable hr.le
  apply ContinuousLinearMap.ext_on (dense_span_chi hL n)
  rintro v ⟨m, j, hm, rfl⟩
  show freeProj L κ n r (chi L m j) = (embed L n ∘L ContinuousLinearMap.adjoint (embed L n)) (chi L m j)
  rw [ContinuousLinearMap.comp_apply, EEadj_chi hL hm]
  unfold freeProj rieszProj
  rw [ContinuousLinearMap.smul_apply, circleIntegral_apply _ hint]
  have hz_ne : ∀ z ∈ sphere (QuantumNLS.LocalSpectral.center L n) r, z ≠ (pm L m : ℂ) := fun z hz hzm => by
    by_cases hmn : m = n
    · subst hmn
      have := hsph z hz
      rw [hzm, sub_self, norm_zero] at this
      exact hr.ne this
    · have h1 := far_pm hL hm hmn hr2
      have := hsph z hz
      rw [hzm] at this
      linarith
  have hpt : ∀ z ∈ sphere (QuantumNLS.LocalSpectral.center L n) r,
      (resolvent L κ (fun _ => 0) (parity n) z) (chi L m j) =
        (z - (pm L m : ℂ))⁻¹ • chi L m j := fun z hz =>
    res_chi hL j (hRf z hz).1 hm (hz_ne z hz)
  rw [circleIntegral.integral_congr hr.le hpt, circleIntegral.integral_smul_const]
  by_cases hmn : m = n
  · subst hmn
    rw [if_pos rfl]
    have hcen : QuantumNLS.LocalSpectral.center L m = (pm L m : ℂ) := rfl
    rw [hcen, circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr), smul_smul,
      inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero]), one_smul]
  · rw [if_neg hmn]
    have hcen : QuantumNLS.LocalSpectral.center L n = (pm L n : ℂ) := rfl
    have hz0 : (∮ z in C(QuantumNLS.LocalSpectral.center L n, r), (z - (pm L m : ℂ))⁻¹) = 0 := by
      rw [hcen]
      refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
        (Set.countable_empty) ?_ ?_
      · intro z hz
        have hzne : z - (pm L m : ℂ) ≠ 0 := by
          intro h0
          have hzm : z = (pm L m : ℂ) := sub_eq_zero.1 h0
          have : ‖z - (pm L n : ℂ)‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
          rw [hzm] at this
          have := far_pm hL hm hmn hr2
          linarith
        exact ((continuousAt_id.sub continuousAt_const).inv₀ hzne).continuousWithinAt
      · intro z hz
        have hzne : z - (pm L m : ℂ) ≠ 0 := by
          intro h0
          have hzm : z = (pm L m : ℂ) := sub_eq_zero.1 h0
          have : ‖z - (pm L n : ℂ)‖ < r := by simpa [mem_ball, dist_eq_norm] using hz.1
          rw [hzm] at this
          have := far_pm hL hm hmn hr2
          linarith
        exact ((differentiableAt_id.sub (differentiableAt_const _)).inv hzne)
    rw [hz0, zero_smul, smul_zero]

/-! ### Rank of the free projection and rank stability -/

/-- The range of a bounded operator, as a submodule. -/
abbrev rng (P : H2 L →L[ℂ] H2 L) : Submodule ℂ (H2 L) := LinearMap.range (P : H2 L →ₗ[ℂ] H2 L)

theorem finrank_freeProj (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (hres : ∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r → ∃ R : H2 L →L[ℂ] H2 L,
      IsResolvent L κ (fun _ => 0) (parity n) z R ∧ ‖R‖ ≤ 1 / r) :
    Module.finrank ℂ (rng (freeProj L κ n r)) = 2 := by
  rw [freeProj_eq hL hr hr2 n hres]
  have hinv := adjoint_embed_comp_embed hL n
  have hinj : Function.Injective (embed L n) := by
    intro v w h
    have := congrArg (fun x => ContinuousLinearMap.adjoint (embed L n) x) h
    simpa [← ContinuousLinearMap.comp_apply, hinv] using this
  have hrange : LinearMap.range ((embed L n ∘L ContinuousLinearMap.adjoint (embed L n) :
      H2 L →L[ℂ] H2 L) : H2 L →ₗ[ℂ] H2 L) = LinearMap.range (embed L n : E2 →ₗ[ℂ] H2 L) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨ContinuousLinearMap.adjoint (embed L n) x, rfl⟩
    · rintro _ ⟨v, rfl⟩
      refine ⟨embed L n v, ?_⟩
      have := congrArg (fun A : E2 →L[ℂ] E2 => A v) hinv
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
      show embed L n (ContinuousLinearMap.adjoint (embed L n) (embed L n v)) = embed L n v
      rw [this]
  show Module.finrank ℂ (LinearMap.range ((embed L n ∘L ContinuousLinearMap.adjoint (embed L n) :
      H2 L →L[ℂ] H2 L) : H2 L →ₗ[ℂ] H2 L)) = 2
  rw [hrange]
  rw [LinearMap.finrank_range_of_inj (f := (embed L n : E2 →ₗ[ℂ] H2 L)) hinj]
  simp

/-- Two idempotents at distance `< 1` have ranges of equal finite dimension. -/
theorem finrank_range_eq_of_close {P Q : H2 L →L[ℂ] H2 L} (hP : P ∘L P = P) (hQ : Q ∘L Q = Q)
    (h : ‖P - Q‖ < 1) (hfin : Module.Finite ℂ (rng Q)) :
    Module.Finite ℂ (rng P) ∧
      Module.finrank ℂ (rng P) = Module.finrank ℂ (rng Q) := by
  have hPx : ∀ x ∈ rng P, P x = x := by
    rintro _ ⟨y, rfl⟩
    have := congrArg (fun A : H2 L →L[ℂ] H2 L => A y) hP
    simpa using this
  have hQx : ∀ x ∈ rng Q, Q x = x := by
    rintro _ ⟨y, rfl⟩
    have := congrArg (fun A : H2 L →L[ℂ] H2 L => A y) hQ
    simpa using this
  have key : ∀ (A B : H2 L →L[ℂ] H2 L), ‖A - B‖ < 1 →
      (∀ x ∈ rng A, A x = x) → ∀ x ∈ rng A, B x = 0 → x = 0 := by
    intro A B hAB hA x hx hBx
    have h1 : x = (A - B) x := by
      rw [ContinuousLinearMap.sub_apply, hA x hx, hBx, sub_zero]
    have h2 : ‖x‖ ≤ ‖A - B‖ * ‖x‖ := by
      calc ‖x‖ = ‖(A - B) x‖ := by rw [← h1]
        _ ≤ ‖A - B‖ * ‖x‖ := (A - B).le_opNorm x
    by_contra hne
    have : 0 < ‖x‖ := norm_pos_iff.2 hne
    nlinarith
  let f : rng P →ₗ[ℂ] rng Q :=
    (Q : H2 L →ₗ[ℂ] H2 L).restrict (p := rng P) (q := rng Q)
      (fun x _ => ⟨x, rfl⟩)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : Q (x : H2 L) = 0 := by
      exact congrArg Subtype.val hx
    exact Subtype.ext (key P Q h hPx x x.2 hx0)
  have : Module.Finite ℂ (rng P) := Module.Finite.of_injective f hf
  let g : rng Q →ₗ[ℂ] rng P :=
    (P : H2 L →ₗ[ℂ] H2 L).restrict (p := rng Q) (q := rng P)
      (fun x _ => ⟨x, rfl⟩)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : P (x : H2 L) = 0 := by
      exact congrArg Subtype.val hx
    have h' : ‖Q - P‖ < 1 := by rw [norm_sub_rev]; exact h
    exact Subtype.ext (key Q P h' hQx x x.2 hx0)
  refine ⟨inferInstance, le_antisymm ?_ ?_⟩
  · exact LinearMap.finrank_le_finrank_of_injective hf
  · exact LinearMap.finrank_le_finrank_of_injective hg

end QuantumNLS.Local002Free
#print axioms QuantumNLS.Local002Free.freeProj_eq
#print axioms QuantumNLS.Local002Free.finrank_freeProj
#print axioms QuantumNLS.Local002Free.finrank_range_eq_of_close
#print axioms QuantumNLS.Local002Free.free_symm
