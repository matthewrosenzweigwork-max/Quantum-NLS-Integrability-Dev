import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK1
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCGenRateLimit

/-! # Trunk C PREPARATORY lemmas, package K2 (rates on the nonnegative face; NOT approved/admitted/rooted)

Author: Claude Opus 5.5 (preparatory author P1, trunk C).  Not self-reviewed, not accepted.
Namespace `NlsGge.ALLS.TransCPrep`; every declaration carries the non-approved prefix `prep_`.
Notation as in K1: `Φ = physicalBirkhoff`, `Ψ = physicalInverseBirkhoff`, `ℓ² = Lib.L2Z`.
`C_n = {x ∈ ℓ² | x_n = ‖x_n‖}` (the `n`-th coordinate is a nonnegative real; no condition on the
other coordinates) and `D_n = {x ∈ C_n | x finitely supported, x_n ≠ 0}`.

Route (coordinator K2): on `D_n`, K1's `A_n(·, x) = exp(−i t actualOmega n (actions x))` by P2's K0
`prep_l2Flow_finite_rotation` (applied to `Ψ x`, with `Φ (Ψ x) = x`); `D_n` is dense in `C_n`
(`prep_mem_closure_D`); the generic `prep_rate_of_dense` (built on `rate_close_of_uniform_close`
on `[0, 1]`) gives the rate on the closure and its continuity.  Times are `t ∈ [0, 1]` (K1 with `T = 1`).

Binders and conclusions (one line each):
* `prep_mem_closure_D (n) (x) (hx : x_n = ‖x_n‖)`: every `x ∈ C_n` lies in the `ℓ²`-closure of `D_n`.
* `prep_K2_rate (n : ℤ)`: there is `ω : ℓ² → ℝ` with (i) `ω` continuous on `C_n` (ℓ² topology);
  (ii) for every `x ∈ C_n` and every `t ∈ [0,1]`,
  `Φ_n(l2Flow t (Ψ x)) = exp(−(t ω x) i) · x_n`; (iii) for every `x ∈ D_n`,
  `ω x = actualOmega n (actions x)` (the existing rate, `actions x k = ‖x_k‖²`).
  `ω` is NOT the trunk C `Ω` and no statement about `Ω`, measurability, or descent to actions is made.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE NlsGge.ThirdConsultation.Common
open NlsGge.SpectralFoundations NlsGge.NLS38
open LiebLiniger.FixedPeriod.ALLS.PdeB NlsGge.ALLS.TransA

namespace NlsGge.ALLS.TransCPrep

/-- Density of `D_n` in `C_n`. -/
theorem prep_mem_closure_D (n : ℤ) (x : Lib.L2Z)
    (hx : (x : ℤ → ℂ) n = ((‖(x : ℤ → ℂ) n‖ : ℝ) : ℂ)) :
    x ∈ closure {y : Lib.L2Z | (y : ℤ → ℂ) n = ((‖(y : ℤ → ℂ) n‖ : ℝ) : ℂ) ∧
      FiniteSupportSequence y ∧ (y : ℤ → ℂ) n ≠ 0} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let q : Finset ℤ → Lib.L2Z := fun S =>
    ∑ i ∈ S, lp.single (E := fun _ : ℤ => ℂ) (2 : ENNReal) i ((x : ℤ → ℂ) i)
  have hpartial : Tendsto q atTop (𝓝 x) :=
    lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ENNReal)) ENNReal.ofNat_ne_top x
  have hcoord (S : Finset ℤ) (k : ℤ) :
      (q S : ℤ → ℂ) k = if k ∈ S then (x : ℤ → ℂ) k else 0 := by
    simp only [q, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  obtain ⟨S, hS⟩ := (hpartial.eventually (Metric.ball_mem_nhds x (half_pos hε))).exists
  set c : ℝ := (if n ∈ S then ‖(x : ℤ → ℂ) n‖ else 0) + ε / 4 with hc
  have hc0 : 0 < c := by
    have : 0 ≤ (if n ∈ S then ‖(x : ℤ → ℂ) n‖ else 0) := by split_ifs <;> simp
    linarith
  let b : Lib.L2Z := q S + ((ε / 4 : ℝ) : ℂ) • prep_basis n
  have hb (k : ℤ) : (b : ℤ → ℂ) k =
      (if k ∈ S then (x : ℤ → ℂ) k else 0) + ((ε / 4 : ℝ) : ℂ) * (if k = n then 1 else 0) := by
    simp only [b, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hcoord, prep_basis_apply]
  have hbn : (b : ℤ → ℂ) n = ((c : ℝ) : ℂ) := by
    have e1 : (b : ℤ → ℂ) n =
        (if n ∈ S then (x : ℤ → ℂ) n else 0) + ((ε / 4 : ℝ) : ℂ) := by
      rw [hb]; congr 1; simp
    rw [e1, hc]
    split_ifs with hS'
    · rw [Complex.ofReal_add, ← hx]
    · rw [Complex.ofReal_add, Complex.ofReal_zero]
  refine ⟨b, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hbn, Complex.norm_real, Real.norm_of_nonneg hc0.le]
  · refine ((S : Set ℤ) ∪ {n}).toFinite.subset fun k hk => ?_
    by_contra hkS
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff, not_or] at hkS
    exact hk (by rw [hb]; simp [hkS.1, hkS.2])
  · rw [hbn]; exact Complex.ofReal_ne_zero.mpr hc0.ne'
  · have hnorm : ‖((ε / 4 : ℝ) : ℂ) • prep_basis n‖ = ε / 4 := by
      rw [norm_smul, prep_basis, lp.norm_single (by norm_num), norm_one, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc dist x b ≤ dist x (q S) + dist (q S) b := dist_triangle _ _ _
      _ = dist (q S) x + ‖((ε / 4 : ℝ) : ℂ) • prep_basis n‖ := by
          rw [dist_comm x, dist_eq_norm (q S) b]
          simp only [b, sub_add_cancel_left, norm_neg]
      _ < ε / 2 + ε / 4 := by rw [hnorm]; linarith
      _ < ε := by linarith

/-- **K2**: rates on `C_n`, continuous there, equal to `actualOmega` on `D_n`. -/
theorem prep_K2_rate (n : ℤ) :
    ∃ ω : Lib.L2Z → ℝ,
      ContinuousOn ω {x : Lib.L2Z | (x : ℤ → ℂ) n = ((‖(x : ℤ → ℂ) n‖ : ℝ) : ℂ)} ∧
      (∀ x : Lib.L2Z, (x : ℤ → ℂ) n = ((‖(x : ℤ → ℂ) n‖ : ℝ) : ℂ) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff x)) : ℤ → ℂ) n =
            Complex.exp (-((t * ω x : ℝ) : ℂ) * Complex.I) * (x : ℤ → ℂ) n) ∧
      (∀ x : Lib.L2Z, (x : ℤ → ℂ) n = ((‖(x : ℤ → ℂ) n‖ : ℝ) : ℂ) →
        FiniteSupportSequence x → (x : ℤ → ℂ) n ≠ 0 → ω x = actualOmega n (actions x)) := by
  obtain ⟨hL, hR, -⟩ := actual_birkhoff_bindings
  obtain ⟨A, hAc, -, hAid⟩ := prep_K1_zeroFace_division n 1
  have hsub : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := fun t =>
    ⟨by linarith [t.2.1], t.2.2⟩
  let a : Set.Icc (0 : ℝ) 1 × Lib.L2Z → ℂ := fun q => A ⟨q.1, hsub q.1⟩ q.2
  have ha : Continuous a :=
    hAc.comp (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd)
  set D : Set Lib.L2Z := {y : Lib.L2Z | (y : ℤ → ℂ) n = ((‖(y : ℤ → ℂ) n‖ : ℝ) : ℂ) ∧
      FiniteSupportSequence y ∧ (y : ℤ → ℂ) n ≠ 0} with hDdef
  have hD : ∀ x ∈ D, ∀ t : Set.Icc (0 : ℝ) 1,
      a (t, x) = Complex.exp (-(((t : ℝ) * actualOmega n (actions x) : ℝ) : ℂ) * Complex.I) := by
    rintro x ⟨hxn, hfin, hx0⟩ t
    have h1 := hAid ⟨t, hsub t⟩ x hxn
    have hfin' : FiniteSupportSequence (physicalBirkhoff (physicalInverseBirkhoff x)) := by
      rw [hR x]; exact hfin
    have h2 := prep_l2Flow_finite_rotation (physicalInverseBirkhoff x) hfin' (t : ℝ) n
    rw [hR x] at h2
    simp only at h1
    rw [h2, mul_comm ((x : ℤ → ℂ) n)] at h1
    have h3 := mul_right_cancel₀ hx0 h1
    simp only [a]
    rw [h3]
    congr 1
    ring
  obtain ⟨ω, hωc, hωid, hωD⟩ := prep_rate_of_dense a ha D (fun x => actualOmega n (actions x)) hD
  have hC : {x : Lib.L2Z | (x : ℤ → ℂ) n = ((‖(x : ℤ → ℂ) n‖ : ℝ) : ℂ)} ⊆ closure D :=
    fun x hx => prep_mem_closure_D n x hx
  refine ⟨ω, hωc.mono hC, fun x hx t ht => ?_, fun x hxn hfin hx0 => hωD x ⟨hxn, hfin, hx0⟩⟩
  have h1 := hAid ⟨t, hsub ⟨t, ht⟩⟩ x hx
  have h2 := hωid x (hC hx) ⟨t, ht⟩
  simp only [a] at h2
  simp only at h1
  rw [← h1, h2, mul_comm]

end NlsGge.ALLS.TransCPrep
