import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK0

/-! # Trunk C PREPARATORY lemma M1: all-data coordinate-phase equivariance (NOT admitted, NOT rooted)

Author: Claude Opus 5.5 (preparatory author P2, trunk C).  Not self-reviewed, not accepted.
Namespace `NlsGge.ALLS.TransCPrep`; non-approved prefix `prep_`.  No declaration here has the type
of an approved command; these are supporting lemmas (missing lemma M1 of PROOF_PLAN_TRUNK_C.md).

Notation: `R_t y = Φ (l2Flow t (Ψ y))` on `ℓ²(ℤ)` with `Φ = physicalBirkhoff`,
`Ψ = physicalInverseBirkhoff`; the phase `θ` acts on coordinate `n` only:
`P_θ y = y + single n ((exp(iθ) - 1) y_n)`, i.e. `(P_θ y)_n = exp(iθ) y_n`, `(P_θ y)_k = y_k` (`k ≠ n`).
This is the form `z + ι((exp(θ I) - 1) * π z)` of the hypothesis `hequiv` of
`TransCGenZeroFace.prep_zero_face_quotient` with `ι = lp.single 2 n`, `π = (· n)`.

Binders and conclusions (one line each):
* `prep_phase_apply (x θ n k)`: for `x ∈ ℓ²`, real `θ`, modes `n k`, coordinate `k` of `P_θ x` is
  `exp(iθ) x_n` if `k = n` and `x_k` otherwise.
* `prep_actions_phase (x θ n)`: `P_θ` does not change the actions: `actions (P_θ x) = actions x`.
* `prep_phase_equivariant_finite (y t θ n) (hfin)`: for finitely supported `y ∈ ℓ²`, all `t θ n`, `R_t (P_θ y) = P_θ (R_t y)`.
* `prep_phase_equivariant (x t θ n)`: for EVERY `x ∈ ℓ²`, every real `t`, `θ` and mode `n`, `R_t (P_θ x) = P_θ (R_t x)`
  (equality of `ℓ²` vectors, so all coordinates `k`, including `k ≠ n`).
* `prep_phase_equivariant_coord (x t θ n)`: coordinate `n` of the previous identity:
  `(R_t (P_θ x))_n = exp(iθ) (R_t x)_n`, for every `x t θ n`.

Route: finite support from `prep_l2Flow_finite_rotation` (rates depend only on actions, which `P_θ`
preserves); all data by the same `Finset`-filter density argument as `prep_action_invariant`
(continuity of `Ψ`, `l2Flow t`, `Φ`, `P_θ`).
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE NlsGge.ThirdConsultation.Common
open LiebLiniger.FixedPeriod.ALLS.PdeB NlsGge.ALLS.TransA

namespace NlsGge.ALLS.TransCPrep

theorem prep_phase_apply (x : Lib.L2Z) (θ : ℝ) (n k : ℤ) :
    ((x + lp.single (E := fun _ : ℤ => ℂ) 2 n
        ((Complex.exp (θ * Complex.I) - 1) * (x : ℤ → ℂ) n) : Lib.L2Z) : ℤ → ℂ) k =
      if k = n then Complex.exp (θ * Complex.I) * (x : ℤ → ℂ) n else (x : ℤ → ℂ) k := by
  rw [lp.coeFn_add, Pi.add_apply]
  by_cases hk : k = n
  · subst hk
    rw [lp.single_apply_self]
    simp only [↓reduceIte]
    ring
  · rw [lp.single_apply_ne 2 n _ hk, add_zero]
    simp only [hk, ↓reduceIte]

theorem prep_actions_phase (x : Lib.L2Z) (θ : ℝ) (n : ℤ) :
    actions (x + lp.single (E := fun _ : ℤ => ℂ) 2 n
        ((Complex.exp (θ * Complex.I) - 1) * (x : ℤ → ℂ) n)) = actions x := by
  funext k
  unfold actions
  rw [prep_phase_apply]
  by_cases hk : k = n
  · subst hk
    simp only [↓reduceIte]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  · simp only [hk, ↓reduceIte]

theorem prep_phase_equivariant_finite (y : Lib.L2Z) (t θ : ℝ) (n : ℤ)
    (hfin : FiniteSupportSequence y) :
    physicalBirkhoff (l2Flow t (physicalInverseBirkhoff
      (y + lp.single (E := fun _ : ℤ => ℂ) 2 n
        ((Complex.exp (θ * Complex.I) - 1) * (y : ℤ → ℂ) n)))) =
    physicalBirkhoff (l2Flow t (physicalInverseBirkhoff y)) +
      lp.single (E := fun _ : ℤ => ℂ) 2 n ((Complex.exp (θ * Complex.I) - 1) *
        (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff y)) : ℤ → ℂ) n) := by
  obtain ⟨-, hR, -⟩ := actual_birkhoff_bindings
  have hfinP : FiniteSupportSequence (y + lp.single (E := fun _ : ℤ => ℂ) 2 n
      ((Complex.exp (θ * Complex.I) - 1) * (y : ℤ → ℂ) n)) := by
    refine hfin.subset fun k hk => ?_
    change (_ : ℂ) ≠ 0 at hk
    change (_ : ℂ) ≠ 0
    rw [prep_phase_apply] at hk
    by_cases hkn : k = n
    · subst hkn
      simp only [↓reduceIte] at hk
      exact right_ne_zero_of_mul hk
    · simpa only [hkn, ↓reduceIte] using hk
  have h1 : FiniteSupportSequence (physicalBirkhoff (physicalInverseBirkhoff
      (y + lp.single (E := fun _ : ℤ => ℂ) 2 n
        ((Complex.exp (θ * Complex.I) - 1) * (y : ℤ → ℂ) n)))) := by
    rw [hR]; exact hfinP
  have h2 : FiniteSupportSequence (physicalBirkhoff (physicalInverseBirkhoff y)) := by
    rw [hR]; exact hfin
  apply lp.ext
  funext k
  rw [prep_l2Flow_finite_rotation _ h1 t k, prep_phase_apply, prep_l2Flow_finite_rotation _ h2 t n,
    prep_l2Flow_finite_rotation _ h2 t k, hR, hR, prep_actions_phase, prep_phase_apply]
  by_cases hk : k = n
  · subst hk
    simp only [↓reduceIte]
    ring
  · simp only [hk, ↓reduceIte]

theorem prep_phase_equivariant (x : Lib.L2Z) (t θ : ℝ) (n : ℤ) :
    physicalBirkhoff (l2Flow t (physicalInverseBirkhoff
      (x + lp.single (E := fun _ : ℤ => ℂ) 2 n
        ((Complex.exp (θ * Complex.I) - 1) * (x : ℤ → ℂ) n)))) =
    physicalBirkhoff (l2Flow t (physicalInverseBirkhoff x)) +
      lp.single (E := fun _ : ℤ => ℂ) 2 n ((Complex.exp (θ * Complex.I) - 1) *
        (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff x)) : ℤ → ℂ) n) := by
  obtain ⟨-, -, hA, hAinv, -⟩ := actual_birkhoff_bindings
  have hΦ : Continuous physicalBirkhoff := continuousOn_univ.mp hA.continuousOn
  have hΨ : Continuous physicalInverseBirkhoff := continuousOn_univ.mp hAinv.continuousOn
  have hsingle : Continuous fun c : ℂ => lp.single (E := fun _ : ℤ => ℂ) 2 n c :=
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).continuous
  have hP : Continuous fun y : Lib.L2Z => y + lp.single (E := fun _ : ℤ => ℂ) 2 n
      ((Complex.exp (θ * Complex.I) - 1) * (y : ℤ → ℂ) n) :=
    continuous_id.add (hsingle.comp (continuous_const.mul (prep_continuous_coord n)))
  have hRt : Continuous fun y : Lib.L2Z => physicalBirkhoff (l2Flow t (physicalInverseBirkhoff y)) :=
    hΦ.comp ((continuous_l2Flow.comp (continuous_const.prodMk continuous_id)).comp hΨ)
  let q : Finset ℤ → Lib.L2Z := fun S =>
    ∑ i ∈ S, lp.single (E := fun _ : ℤ => ℂ) (2 : ENNReal) i ((x : ℤ → ℂ) i)
  have hpartial : Tendsto q atTop (𝓝 x) :=
    lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ENNReal)) ENNReal.ofNat_ne_top x
  have hcoord (S : Finset ℤ) (k : ℤ) :
      (q S : ℤ → ℂ) k = if k ∈ S then (x : ℤ → ℂ) k else 0 := by
    simp only [q, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  have hfin (S : Finset ℤ) : FiniteSupportSequence (q S) := by
    refine S.finite_toSet.subset fun k hk => ?_
    by_contra hkS
    have hkS' : k ∉ S := by simpa using hkS
    exact hk (by rw [hcoord]; simp [hkS'])
  have hL := ((hRt.comp hP).tendsto x).comp hpartial
  have hRr := ((hP.comp hRt).tendsto x).comp hpartial
  have heq : (fun y : Lib.L2Z => physicalBirkhoff (l2Flow t (physicalInverseBirkhoff
      (y + lp.single (E := fun _ : ℤ => ℂ) 2 n
        ((Complex.exp (θ * Complex.I) - 1) * (y : ℤ → ℂ) n))))) ∘ q =
      (fun y : Lib.L2Z => physicalBirkhoff (l2Flow t (physicalInverseBirkhoff y)) +
        lp.single (E := fun _ : ℤ => ℂ) 2 n ((Complex.exp (θ * Complex.I) - 1) *
          (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff y)) : ℤ → ℂ) n)) ∘ q := by
    funext S
    exact prep_phase_equivariant_finite (q S) t θ n (hfin S)
  simp only [Function.comp_def] at hL hRr heq
  rw [heq] at hL
  exact tendsto_nhds_unique hL hRr

theorem prep_phase_equivariant_coord (x : Lib.L2Z) (t θ : ℝ) (n : ℤ) :
    (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff
      (x + lp.single (E := fun _ : ℤ => ℂ) 2 n
        ((Complex.exp (θ * Complex.I) - 1) * (x : ℤ → ℂ) n)))) : ℤ → ℂ) n =
    Complex.exp (θ * Complex.I) *
      (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff x)) : ℤ → ℂ) n := by
  rw [prep_phase_equivariant, prep_phase_apply]
  simp only [↓reduceIte]

end NlsGge.ALLS.TransCPrep
