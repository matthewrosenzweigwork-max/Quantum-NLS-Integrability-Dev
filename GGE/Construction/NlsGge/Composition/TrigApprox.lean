import NlsGge.Composition.Model

/-!
# W03.05: approximation by trigonometric polynomials in the unchanged weighted norm

Source: `paper/v2.tex`, line 1464 ("Choose a real trigonometric polynomial `p` approximating `f`
in `A_w(X)`").  A model element with finite support synthesizes to a finite Fourier sum, and
finite truncations converge in `ℓ²`, i.e. in the `A_w` norm.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NlsGge.Composition

open AddCircle

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {w : ℤ → ℝ}

/-- Truncation of a model element to a finite set of frequencies. -/
def truncate (S : Finset ℤ) (g : Model X) : Model X :=
  Model.ofLp (∑ i ∈ S, lp.single 2 i (g i))

theorem truncate_apply (S : Finset ℤ) (g : Model X) (n : ℤ) :
    truncate S g n = if n ∈ S then g n else 0 := by
  classical
  unfold truncate
  simp only [Model.coe_ofLp]
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply]
  by_cases hn : n ∈ S
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · intro h; exact absurd hn h
  · rw [if_neg hn]
    refine Finset.sum_eq_zero fun b hb => ?_
    have : n ≠ b := fun h => hn (h ▸ hb)
    simp [Pi.single_apply, this]

/-- Every model element is approximated by truncations. -/
theorem exists_truncate_near (g : Model X) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℤ, ‖g - truncate S g‖ < ε := by
  classical
  have h := lp.hasSum_single (p := 2) (by norm_num) g.toLp
  obtain ⟨S, hS⟩ := (Metric.tendsto_nhds.mp h ε hε).exists
  refine ⟨S, ?_⟩
  rw [dist_comm, dist_eq_norm] at hS
  exact hS

/-- The synthesis of a truncation is a finite trigonometric sum. -/
theorem synth_truncate (S : Finset ℤ) (g : Model X)
    (θ : AddCircle (1 : ℝ)) :
    synth w (truncate S g) θ = ∑ n ∈ S, fourier n θ • coeff w g n := by
  classical
  unfold synth expSum
  rw [tsum_eq_sum (s := S)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp [coeff, truncate_apply, hn]
  · intro n hn
    simp [coeff, truncate_apply, hn]

end NlsGge.Composition
