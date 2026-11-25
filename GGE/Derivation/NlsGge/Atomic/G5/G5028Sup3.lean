import Mathlib
import NlsGge.Atomic.G5.G5028Sup1
import NlsGge.Atomic.G5.G5028Sup2
import NlsGge.Atomic.G1.G1072
import NlsGge.Atomic.G5.G5018Asm
import NlsGge.Atomic.G5.G5018Dir
import NlsGge.Atomic.G5.G5001Host
import NlsGge.Atomic.G5.G5017Host

/- G5-028 SUPPORT 3 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5028Sup3.lean, namespace NlsGge.Atomic.G5028.
   (1) hform_aux: for ONE real potential v with interior Dirichlet points in gaps k and l, and Delta_v = Delta_u0, lamMinus_v = L:
       {mu_k, lam_l^-}/(delta_k delta_l) = dirInterpolation(mu_k; L) / (2 Delta'(L) delta_l)      [Sup1 + swap + landed G1-072].
   (2) pointwise_bound: the quantitative estimate of that quotient used by the limit. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G5028
noncomputable section

theorem hform_aux (v w : PhysicalL2) (k l : ℤ) (hk : InteriorRealDirichletGap k v)
    (hl : InteriorRealDirichletGap l v)
    (hD : discrim (realSlice v) = discrim (realSlice w)) (L : ℂ)
    (hL : lamMinus (realSlice v) l = L) :
    pairPoisson (fun ψ : PotPair => muSeq ψ k) (fun ψ : PotPair => lamMinus ψ l) (realSlice v) /
        (antiDiscrim (realSlice v) (muSeq (realSlice v) k) *
          antiDiscrim (realSlice v) (muSeq (realSlice v) l)) =
      dirInterpolation38 (realSlice v) (muSeq (realSlice v) k) L /
        (2 * deriv (discrim (realSlice w)) L *
          antiDiscrim (realSlice v) (muSeq (realSlice v) l)) := by
  have hpp := pairPoisson_mu_lamMinus v k l hl
  have hgap : gamma2 (realSlice v) l ≠ 0 := gamma2_ne_zero_of_lt _ _ (lt_trans hl.1 hl.2)
  obtain ⟨-, hr, hs⟩ := lower_endpoint_simple v l hgap
  have h72 := G1_072 (realSlice v) k (lamMinus (realSlice v) l) ⟨hr, hs⟩ (g5018dir_simple v k)
  have hsw := kernelPoisson_swap38
    (periodicKernel38 (realSlice v) (lamMinus (realSlice v) l))
    (dirEigenKernel38 (realSlice v) (muSeq (realSlice v) k))
  have hdn : deriv (discrim (realSlice v)) (lamMinus (realSlice v) l) ≠ 0 := h72.1
  have eq1 : pairPoisson (fun ψ : PotPair => muSeq ψ k) (fun ψ : PotPair => lamMinus ψ l) (realSlice v) =
      antiDiscrim (realSlice v) (muSeq (realSlice v) k) *
        dirInterpolation38 (realSlice v) (muSeq (realSlice v) k) (lamMinus (realSlice v) l) /
        (2 * deriv (discrim (realSlice v)) (lamMinus (realSlice v) l)) := by
    rw [hpp, hsw]
    have h2 := h72.2
    field_simp at h2 ⊢
    linear_combination -h2
  rw [eq1, hL, hD]
  have hδk := g5018_antiDiscrim_ne_zero v k hk
  have hδl := g5018_antiDiscrim_ne_zero v l hl
  have hdn' : deriv (discrim (realSlice w)) L ≠ 0 := by rw [← hD, ← hL]; exact hdn
  field_simp

theorem pointwise_bound (v : PhysicalL2) (k l : ℤ) (L Δ' : ℂ) (T c C : ℝ)
    (hl : InteriorRealDirichletGap l v) (hΔn : 0 < ‖Δ'‖) (hc : 0 < c) (hTpos : 0 < T)
    (hne : muSeq (realSlice v) k ≠ L)
    (hC : ‖dirichletChar (realSlice v) L‖ ≤ C * ‖L - muSeq (realSlice v) l‖)
    (hT : T / 2 ≤ ‖L - muSeq (realSlice v) k‖ *
      ‖deriv (dirichletChar (realSlice v)) (muSeq (realSlice v) k)‖)
    (hcj : c * ‖muSeq (realSlice v) l - L‖ ≤ ‖perChar (realSlice v) (muSeq (realSlice v) l)‖) :
    ‖dirInterpolation38 (realSlice v) (muSeq (realSlice v) k) L /
        (2 * Δ' * antiDiscrim (realSlice v) (muSeq (realSlice v) l))‖ ≤
      (max C 0 / ((T / 2) * (2 * ‖Δ'‖) * Real.sqrt c)) * Real.sqrt ‖L - muSeq (realSlice v) l‖ := by
  have hδl := g5018_antiDiscrim_ne_zero v l hl
  have hδpos : 0 < ‖antiDiscrim (realSlice v) (muSeq (realSlice v) l)‖ := norm_pos_iff.mpr hδl
  have hsq := dirichlet_perChar_eq_anti_sq38 (realSlice v) (muSeq (realSlice v) l)
    (muSeq_root38 _ l)
  have hδe : c * ‖L - muSeq (realSlice v) l‖ ≤
      ‖antiDiscrim (realSlice v) (muSeq (realSlice v) l)‖ ^ 2 := by
    rw [norm_sub_rev]
    rw [hsq, norm_pow] at hcj
    exact hcj
  have hN : ‖dirichletChar (realSlice v) L‖ ≤ max C 0 * ‖L - muSeq (realSlice v) l‖ :=
    le_trans hC (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hdsl : dirInterpolation38 (realSlice v) (muSeq (realSlice v) k) L =
      dirichletChar (realSlice v) L /
        ((L - muSeq (realSlice v) k) * deriv (dirichletChar (realSlice v))
          (muSeq (realSlice v) k)) := by
    unfold dirInterpolation38
    rw [dslope_of_ne _ hne.symm, slope_def_field, muSeq_root38, sub_zero]
    field_simp
  have hQ : ‖dirInterpolation38 (realSlice v) (muSeq (realSlice v) k) L /
      (2 * Δ' * antiDiscrim (realSlice v) (muSeq (realSlice v) l))‖ =
      ‖dirichletChar (realSlice v) L‖ /
        (‖L - muSeq (realSlice v) k‖ *
          ‖deriv (dirichletChar (realSlice v)) (muSeq (realSlice v) k)‖) /
        (2 * ‖Δ'‖ * ‖antiDiscrim (realSlice v) (muSeq (realSlice v) l)‖) := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_div, hdsl, norm_div, norm_mul, norm_mul, norm_mul, h2]
  rw [hQ]
  have hTh : 0 < T / 2 := half_pos hTpos
  have hmono : ‖dirichletChar (realSlice v) L‖ /
        (‖L - muSeq (realSlice v) k‖ *
          ‖deriv (dirichletChar (realSlice v)) (muSeq (realSlice v) k)‖) ≤
      ‖dirichletChar (realSlice v) L‖ / (T / 2) :=
    div_le_div_of_nonneg_left (norm_nonneg _) hTh hT
  have hden : 0 < 2 * ‖Δ'‖ * ‖antiDiscrim (realSlice v) (muSeq (realSlice v) l)‖ := by positivity
  refine le_trans (div_le_div_of_nonneg_right hmono hden.le) ?_
  have := real_aux ‖L - muSeq (realSlice v) l‖ _ _ (T / 2) (max C 0) (2 * ‖Δ'‖) c
    (norm_nonneg _) hδpos hc hTh (by positivity) (le_max_right _ _) (norm_nonneg _) hN hδe
  exact this

theorem mu_tendsto (u₀ : PhysicalL2) (u : ℕ → PhysicalL2) (hlim : Tendsto u atTop (𝓝 u₀)) (n : ℤ) :
    Tendsto (fun j : ℕ => muSeq (realSlice (u j)) n) atTop (𝓝 (muSeq (realSlice u₀) n)) := by
  have h1 : Tendsto (fun j : ℕ => gkMu (u j) n) atTop (𝓝 (gkMu u₀ n)) :=
    ((continuous_gkMu38 n).tendsto u₀).comp hlim
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h1
  simpa only [Function.comp_def, muSeq_eq_gkMu38] using h2

theorem tendsto_deriv_dirichlet (φ : ℕ → PotPair) (φ₀ : PotPair) (a : ℕ → ℂ) (a₀ : ℂ)
    (hφ : Tendsto φ atTop (𝓝 φ₀)) (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun j : ℕ => deriv (dirichletChar (φ j)) (a j)) atTop
      (𝓝 (deriv (dirichletChar φ₀) a₀)) := by
  have hp : Tendsto (fun j : ℕ => (φ j, a j)) atTop (𝓝 (φ₀, a₀)) := hφ.prodMk_nhds ha
  have h := (continuous_deriv_dirichletChar.tendsto (φ₀, a₀)).comp hp
  exact h

theorem tendsto_product_aux (a : ℕ → ℂ) (a₀ L : ℂ) (d : ℕ → ℂ) (d₀ : ℂ)
    (ha : Tendsto a atTop (𝓝 a₀)) (hd : Tendsto d atTop (𝓝 d₀)) :
    Tendsto (fun j : ℕ => ‖L - a j‖ * ‖d j‖) atTop (𝓝 (‖L - a₀‖ * ‖d₀‖)) :=
  ((tendsto_const_nhds.sub ha).norm).mul hd.norm

theorem product_event (a : ℕ → ℂ) (a₀ L : ℂ) (d : ℕ → ℂ) (d₀ : ℂ)
    (ha : Tendsto a atTop (𝓝 a₀)) (hd : Tendsto d atTop (𝓝 d₀)) (hLa : L ≠ a₀) (hd0 : d₀ ≠ 0) :
    0 < ‖L - a₀‖ * ‖d₀‖ ∧ ∀ᶠ j : ℕ in atTop, (‖L - a₀‖ * ‖d₀‖) / 2 < ‖L - a j‖ * ‖d j‖ := by
  have hpos : 0 < ‖L - a₀‖ * ‖d₀‖ :=
    mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hLa)) (norm_pos_iff.mpr hd0)
  exact ⟨hpos, (tendsto_product_aux a a₀ L d d₀ ha hd).eventually (lt_mem_nhds (half_lt_self hpos))⟩

theorem T_event (u₀ : PhysicalL2) (u : ℕ → PhysicalL2) (hlim : Tendsto u atTop (𝓝 u₀)) (k : ℤ)
    (L Lk : ℂ) (hmuk : Tendsto (fun j : ℕ => muSeq (realSlice (u j)) k) atTop (𝓝 Lk))
    (hLLk : L ≠ Lk) (hD0 : deriv (dirichletChar (realSlice u₀)) Lk ≠ 0) :
    0 < ‖L - Lk‖ * ‖deriv (dirichletChar (realSlice u₀)) Lk‖ ∧
    ∀ᶠ j : ℕ in atTop, (‖L - Lk‖ * ‖deriv (dirichletChar (realSlice u₀)) Lk‖) / 2 <
      ‖L - muSeq (realSlice (u j)) k‖ *
        ‖deriv (dirichletChar (realSlice (u j))) (muSeq (realSlice (u j)) k)‖ := by
  have hφ : Tendsto (fun j : ℕ => realSlice (u j)) atTop (𝓝 (realSlice u₀)) :=
    (realSlice.continuous.tendsto u₀).comp hlim
  exact product_event _ Lk L _ _ hmuk (tendsto_deriv_dirichlet _ _ _ _ hφ hmuk) hLLk hD0

theorem core_limit (u₀ : PhysicalL2) (u : ℕ → PhysicalL2) (k l : ℤ) (L Δ' : ℂ) (T c C : ℝ)
    (hinterior : ∀ j : ℕ, InteriorRealDirichletGap l (u j))
    (hΔn : 0 < ‖Δ'‖) (hc : 0 < c) (hTpos : 0 < T)
    (hmul : Tendsto (fun j : ℕ => muSeq (realSlice (u j)) l) atTop (𝓝 L))
    (hne : ∀ᶠ j : ℕ in atTop, muSeq (realSlice (u j)) k ≠ L)
    (hC : ∀ᶠ j : ℕ in atTop, ‖dirichletChar (realSlice (u j)) L‖ ≤
      C * ‖L - muSeq (realSlice (u j)) l‖)
    (hT : ∀ᶠ j : ℕ in atTop, T / 2 < ‖L - muSeq (realSlice (u j)) k‖ *
      ‖deriv (dirichletChar (realSlice (u j))) (muSeq (realSlice (u j)) k)‖)
    (hcev : ∀ᶠ j : ℕ in atTop, c * ‖muSeq (realSlice (u j)) l - L‖ ≤
      ‖perChar (realSlice (u j)) (muSeq (realSlice (u j)) l)‖) :
    Tendsto (fun j : ℕ => dirInterpolation38 (realSlice (u j)) (muSeq (realSlice (u j)) k) L /
      (2 * Δ' * antiDiscrim (realSlice (u j)) (muSeq (realSlice (u j)) l))) atTop (𝓝 0) := by
  have he0 : Tendsto (fun j : ℕ => ‖L - muSeq (realSlice (u j)) l‖) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := L)).sub hmul).norm
    simpa only [sub_self, norm_zero] using h
  refine squeeze_sqrt _ _ ((max C 0) / ((T / 2) * (2 * ‖Δ'‖) * Real.sqrt c)) he0 ?_
  filter_upwards [hC, hT, hne, hcev] with j hCj hTj hnej hcj
  exact pointwise_bound (u j) k l L Δ' T c C (hinterior j) hΔn hc hTpos hnej hCj hTj.le hcj

end
end NlsGge.Atomic.G5028
