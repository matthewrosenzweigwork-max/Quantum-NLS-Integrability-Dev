import NlsGge.GK38.AbelianPaddedPeriodMapBound
import NlsGge.GK38.AbelianBoundedHolomorphicDerivative

/-! Actual potential residuals are uniformly small before ALL signed indices
and nearby full inputs. The seed target is the literal base value, including
its actual missing coordinate; no padded map is assumed zero at its seed. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedFn_local_uniform_potential_residual38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ ρ M : ℝ, 0 < ρ ∧ 0 ≤ M ∧ ball φ₀ ρ ⊆ gkW ∧
      ∀ b ∈ ball s₀ ρ, ∀ φ ∈ ball φ₀ ρ, ∀ n : ℤ,
        ‖p6PaddedFn38 n (φ,b)-p6PaddedFn38 n (φ₀,b)‖ ≤ M*‖φ-φ₀‖ := by
  obtain ⟨U,hU,hUW,V,hV,A,hA,hbound⟩ :=
    p6PaddedFn_uniform_norm_bound38 φ₀ hφ₀ s₀
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (prod_mem_nhds hU hV)
  have hdom : ball (φ₀,s₀) R ⊆ gkW ×ˢ (univ : Set Lib.L2Seq) :=
    fun p hp => ⟨hUW (hball hp).1,mem_univ _⟩
  have hhalf : R/2 ≤ R := by linarith
  have hpot : ball φ₀ (R/2) ⊆ gkW := by
    intro φ hφ
    have hp : (φ,s₀) ∈ ball (φ₀,s₀) R := by
      rw [mem_ball,Prod.dist_eq,dist_self]
      exact max_lt ((mem_ball.mp hφ).trans_le hhalf) hR
    exact (hdom hp).1
  refine ⟨R/2,4*A/R,half_pos hR,by positivity,hpot,?_⟩
  intro b hb φ hφ n
  have hp : (φ,b) ∈ ball (φ₀,s₀) (R/2) := by
    rw [mem_ball,Prod.dist_eq]
    exact max_lt (mem_ball.mp hφ) (mem_ball.mp hb)
  have hq : (φ₀,b) ∈ ball (φ₀,s₀) (R/2) := by
    rw [mem_ball,Prod.dist_eq,dist_self]
    exact max_lt (half_pos hR) (mem_ball.mp hb)
  have he : ‖(φ,b)-(φ₀,b)‖=‖φ-φ₀‖ := by
    rw [← dist_eq_norm,dist_prod_same_right,dist_eq_norm]
  have h := P6HolomorphicBounds.norm_sub_le_of_ball_bound
    (p6PaddedFn38 n) (φ₀,s₀) R A hR ((p6PaddedFn_analytic38 n).mono hdom)
    (fun p hp => hbound p.1 (hball hp).1 p.2 (hball hp).2 n)
    (φ,b) (φ₀,b) hp hq
  simpa only [he] using h

end
end NlsGge.GK38
