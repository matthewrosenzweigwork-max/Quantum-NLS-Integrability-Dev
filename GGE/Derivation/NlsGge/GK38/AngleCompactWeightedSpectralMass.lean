import NlsGge.GK38.AngleWeightedSpectralOriginalFamily
import Mathlib.Order.Filter.Finite

/-! Genuine compact input globalization of the ACTUAL weighted spectral
square majorant. ONE supplied ORIGINAL family persists on ONE potential
neighborhood, so different local seed covers never change the nth-placement
certificate. No locally uniform vanishing tail is asserted. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem angleRegularFactor_compact_weighted_spectral_mass38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfamily : IsolatingFamily38 φ₀ C R)
    (K : Set Lib.L2Seq) (hK : IsCompact K) :
    ∃ U : Set PotPair, ∃ V : Set Lib.L2Seq, ∃ B : ℝ,
      IsOpen U ∧ IsOpen V ∧ φ₀ ∈ U ∧ U ⊆ gkW ∧ K ⊆ V ∧ 0 ≤ B ∧
      ∀ φ ∈ U, IsolatingFamily38 φ C R ∧
        ∀ s ∈ V, ∀ n : ℤ,
          Lib.sigmaOf s n ∈ closedBall (C n) (R n) →
          ∃ b : ℤ → ℝ, (∀ m, 0 ≤ b m) ∧
            Summable (fun m : ℤ => b m^2) ∧ (∑' m : ℤ, b m^2) ≤ B ∧
            ∀ m : ℤ, n ≠ m →
              ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
                DifferentiableAt ℂ
                  (fun w => angleRegularFactor38 n m ((φ,s),w)) z ∧
                ‖(((n-m : ℤ) : ℂ))*
                  deriv (fun w => angleRegularFactor38 n m ((φ,s),w)) z‖ ≤ b m := by
  classical
  choose U hU hUW V hV B hB hspec using
    (fun s₀ : Lib.L2Seq => angleRegularFactor_weighted_spectral_derivative_l2_original_family38
      φ₀ hφ₀ C R hfamily s₀)
  obtain ⟨F,_hFK,hcover⟩ := hK.elim_nhds_subcover
    (fun s₀ => interior (V s₀))
    (fun s₀ _ => isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr (hV s₀)))
  let H : Set PotPair := {φ | ∀ s₀ ∈ F, φ ∈ U s₀}
  have hH : H ∈ nhds φ₀ := F.eventually_all.mpr (fun s₀ _ => hU s₀)
  obtain ⟨ρ,hρ,c,N,hgeom,hpersist⟩ := fixed_family_persistence38 φ₀ C R hfamily
  let U₀ : Set PotPair := gkW ∩ (ball φ₀ ρ ∩ interior H)
  let V₀ : Set Lib.L2Seq := ⋃ s₀ ∈ F, interior (V s₀)
  have hU₀ : IsOpen U₀ := isOpen_gkW.inter (isOpen_ball.inter isOpen_interior)
  have hbase : φ₀ ∈ U₀ := ⟨hφ₀,mem_ball_self hρ,mem_interior_iff_mem_nhds.mpr hH⟩
  refine ⟨U₀,V₀,∑ s₀ ∈ F, B s₀,hU₀,
    isOpen_biUnion (fun s₀ _ => isOpen_interior),hbase,fun φ hφ => hφ.1,hcover,
    Finset.sum_nonneg (fun s₀ _ => hB s₀),?_⟩
  intro φ hφ
  refine ⟨⟨c,N,hgeom,hpersist φ hφ.2.1⟩,?_⟩
  intro s hs n hσ
  obtain ⟨s₀,hs₀F,hs₀V⟩ := mem_iUnion₂.mp hs
  have hφU : φ ∈ U s₀ := (interior_subset hφ.2.2) s₀ hs₀F
  obtain ⟨b,hb0,hbs,hbB,hbcut⟩ :=
    (hspec s₀ φ hφU).2 s (interior_subset hs₀V) n hσ
  refine ⟨b,hb0,hbs,hbB.trans ?_,hbcut⟩
  exact Finset.single_le_sum (fun t _ => hB t) hs₀F

end
end NlsGge.GK38
