import QuantumNLS.RayPeriodUpgrade

/-! integrator-authored trusted spec for LOCAL-015 `reset:ray-period-upgrade`
(local/quantum_periods.tex:405-411). Let H be a complex Hilbert space of complex dimension at least two and
F continuously Fréchet differentiable (over ℝ, on the realification) on the punctured norm ball
{u : 0 < ‖u‖ < R}, symplectic there for Ω(h,k) = 2 Im⟨h,k⟩ (DEF-015, written literally): Ω(DF(u)h, DF(u)k) =
Ω(h,k). Suppose F(u) lies on the complex unit ray of u (F(u) = c u with |c| = 1) for every u in the punctured
ball, and each mass sphere {‖u‖² = m}, 0 < m < R², contains a point fixed by F. Then F is the identity on the
punctured ball. -/

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.LOCAL015Spec

def Spec : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    2 ≤ Module.rank ℂ H → ∀ (R : ℝ) (F : H → H),
    ContDiffOn ℝ 1 F {u | 0 < ‖u‖ ∧ ‖u‖ < R} →
    (∀ u, 0 < ‖u‖ → ‖u‖ < R → ∀ h k : H,
      2 * (inner ℂ (fderiv ℝ F u h) (fderiv ℝ F u k)).im = 2 * (inner ℂ h k).im) →
    (∀ u, 0 < ‖u‖ → ‖u‖ < R → ∃ c : ℂ, ‖c‖ = 1 ∧ F u = c • u) →
    (∀ m : ℝ, 0 < m → m < R ^ 2 → ∃ v : H, ‖v‖ ^ 2 = m ∧ F v = v) →
    ∀ u, 0 < ‖u‖ → ‖u‖ < R → F u = u

theorem spec : Spec := by
  intro H _ _ _ hdim R F hF hsymp hray hfix u hu0 huR
  have hset : {u : H | 0 < ‖u‖ ∧ ‖u‖ < R} = RayPeriodUpgrade.puncturedBall H R := by
    ext v; exact RayPeriodUpgrade.mem_puncturedBall.symm
  rw [hset] at hF
  exact RayPeriodUpgrade.ray_period_upgrade hdim hF
    (fun v hv h k => hsymp v (RayPeriodUpgrade.mem_puncturedBall.mp hv).1
      (RayPeriodUpgrade.mem_puncturedBall.mp hv).2 h k)
    (fun v hv => hray v (RayPeriodUpgrade.mem_puncturedBall.mp hv).1
      (RayPeriodUpgrade.mem_puncturedBall.mp hv).2)
    hfix u (RayPeriodUpgrade.mem_puncturedBall.mpr ⟨hu0, huR⟩)

end QuantumNLS.LOCAL015Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.LOCAL015Spec.spec
  IO.println s!"LOCAL015Spec.spec axioms: {ax}"
