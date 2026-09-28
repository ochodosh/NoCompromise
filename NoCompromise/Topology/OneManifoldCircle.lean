import NoCompromise.Topology.OneManifoldSmooth
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Periodic complete integral curves and the smooth circle

Smoothness means `∞ : WithTop ℕ∞` throughout. The local argument of `w / z`
is smooth near `w = z`, since the quotient is then `1`, in the complex slit plane.
-/

namespace LiquidDrop

open Set Function Filter Manifold
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false in
/-- The argument relative to a fixed circle point is smooth at that point. -/
theorem oneManifold_circle_contMDiffAt_arg_div (z : Circle) :
    ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (fun w : Circle => Complex.arg (↑(w / z) : ℂ)) z := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  have hq : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun w : Circle => (↑(w / z) : ℂ)) z :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1)).contMDiffAt.comp z
      (contMDiffAt_id.div contMDiffAt_const)
  have hl : ContDiffAt ℝ ∞ Complex.log (↑(z / z) : ℂ) :=
    (Complex.contDiffAt_log (x := (↑(z / z) : ℂ)) (by simp)).restrict_scalars ℝ
  have hi := Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp z
    (hl.contMDiffAt.comp z hq)
  change ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
    (fun w : Circle => (Complex.log (↑(w / z) : ℂ)).im) z at hi
  simpa only [Complex.log_im] using hi

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, ℝ) x} {γ : ℝ → M}

set_option backward.isDefEq.respectTransparency false in
/-- A fundamental period identifies a complete integral curve of a smooth,
nowhere-zero field with the standard smooth circle. -/
theorem oneManifold_integralCurve_diffeomorph_circle [T2Space M] [ConnectedSpace M]
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hv0 : ∀ x, v x ≠ 0) (hγ : IsMIntegralCurve γ v)
    {τ : ℝ} (hτ : 0 < τ) (hper : Periodic γ τ) (hinj : InjOn γ (Ico 0 τ)) :
    ∃ Φ : Circle ≃ₘ^∞⟮𝓡 1, 𝓘(ℝ, ℝ)⟯ M,
      ∀ t : ℝ, Φ (Circle.exp (2 * Real.pi / τ * t)) = γ t := by
  obtain ⟨e, he⟩ := oneManifold_integralCurve_homeomorph_addCircle
    (hv.of_le (by simp)) hv0 hγ hτ hper hinj
  let f : Circle ≃ₜ M := (AddCircle.homeomorphCircle (ne_of_gt hτ)).symm.trans e
  have hf (t : ℝ) : f (Circle.exp (2 * Real.pi / τ * t)) = γ t := by
    have hc : AddCircle.homeomorphCircle (ne_of_gt hτ) (t : AddCircle τ) =
        Circle.exp (2 * Real.pi / τ * t) := by
      rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    change e ((AddCircle.homeomorphCircle (ne_of_gt hτ)).symm _) = γ t
    rw [← hc, Homeomorph.symm_apply_apply]
    exact he t
  have hcancel (t : ℝ) : 2 * Real.pi / τ * (τ / (2 * Real.pi) * t) = t := by
    field_simp
  have hforward : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ f := by
    intro z
    let a : Circle → ℝ := fun w => Complex.arg (↑(w / z) : ℂ) + Complex.arg (z : ℂ)
    have ha (w : Circle) : Circle.exp (a w) = w := by
      change Circle.exp (Complex.arg (↑(w / z) : ℂ) + Complex.arg (z : ℂ)) = w
      rw [Circle.exp_add, Circle.exp_arg, Circle.exp_arg, div_mul_cancel]
    have heq : (f : Circle → M) = fun w => γ (τ / (2 * Real.pi) * a w) := by
      funext w
      rw [← hf, hcancel, ha]
    rw [heq]
    apply (oneManifold_integralCurve_contMDiff hv hγ _).comp z
    exact ((contDiff_const.mul contDiff_id).contMDiff.contMDiffAt).comp z
      ((oneManifold_circle_contMDiffAt_arg_div z).add contMDiffAt_const)
  have hinverse : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ f.symm := by
    intro y
    obtain ⟨t, rfl⟩ := oneManifold_integralCurve_surjective (hv.of_le (by simp)) hv0 hγ y
    have ht := oneManifold_integralCurve_isLocalDiffeomorph hv hv0 hγ t
    have hs : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 1) ∞
        (fun x => Circle.exp (2 * Real.pi / τ * ht.localInverse x)) (γ t) :=
      contMDiff_circleExp.contMDiffAt.comp (γ t)
        (((contDiff_const.mul contDiff_id).contMDiff.contMDiffAt).comp (γ t)
          ht.localInverse_contMDiffAt)
    apply hs.congr_of_eventuallyEq
    filter_upwards [ht.localInverse.open_source.mem_nhds ht.localInverse_mem_source] with x hx
    apply f.injective
    rw [f.apply_symm_apply, hf, ht.localInverse_right_inv hx]
  exact ⟨{ f.toEquiv with contMDiff_toFun := hforward, contMDiff_invFun := hinverse }, hf⟩

/-- A complete integral curve of a smooth nowhere-zero field on a connected
Hausdorff one-manifold gives a diffeomorphism from the real line or the circle. -/
theorem oneManifold_diffeomorph_real_or_circle_of_isMIntegralCurve
    [T2Space M] [ConnectedSpace M]
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hv0 : ∀ x, v x ≠ 0) (hγ : IsMIntegralCurve γ v) :
    Nonempty (ℝ ≃ₘ^∞⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ M) ∨
      Nonempty (Circle ≃ₘ^∞⟮𝓡 1, 𝓘(ℝ, ℝ)⟯ M) := by
  rcases (oneManifold_classification_of_isMIntegralCurve
    (hv.of_le (by simp)) hv0 hγ).2 with ⟨hinj, _⟩ | ⟨τ, hτ, hper, hinj, _⟩
  · obtain ⟨Φ, _⟩ := oneManifold_integralCurve_diffeomorph_real hv hv0 hγ hinj
    exact Or.inl ⟨Φ⟩
  · obtain ⟨Φ, _⟩ := oneManifold_integralCurve_diffeomorph_circle hv hv0 hγ hτ hper hinj
    exact Or.inr ⟨Φ⟩

end LiquidDrop
