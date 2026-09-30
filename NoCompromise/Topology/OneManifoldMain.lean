module

public import NoCompromise.Topology.OneManifoldDiffeo

@[expose] public section

/-!
# `lem:one-manifold`

`blueprint/chapters/14-flows.tex`, `lem:one-manifold`: a connected Hausdorff smooth
one-manifold without boundary (modelled on `𝓘(ℝ, ℝ)`) carrying a smooth nowhere-zero tangent
vector field is diffeomorphic to `ℝ` or to the circle, and if it is not compact it has exactly two
ends (`HasExactlyTwoEnds`). Second countability is not needed. The embedded form used for
components of regular level sets on an oriented surface is `levelComponent_diffeo_circle_or_real`
and `levelComponent_hasExactlyTwoEnds` (`Surface/LevelOneManifold.lean`, `Surface/OneManifold.lean`).
-/

namespace LiquidDrop

open scoped ContDiff Manifold

/-- `lem:one-manifold`, abstract form. -/
theorem oneManifold_diffeo_and_ends {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold 𝓘(ℝ, ℝ) ∞ M] [T2Space M] [ConnectedSpace M]
    {v : (x : M) → TangentSpace 𝓘(ℝ, ℝ) x}
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hv0 : ∀ x, v x ≠ 0) :
    (Nonempty (ℝ ≃ₘ^∞⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ M) ∨ Nonempty (Circle ≃ₘ^∞⟮𝓡 1, 𝓘(ℝ, ℝ)⟯ M)) ∧
      (¬ CompactSpace M → HasExactlyTwoEnds M) :=
  ⟨oneManifold_diffeomorph_real_or_circle hv hv0,
    fun hM => oneManifold_hasExactlyTwoEnds (hv.of_le (by simp)) hv0 hM⟩

end LiquidDrop
