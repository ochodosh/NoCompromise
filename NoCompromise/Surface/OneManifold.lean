import NoCompromise.Surface.LevelOneManifold
import NoCompromise.Topology.Ends

/-!
# `lem:one-manifold`, embedded form: the two ends of a noncompact level component

`blueprint/chapters/14-flows.tex`, `lem:one-manifold`, in the form the blueprint applies
(`lem:merge-disjoint`): on a compact embedded surface `S ⊆ ℝ³` with unit normal field `n`, a
connected component `C` of the regular part of a level set of a smooth `h` is diffeomorphic to
`S¹` or to `ℝ` (`levelComponent_diffeo_circle_or_real`), and if `C` is not compact it has exactly
two ends in the Freudenthal–Hopf sense (`HasExactlyTwoEnds`). When `p` is the only critical point
of `h` on `S` at level `c`, the regular part of the level is `(S ∩ {h = c}) \ {p}`, the set whose
components `lem:merge-disjoint` considers.
-/

noncomputable section

open Set

namespace LiquidDrop

variable {S : Set E₃} {n : E₃ → E₃} {h : E₃ → ℝ}

/-- `lem:one-manifold` (embedded form), consequence: a noncompact connected component of the
regular part of a level set on a compact oriented embedded surface has exactly two ends. -/
theorem levelComponent_hasExactlyTwoEnds (hS : IsSmoothEmbeddedSurface S) (hSc : IsCompact S)
    (hn : IsUnitNormalField S n) (hh : ContDiff ℝ (⊤ : ℕ∞) h) {c : ℝ} {x₀ : E₃}
    (hx₀ : x₀ ∈ regularLevel S h c)
    (hC : ¬ IsCompact (connectedComponentIn (regularLevel S h c) x₀)) :
    HasExactlyTwoEnds (connectedComponentIn (regularLevel S h c) x₀) := by
  obtain ⟨γ, -, -, -, -, -, hcase⟩ := levelComponent_diffeo_circle_or_real (n := n) hS hSc hn hh hx₀
  rcases hcase with ⟨τ, -, -, -, hcpt, -⟩ | ⟨-, -, e, -⟩
  · exact absurd hcpt hC
  · exact Homeomorph.hasExactlyTwoEnds e hasExactlyTwoEnds_real

/-- If `p` is the only critical point of `h` on `S` at level `c`, the regular part of the level
`c` is the level minus `p`. -/
theorem regularLevel_eq_diff_singleton {c : ℝ} {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p)
    (huniq : ∀ q, IsSurfaceCriticalPoint S h q → h q = c → q = p) :
    regularLevel S h c = (S ∩ {x | h x = c}) \ {p} := by
  ext x
  simp only [regularLevel, mem_ofPred_eq, mem_sdiff, mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxS, hxc, hxr⟩
    exact ⟨⟨hxS, hxc⟩, fun hxp => hxr (hxp ▸ hp)⟩
  · rintro ⟨⟨hxS, hxc⟩, hxp⟩
    exact ⟨hxS, hxc, fun hcrit => hxp (huniq x hcrit hxc)⟩

end LiquidDrop
