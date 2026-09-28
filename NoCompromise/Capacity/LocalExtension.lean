import NoCompromise.Capacity.HullEnergy
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Local-to-global form of the named C² boundary-extension hypothesis

Chapters 30/31 take as a named hypothesis a global `C²` function `g` with `u = g` on
`closure Kᶜ` (the stand-in for `thm:boundary-C2a` up to `∂K`). Boundary regularity is local:
flattening a boundary chart and extending across the flat face produces, near each `p ∈ ∂K`,
a `C²` function agreeing with `u` on the closure of the exterior near `p`. A smooth partition of
unity glues these local extensions, `u` itself on `Kᶜ`, and `0` on `int K` into one global `C²`
function. This reduces the named hypothesis to its local form.
-/

noncomputable section
open Set Filter Metric
open scoped Topology Manifold ContDiff
namespace LiquidDrop

/-- Local `C²` extensions at every boundary point glue to a global `C²` extension: if `u` is
`C²` on the open exterior `Kᶜ` and near every `p ∈ ∂K` agrees on `closure Kᶜ` with a `C²`
function, then some `C²` function agrees with `u` on all of `closure Kᶜ`. -/
theorem exists_c2_extension_of_local {K : Set AmbientSpace} (hK : IsClosed K)
    {u : AmbientSpace → ℝ} (hs : ContDiffOn ℝ 2 u Kᶜ)
    (hloc : ∀ p ∈ frontier K, ∃ U : Set AmbientSpace, IsOpen U ∧ p ∈ U ∧
      ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (U ∩ closure Kᶜ)) :
    ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure Kᶜ) := by
  classical
  have hcl : closure Kᶜ = (interior K)ᶜ := closure_compl
  have hpick : ∀ x : AmbientSpace, ∃ U : Set AmbientSpace, ∃ h : AmbientSpace → ℝ,
      IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, ContDiffAt ℝ 2 h y) ∧ EqOn u h (U ∩ closure Kᶜ) := by
    intro x
    by_cases hxK : x ∈ K
    · by_cases hxi : x ∈ interior K
      · refine ⟨interior K, fun _ => 0, isOpen_interior, hxi, fun y _ => contDiffAt_const, ?_⟩
        intro y hy
        rw [hcl] at hy
        exact (hy.2 hy.1).elim
      · have hxf : x ∈ frontier K := by
          rw [frontier, hK.closure_eq]
          exact ⟨hxK, hxi⟩
        obtain ⟨U, hU, hxU, g, hg, hug⟩ := hloc x hxf
        exact ⟨U, g, hU, hxU, fun y _ => hg.contDiffAt, hug⟩
    · refine ⟨Kᶜ, u, hK.isOpen_compl, hxK, fun y hy => hs.contDiffAt
        (hK.isOpen_compl.mem_nhds hy), fun y _ => rfl⟩
  choose U h hUo hxU hh hUeq using hpick
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, AmbientSpace)) isClosed_univ U hUo (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨fun y => ∑ᶠ x, f x y • h x y, ?_, ?_⟩
  · have hsm : ContMDiff 𝓘(ℝ, AmbientSpace) 𝓘(ℝ, ℝ) (2 : ℕ∞)
        (fun y => ∑ᶠ x, f x y • h x y) := by
      refine f.contMDiff_finsum_smul fun i y hy => ?_
      exact (hh i y (hf i hy)).contMDiffAt
    exact contMDiff_iff_contDiff.mp hsm
  · intro y hy
    have hmem := f.finsum_smul_mem_convex (g := h) (t := {u y}) (mem_univ y)
      (fun i hi => by
        have hyU : y ∈ U i := hf i (subset_tsupport _ hi)
        exact (hUeq i ⟨hyU, hy⟩).symm) (convex_singleton (u y))
    exact (mem_singleton_iff.mp hmem).symm

/-- The named hypothesis of chapters 30/31 for the filled hull follows from its local form:
`C²` extensions of the capacitary potential near each point of `∂K`. -/
theorem filledHull_capacitary_c2_extension_of_local {Ω : Set AmbientSpace}
    (hbd : Bornology.IsBounded Ω) {u : AmbientSpace → ℝ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (filledHull Ω)ᶜ)
    (hloc : ∀ p ∈ frontier (filledHull Ω), ∃ U : Set AmbientSpace, IsOpen U ∧ p ∈ U ∧
      ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (U ∩ closure (filledHull Ω)ᶜ)) :
    ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ) :=
  exists_c2_extension_of_local (filledHull_isCompact hbd).isClosed
    (hs.of_le (WithTop.coe_le_coe.mpr le_top)) hloc

end LiquidDrop
