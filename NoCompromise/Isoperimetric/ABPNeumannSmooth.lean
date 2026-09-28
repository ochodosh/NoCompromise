import NoCompromise.Isoperimetric.ABPNeumann

/-!
# The smooth clause of `lem:abp-neumann` from local boundary regularity of every order

`ABPNeumannSolvable` asks for a solution `z` of the ABP Neumann problem that is smooth up to
the boundary, `ContDiffOn ℝ ⊤ z (closure G)`. This file reduces it to one local statement,
`ABPNeumannLocalBoundarySmoothRegularity`: for every boundary point `p` and every order `k`
there is an open neighbourhood `V` of `p` (which may shrink with `k`) on which the weak
solution agrees a.e. on `G ∩ V` with a `C^{k+1}` function whose derivative along the classical
outward normal is `1` on the boundary. The interior representative is smooth
(`exists_smooth_interior_representative`); the C¹ gluing `neumann_glue_c1_closure` gives one
function on `closure G`, and near each boundary point it agrees on `closure G ∩ V` with each
local function (they are continuous and agree a.e. on the open set `G ∩ V`). Since `Cᵏ` within
`closure G` is a local property, the glued function is `Cᵏ` on `closure G` for every `k`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal InnerProductSpace

namespace LiquidDrop

/-- Local boundary regularity of every order for the weak solutions of the constant ABP data,
as a named hypothesis: for every boundary point `p` and every `k` there is an open `V ∋ p`
(depending on `k`) on which the weak solution agrees a.e. on `G ∩ V` with a `C^{k+1}` function
on `V` whose derivative along the classical outward normal is `1` on `∂G ∩ V`. -/
def ABPNeumannLocalBoundarySmoothRegularity : Prop :=
  ∀ (G : Set AmbientSpace) (hGo : IsOpen G) (hGb : Bornology.IsBounded G)
    (_hGc : IsConnected G) (hGs : HasSmoothBoundary G) (z : H1Space G),
    IsWeakNeumannSolution hGo hGb hGs.hasC1Boundary.hasLipschitzBoundary
      (abpNeumannForcing G hGb) (abpNeumannFlux G hGo hGb hGs) z →
    ∀ p ∈ frontier G, ∀ k : ℕ, ∃ V : Set AmbientSpace, ∃ w : AmbientSpace → ℝ,
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ (k + 1) w V ∧
        (⇑z =ᵐ[volume.restrict (G ∩ V)] w) ∧
        ∀ x ∈ frontier G ∩ V, fderiv ℝ w x (hGs.hasC1Boundary.outwardNormal x) = 1

/-- The local smooth hypothesis contains the local C¹ one. -/
theorem ABPNeumannLocalBoundarySmoothRegularity.c1
    (h : ABPNeumannLocalBoundarySmoothRegularity) : ABPNeumannLocalBoundaryC1Regularity := by
  intro G hGo hGb hGc hGs z hz p hp
  obtain ⟨V, w, hV, hpV, hw, hzw, hν⟩ := h G hGo hGb hGc hGs z hz p hp 0
  exact ⟨V, w, hV, hpV, by simpa using hw, hzw, hν⟩

/-- `ABPNeumannBoundaryRegularity` (weak solutions of the constant ABP data have a
representative smooth up to the boundary, with `Δ = Per(G)/|G|` and `∂_ν = 1`) from the
local boundary regularity of every order. -/
theorem abpNeumannBoundaryRegularity_of_localBoundarySmooth
    (hb : ABPNeumannLocalBoundarySmoothRegularity) : ABPNeumannBoundaryRegularity := by
  intro G hGo hGb hGc hGs z hz
  obtain ⟨v₀, hv₀, hz₀, hlap, -⟩ :=
    hz.exists_smooth_interior_representative (abpNeumannForcing_ae G hGb)
  have hloc := hb G hGo hGb hGc hGs z hz
  have hv₀2 : ContDiffOn ℝ 2 v₀ G := by simpa using contDiffOn_infty.mp hv₀ 2
  obtain ⟨v, hvG, hzv, -, hv1, hν⟩ := neumann_glue_c1_closure hGo hv₀2 hz₀
    (fun p hp => by
      obtain ⟨V, w, hV, hpV, hw, hzw, hwν⟩ := hloc p hp 0
      exact ⟨V, w, hV, hpV, by simpa using hw, hzw, hwν⟩)
    (fun x hx => hGs.hasC1Boundary.uniqueDiffWithinAt_closure hx)
  refine ⟨v, hzv, ?_, ?_, hν⟩
  · refine contDiffOn_infty.mpr fun k => contDiffOn_of_locally_contDiffOn fun x hx => ?_
    by_cases hxG : x ∈ G
    · refine ⟨G, hGo, hxG, ?_⟩
      have h1 : ContDiffOn ℝ k v₀ G := contDiffOn_infty.mp hv₀ k
      exact (h1.mono inter_subset_right).congr fun y hy => hvG hy.2
    · have hxf : x ∈ frontier G := by
        rw [hGo.frontier_eq]
        exact ⟨hx, hxG⟩
      obtain ⟨V, w, hV, hxV, hw, hzw, -⟩ := hloc x hxf k
      refine ⟨V, hV, hxV, ?_⟩
      have hint : EqOn v w (G ∩ V) := by
        have hzv' : ⇑z =ᵐ[volume.restrict (G ∩ V)] v :=
          ae_restrict_of_ae_restrict_of_subset inter_subset_left hzv
        have hae : v =ᵐ[volume.restrict (G ∩ V)] w := hzv'.symm.trans hzw
        exact Measure.eqOn_open_of_ae_eq hae (hGo.inter hV)
          (hv1.continuousOn.mono (inter_subset_left.trans subset_closure))
          (hw.continuousOn.mono inter_subset_right)
      have heq : EqOn v w (closure G ∩ V) := by
        refine hint.of_subset_closure (hv1.continuousOn.mono inter_subset_left)
          (hw.continuousOn.mono inter_subset_right)
          (inter_subset_inter_left V subset_closure) ?_
        intro y hy
        have := hV.inter_closure ⟨hy.2, hy.1⟩
        rwa [inter_comm] at this
      have hwk : ContDiffOn ℝ k w V := hw.of_le (by exact_mod_cast Nat.le_succ k)
      exact (hwk.mono inter_subset_right).congr heq
  · intro x hx
    have he : v =ᶠ[𝓝 x] v₀ := Filter.eventually_of_mem (hGo.mem_nhds hx) (fun y hy => hvG hy)
    have hd : fderiv ℝ (fderiv ℝ v) x = fderiv ℝ (fderiv ℝ v₀) x := he.fderiv.fderiv_eq
    rw [← hlap x hx]
    simp only [laplacianTrace, hessianForm, hd]

/-- Blueprint `lem:abp-neumann` (literal smooth clause) from the local boundary regularity of
every order: every bounded connected open set with smooth boundary carries a solution `z`
smooth up to the boundary with `Δz = Per(G)/|G|` in `G` and `∂_ν z = 1` on `∂G`. -/
theorem abpNeumannSolvable_of_localBoundarySmooth
    (hb : ABPNeumannLocalBoundarySmoothRegularity) : ABPNeumannSolvable :=
  abpNeumannSolvable_of_boundaryRegularity (abpNeumannBoundaryRegularity_of_localBoundarySmooth hb)

end LiquidDrop
