import NoCompromise.DeGiorgi.SmoothBoundary
import NoCompromise.Sobolev.LipschitzDomains
import NoCompromise.Sobolev.H1Poincare
import NoCompromise.Sobolev.H1TraceOperator
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Sobolev estimates on geometric C¹ domains

A local C¹ subgraph chart admits a smaller Lipschitz shear chart, with the
opposite normal orientation so that the domain corresponds to the upper half
cube. The Sobolev estimates therefore apply to the geometric C¹ boundary
condition, without an extension or trace operator among the hypotheses.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology
open scoped ENNReal NNReal Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A C¹ boundary chart supplies a genuine Lipschitz chart after shrinking. -/
theorem C1BoundaryChart.IsChartFor.exists_lipschitzGraphChart
    {c : C1BoundaryChart} {D : Set AmbientSpace} (hc : c.IsChartFor D)
    {x : AmbientSpace} (hx : x ∈ frontier D) (hxr : x ∈ c.region) :
    ∃ d : LipschitzGraphChart 3, d.IsChartFor D ∧ x ∈ d.region := by
  have hxg : x ∈ c.graphSurface :=
    (hc.frontier_inter_eq ▸ (show x ∈ frontier D ∩ c.region from ⟨hx, hxr⟩)).1
  obtain ⟨z, ⟨p, rfl⟩, rfl⟩ := hxg
  let q : AmbientSpace := graphMapN c.height p
  let h : AmbientSpace → ℝ := fun y => c.height p - c.height (p - graphProjectionN 2 y)
  have hh : ContDiff ℝ 1 h :=
    contDiff_const.sub (c.height_contDiff.comp
      (contDiff_const.sub (graphProjectionN 2).contDiff))
  obtain ⟨L, V, hV, hLV⟩ := hh.contDiffAt.exists_lipschitzOnWith (x := 0)
  obtain ⟨g, hg, heq⟩ := exists_lipschitz_extension_real hLV
  have hg0 : g 0 = 0 := by
    rw [← heq (mem_of_mem_nhds hV)]
    simp [h]
  let a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace :=
    (AffineIsometryEquiv.constVSub ℝ q).trans c.placement
  let e := placedGraphHomeomorph (Fin.last 2) hg a
  have he0 : e 0 = c.placement q := by
    change c.placement (q - graphShear (Fin.last 2) g 0) = _
    have herase : coordinateErase (Fin.last 2) (0 : AmbientSpace) = 0 := by
      ext j
      simp [coordinateErase_apply]
    simp only [graphShear, herase, hg0, zero_smul, add_zero, sub_zero]
  have hn : {y | coordinateErase (Fin.last 2) y ∈ V ∧ e y ∈ c.region} ∈ 𝓝 0 := by
    apply inter_mem
    · have hc0 := (lipschitzWith_coordinateErase (Fin.last 2)).continuous.continuousAt
        (x := (0 : AmbientSpace))
      have hez : coordinateErase (Fin.last 2) (0 : AmbientSpace) = 0 := by
        ext j
        simp [coordinateErase_apply]
      exact hc0.preimage_mem_nhds (by simpa only [hez] using hV)
    · apply e.continuous.continuousAt.preimage_mem_nhds
      exact c.isOpen_region.mem_nhds (he0 ▸ hxr)
  obtain ⟨R, hR, hsub⟩ := exists_coordinateCube_subset_nhds_zero hn
  let d : LipschitzGraphChart 3 := ⟨Fin.last 2, R, hR, g, L, hg, a⟩
  have hmem (y : AmbientSpace) (hy : y ∈ coordinateCube 3 R) :
      d.homeomorph y ∈ D ↔ 0 < y (Fin.last 2) := by
    have hsmall := hsub hy
    change e y ∈ D ↔ _
    rw [hc _ hsmall.2]
    change c.placement.symm (c.placement (q - graphShear (Fin.last 2) g y)) ∈
      smoothSubgraph c.height ↔ _
    rw [c.placement.symm_apply_apply]
    have hproj : graphProjectionN 2 (graphShear (Fin.last 2) g y) =
        graphProjectionN 2 y := by
      ext j
      simp only [graphProjectionN_apply, graphShear_apply, Fin.castSucc_ne_last, ite_false]
    have hprojE : graphProjectionN 2 (coordinateErase (Fin.last 2) y) =
        graphProjectionN 2 y := by
      ext j
      simp only [graphProjectionN_apply, coordinateErase_apply, Fin.castSucc_ne_last, ite_false]
    have hprojq : graphProjectionN 2 q = p := by
      ext j
      simp [q]
    change (q - graphShear (Fin.last 2) g y) (Fin.last 2) <
      c.height (graphProjectionN 2 (q - graphShear (Fin.last 2) g y)) ↔ _
    simp only [map_sub, hproj, hprojq, PiLp.sub_apply, graphShear_apply, ite_true]
    rw [← heq hsmall.1]
    simp only [h, hprojE, q, graphMapN_last]
    constructor <;> intro hlt <;> linarith
  refine ⟨d, ?_, ?_⟩
  · change d.homeomorph '' coordinateHalfCube (Fin.last 2) R =
      D ∩ (d.homeomorph '' coordinateCube 3 R)
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hmem y hy.1).mpr hy.2, ⟨y, hy.1, rfl⟩⟩
    · rintro ⟨hz, y, hy, rfl⟩
      exact ⟨y, ⟨hy, (hmem y hy).mp hz⟩, rfl⟩
  · refine ⟨0, ?_, he0⟩
    intro j
    simpa only [PiLp.zero_apply, abs_zero] using hR

/-- Every geometric C¹ boundary is Lipschitz in the chart convention used for
Sobolev extension. This local implication needs neither boundedness nor openness. -/
theorem HasC1Boundary.hasLipschitzBoundary {D : Set AmbientSpace}
    (h : HasC1Boundary D) : HasLipschitzBoundary D := by
  intro x hx
  obtain ⟨c, hc, hxr⟩ := h x hx
  exact hc.exists_lipschitzGraphChart hx hxr

/-- Poincaré on every bounded connected open geometric C¹ domain in three dimensions. -/
theorem h1_poincare_c1_domain {D : Set AmbientSpace}
    (hD : IsOpen D) (hcD : IsPreconnected D) (hbD : Bornology.IsBounded D)
    (hC1 : HasC1Boundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f G, HasH1GradientOn f G D →
      lpNorm (fun x => f x - ⨍ y in D, f y) 2 (volume.restrict D) ≤
        C * lpNorm G 2 (volume.restrict D) :=
  h1_poincare_spatial hD hcD hbD hC1.hasLipschitzBoundary

/-- Both clauses of blueprint `prop:poincare-trace` on bounded connected open
C¹ domains. The trace is a genuine bounded operator, agrees with continuous
representatives, and is the L² limit of the boundary values of smooth H¹
approximations. The same positive constant controls both inequalities. -/
theorem exists_h1_poincare_trace_c1_domain {D : Set AmbientSpace}
    (hD : IsOpen D) (hcD : IsPreconnected D) (hbD : Bornology.IsBounded D)
    (hC1 : HasC1Boundary D) :
    ∃ T : H1Space D →L[ℝ] Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D)),
    ∃ C : ℝ, 0 < C ∧ ‖T‖ ≤ C ∧
      (∀ f G, HasH1GradientOn f G D →
        lpNorm (fun x => f x - ⨍ y in D, f y) 2 (volume.restrict D) ≤
          C * lpNorm G 2 (volume.restrict D)) ∧
      (∀ u : H1Space D, ‖T u‖ ≤ C *
        (lpNorm u 2 (volume.restrict D) + lpNorm u.gradientLp 2 (volume.restrict D))) ∧
      (∀ f G (hf : HasH1GradientOn f G D), Continuous f →
        ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D),
          T (H1Space.ofFunction f G hf) x = f x) ∧
      ∀ u : H1Space D, ∃ v : ℕ → AmbientSpace → ℝ,
        ∃ hv : ∀ j, HasH1GradientOn (v j) (gradient (v j)) D,
        ∃ hb : ∀ j, MemLp (v j) 2 ((hausdorffMeasure2 3).restrict (frontier D)),
          (∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j)) ∧
          Tendsto (fun j => H1Space.ofFunction (v j) (gradient (v j)) (hv j)) atTop (𝓝 u) ∧
          Tendsto (fun j => (hb j).toLp (v j)) atTop (𝓝 (T u)) := by
  obtain ⟨P, hP, hPI⟩ := h1_poincare_c1_domain hD hcD hbD hC1
  obtain ⟨T, C, hC, hTC, hTI, hT, happrox⟩ :=
    exists_h1_trace hD hbD hC1.hasLipschitzBoundary
  refine ⟨T, max P C, lt_of_lt_of_le hP (le_max_left _ _),
    hTC.trans (le_max_right _ _), ?_, ?_, hT, happrox⟩
  · intro f G hf
    exact (hPI f G hf).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) lpNorm_nonneg)
  · intro u
    exact (hTI u).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (add_nonneg lpNorm_nonneg lpNorm_nonneg))

end LiquidDrop
