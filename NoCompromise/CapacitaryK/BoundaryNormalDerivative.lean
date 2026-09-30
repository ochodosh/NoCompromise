module

public import NoCompromise.CapacitaryK.CollarC2

@[expose] public section

/-!
# `|∇u|` on `∂K` is the one-sided normal derivative of `u`

The boundary integrands of `thm:capacitary-inequalities` are written with a `C²` extension `g`
of the capacitary potential `u` across `∂K`. They do not depend on the choice of `g`: at
`p ∈ ∂K`, `t ↦ u(p + t ν_K)` has right derivative `-|∇g(p)|` at `0`, since `p + t ν_K ∈ Kᶜ` for
small `t > 0`. Hence `|∇g(p)|` (and, by `meanCurv_extension_eq_meanCurvature_chart`, the mean
curvature) is intrinsic to `u` and `K` (not:w, `w = |∇u|` on `∂K`).
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- Points `p + t ν_K`, `t > 0` small, on the outward normal line at `p ∈ ∂K` lie in `Kᶜ`. -/
lemma eventually_normal_line_mem_compl {K : Set E3} (hreg : K = closure (interior K))
    (hC1 : HasC1Boundary (interior K)) {p : E3} (hp : p ∈ frontier (interior K)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • hC1.outwardNormal p ∈ Kᶜ := by
  obtain ⟨c, hc, hpc⟩ := hC1 p hp
  have hn := hC1.outwardNormal_eq_chart hc hp hpc
  have hcv : 0 < inner ℝ (hC1.outwardNormal p) (c.outwardNormal p) := by
    rw [hn, real_inner_self_eq_norm_sq, c.norm_outwardNormal]
    norm_num
  have hext := classicalNormal_eventually_pos_of_hasDerivAt
    (c.hasDerivAt_definingFunction_line p (hC1.outwardNormal p))
    (by simpa using hc.definingFunction_eq_zero hp hpc)
    (mul_pos (Real.sqrt_pos.mpr (by positivity)) hcv)
  have hcont : Continuous (fun t : ℝ => p + t • hC1.outwardNormal p) := by fun_prop
  have hline : Tendsto (fun t : ℝ => p + t • hC1.outwardNormal p) (𝓝[>] 0) (𝓝 p) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [hext, hline (c.isOpen_region.mem_nhds hpc)] with t hte htr
  intro hin
  have hin' : p + t • hC1.outwardNormal p ∈ closure (interior K) := by rwa [← hreg]
  have hgraph : p + t • hC1.outwardNormal p ∈ closure c.graphDomain :=
    (hc.closure_inter_eq ▸ (show p + t • hC1.outwardNormal p ∈ closure (interior K) ∩ c.region
      from ⟨hin', htr⟩)).1
  have hle := (c.mem_closure_graphDomain_iff _).mp hgraph
  exact (not_lt_of_ge hle) (sub_pos.mp hte)

/-- At `p ∈ ∂K`, the right derivative of `t ↦ u(p + t ν_K)` at `0` is `-|∇g(p)|`, for any
`C²` extension `g` of `u` across `∂K` with `∇g(p) = -|∇g(p)| ν_K`. -/
theorem hasDerivWithinAt_normal_line_of_extension {K : Set E3} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {u g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    {p : E3} (hp : p ∈ frontier K)
    (hgp : gradient g p = -‖gradient g p‖ • hC1.outwardNormal p) :
    HasDerivWithinAt (fun t : ℝ => u (p + t • hC1.outwardNormal p)) (-‖gradient g p‖)
      (Ioi 0) 0 := by
  have hpi : p ∈ frontier (interior K) := by rwa [capacity_frontier_interior hK hreg]
  have hν : ‖hC1.outwardNormal p‖ = 1 := hC1.norm_outwardNormal hpi
  have hline : HasDerivAt (fun t : ℝ => p + t • hC1.outwardNormal p) (hC1.outwardNormal p) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (hC1.outwardNormal p)).const_add p
  have hdg : HasFDerivAt g (fderiv ℝ g p) (p + (0 : ℝ) • hC1.outwardNormal p) := by
    simpa using (hg.differentiable (by norm_num) p).hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => g (p + t • hC1.outwardNormal p))
      (fderiv ℝ g p (hC1.outwardNormal p)) 0 := hdg.comp_hasDerivAt 0 hline
  have hval : fderiv ℝ g p (hC1.outwardNormal p) = -‖gradient g p‖ := by
    rw [← inner_gradient_eq_fderiv]
    conv_lhs => rw [hgp]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hν]
    ring
  rw [hval] at hcomp
  have hpcl : p ∈ closure Kᶜ :=
    frontier_subset_closure (show p ∈ frontier Kᶜ by rwa [frontier_compl])
  refine hcomp.hasDerivWithinAt.congr_of_eventuallyEq ?_ (by simpa using hug hpcl)
  filter_upwards [eventually_normal_line_mem_compl hreg hC1 hpi] with t ht
  exact hug (subset_closure ht)

/-- The boundary value `|∇g|` on `∂K` does not depend on the `C²` extension `g`. -/
theorem norm_gradient_extension_eq {K : Set E3} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {u g₁ g₂ : E3 → ℝ} (hg₁ : ContDiff ℝ 2 g₁) (hug₁ : EqOn u g₁ (closure Kᶜ))
    (hg₂ : ContDiff ℝ 2 g₂) (hug₂ : EqOn u g₂ (closure Kᶜ))
    {p : E3} (hp : p ∈ frontier K)
    (hgp₁ : gradient g₁ p = -‖gradient g₁ p‖ • hC1.outwardNormal p)
    (hgp₂ : gradient g₂ p = -‖gradient g₂ p‖ • hC1.outwardNormal p) :
    ‖gradient g₁ p‖ = ‖gradient g₂ p‖ := by
  have h := (uniqueDiffWithinAt_Ioi (0 : ℝ)).eq_deriv _
    (hasDerivWithinAt_normal_line_of_extension hK hreg hC1 hg₁ hug₁ hp hgp₁)
    (hasDerivWithinAt_normal_line_of_extension hK hreg hC1 hg₂ hug₂ hp hgp₂)
  linarith

end LiquidDrop.CapacitaryK
