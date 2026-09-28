import NoCompromise.Capacity.FluxIdentity
import NoCompromise.Capacity.LowerBarrier

/-!
# Boundary gradient and the positive boundary flux

Blueprint `not:w` (`eq:w-boundary`) and `lem:flux-identity`
(`eq:flux-boundary`), with the same C² extension hypotheses as the signed
flux identity, and C² boundary charts and connected exterior for the Hopf sign.

The exterior maximum principle identifies the direction of the gradient:
if it were not opposite to the outward normal, the sum of the gradient and
its norm times the normal would point strictly outside and strictly increase
the potential above its boundary value. Hopf excludes a zero gradient.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology InnerProductSpace
open scoped ENNReal NNReal Gradient
namespace LiquidDrop

/-- Blueprint `not:w` (`eq:w-boundary`): the boundary gradient points into
`K`, and its magnitude is strictly positive. -/
theorem gradient_eq_neg_norm_smul_normal {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {R₀ : ℝ} (_hR₀ : 0 < R₀) (_hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    (hC2 : HasC2Boundary (interior K)) (hconn : IsPreconnected Kᶜ) :
    ∀ p ∈ frontier K,
      gradient g p = -‖gradient g p‖ • hC1.outwardNormal p ∧ 0 < ‖gradient g p‖ := by
  intro p hp
  have hpi : p ∈ frontier (interior K) := by
    rwa [capacity_frontier_interior hK hreg]
  have hpcl : p ∈ closure Kᶜ :=
    frontier_subset_closure (show p ∈ frontier Kᶜ by simpa using hp)
  have hup : u p = 1 := hb p (hK.isClosed.frontier_subset hp)
  have hgp : g p = 1 := (hug hpcl).symm.trans hup
  have hdg := (hg.differentiable (by norm_num) p).hasFDerivAt
  have hdu : HasFDerivWithinAt u (fderiv ℝ g p) (closure Kᶜ) p :=
    hdg.hasFDerivWithinAt.congr hug (hug hpcl)
  have hupper := (capacitary_signs hK hzero hu hh hb hinf).2 hconn
  obtain ⟨c, hc, hpc, hc2⟩ := hC2 p hpi
  have hn := hC1.outwardNormal_eq_chart hc hpi hpc
  have hsign : inner ℝ (gradient g p) (c.outwardNormal p) < 0 := by
    rw [inner_gradient_left]
    apply hopf_exterior_chart hc hc2 hpi hpc
    · simpa only [← hreg] using hu.continuousOn
    · simpa only [← hreg] using hh
    · simpa only [← hreg] using hupper
    · exact hup
    · simpa only [← hreg] using hdu
  have hpos : 0 < ‖gradient g p‖ := by
    apply norm_pos_iff.mpr
    intro hz
    simp only [hz, inner_zero_left] at hsign
    exact (lt_irrefl 0) hsign
  refine ⟨?_, hpos⟩
  rw [hn]
  by_contra hne
  let v := gradient g p + ‖gradient g p‖ • c.outwardNormal p
  have hv : v ≠ 0 := by
    intro hz
    apply hne
    exact (eq_neg_of_add_eq_zero_left hz).trans (neg_smul _ _).symm
  have hi : 0 < inner ℝ (gradient g p) (c.outwardNormal p) + ‖gradient g p‖ := by
    have hs := sq_pos_of_pos (norm_pos_iff.mpr hv)
    dsimp only [v] at hs
    rw [norm_add_sq_real, norm_smul, c.norm_outwardNormal,
      Real.norm_of_nonneg (norm_nonneg _), mul_one, inner_smul_right] at hs
    nlinarith
  have hcv : 0 < inner ℝ v (c.outwardNormal p) := by
    simpa only [v, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      c.norm_outwardNormal, one_pow, mul_one] using hi
  have hgv : 0 < fderiv ℝ g p v := by
    rw [← inner_gradient_left]
    dsimp only [v]
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    nlinarith [mul_pos hpos hi]
  have hext := classicalNormal_eventually_pos_of_hasDerivAt
    (c.hasDerivAt_definingFunction_line p v)
    (by simpa using hc.definingFunction_eq_zero hpi hpc)
    (mul_pos (Real.sqrt_pos.mpr (by positivity)) hcv)
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hgline : HasDerivAt (fun t : ℝ => g (p + t • v) - 1) (fderiv ℝ g p v) 0 := by
    have hdg' : HasFDerivAt g (fderiv ℝ g p) (p + (0 : ℝ) • v) := by
      simpa using hdg
    exact (hdg'.comp_hasDerivAt 0 hline).sub_const 1
  have hinc := classicalNormal_eventually_pos_of_hasDerivAt hgline
    (by simp [hgp]) hgv
  have ht : Tendsto (fun t : ℝ => p + t • v) (𝓝[>] 0) (𝓝 p) := by
    simpa using hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨t, hte, htg, htr⟩ :=
    (hext.and (hinc.and (ht (c.isOpen_region.mem_nhds hpc)))).exists
  have hout : p + t • v ∈ Kᶜ := by
    intro hin
    have hin' : p + t • v ∈ closure (interior K) := by rwa [← hreg]
    have hgraph : p + t • v ∈ closure c.graphDomain :=
      (hc.closure_inter_eq ▸ (show p + t • v ∈ closure (interior K) ∩ c.region
        from ⟨hin', htr⟩)).1
    have hle := (c.mem_closure_graphDomain_iff _).mp hgraph
    exact (not_lt_of_ge hle) (sub_pos.mp hte)
  have hlt : g (p + t • v) < 1 := by
    rw [← hug (subset_closure hout)]
    exact hupper _ hout
  linarith

/-- Blueprint `lem:flux-identity` (`eq:flux-boundary`), written using
`w = |∇u|` on the boundary through the C² extension `g`. -/
theorem flux_identity_w {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    (hC2 : HasC2Boundary (interior K)) (hconn : IsPreconnected Kᶜ) :
    4 * Real.pi * capacityOf K u =
      ∫ x in frontier K, ‖gradient g x‖ ∂hausdorffMeasure2 3 := by
  rw [flux_identity_of_boundary_C2 hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug,
    ← integral_neg]
  apply setIntegral_congr_fun isClosed_frontier.measurableSet
  intro x hx
  have hgrad := (gradient_eq_neg_norm_smul_normal hK hreg hC1 hR₀ hKR hzero
    hu hh hb hinf hg hug hC2 hconn x hx).1
  have hnorm := hC1.norm_outwardNormal (show x ∈ frontier (interior K) by
    rwa [capacity_frontier_interior hK hreg])
  calc
    -inner ℝ (gradient g x) (hC1.outwardNormal x) =
        -inner ℝ (-‖gradient g x‖ • hC1.outwardNormal x) (hC1.outwardNormal x) :=
      congrArg (fun v => -inner ℝ v (hC1.outwardNormal x)) hgrad
    _ = ‖gradient g x‖ := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]
      simp

end LiquidDrop
