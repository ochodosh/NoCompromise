module

public import NoCompromise.Area.SmoothSurface

@[expose] public section

/-!
# Tangent planes of compact embedded C¹ surfaces

In a rotated graph chart `S ∩ U = U ∩ R '' (graphMap f '' Ω)` the classical (chart-independent)
tangent cone `tangentConeAt ℝ S x` at a point `x = R (graphMap f y)`, `y ∈ Ω`, is the image of the
differential of the chart `z ↦ R (graphMap f z)` at `y`. Consequently the Lipschitz charts of
`IsCompactC1EmbeddedSurface.exists_local_lipschitz_chart` can be chosen so that, at every interior
point of their compact domain, they are differentiable with injective differential whose range is
the classical tangent plane of `S`.
-/

noncomputable section
open MeasureTheory Set Function Metric Filter
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Orthogonal projection of three-space onto the base plane of a graph. -/
def graphBaseProjection : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.proj (0 : Fin 3)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (EuclideanSpace.proj (1 : Fin 3)).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

@[simp] lemma graphBaseProjection_graphMap (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) : graphBaseProjection (graphMap f z) = z := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [graphBaseProjection]

/-- Derivative of a rotated graph chart at a differentiability point of the height. -/
lemma hasFDerivAt_rotated_graphMap
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {y : EuclideanSpace ℝ (Fin 2)}
    (hf : DifferentiableAt ℝ f y) :
    HasFDerivAt (fun z => R (graphMap f z))
      ((R.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)).comp
        (fderiv ℝ (graphMap f) y)) y :=
  R.toContinuousLinearEquiv.hasFDerivAt.comp y
    (hasFDerivAt_graphMap hf).differentiableAt.hasFDerivAt

/-- The tangent cone of a rotated graph over any base set lies in the image of the differential
of the chart. Only differentiability of the height at the base point is used. -/
lemma tangentConeAt_rotated_graph_subset
    {R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {T : Set (EuclideanSpace ℝ (Fin 2))}
    {y : EuclideanSpace ℝ (Fin 2)} (hf : DifferentiableAt ℝ f y) :
    tangentConeAt ℝ (R '' (graphMap f '' T)) (R (graphMap f y)) ⊆
      range (fun v => R (fderiv ℝ (graphMap f) y v)) := by
  intro w hw
  obtain ⟨α, l, hl, c, d, hd₀, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hw
  set P : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    graphBaseProjection.comp
      (R.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    with hPdef
  have hP : ∀ z, P (R (graphMap f z)) = z := by
    intro z
    simp [P]
  set Φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) := fun z => R (graphMap f z)
    with hΦdef
  have hΦ := hasFDerivAt_rotated_graphMap R hf
  have hd : ∀ᶠ n in l, d n = Φ (y + P (d n)) - Φ y := by
    filter_upwards [hds] with n hn
    obtain ⟨_, ⟨z, _, rfl⟩, hz⟩ := hn
    have hzP : y + P (d n) = z := by
      have := congrArg P hz
      rw [map_add, hP, hP] at this
      exact this.symm
    rw [hzP]
    change d n = R (graphMap f z) - R (graphMap f y)
    rw [hz]
    abel
  have hPd : Tendsto (fun n => P (d n)) l (𝓝 0) := by
    simpa [Function.comp_def] using (P.continuous.tendsto 0).comp hd₀
  have hPcd : Tendsto (fun n => c n • P (d n)) l (𝓝 (P w)) := by
    simpa [Function.comp_def, map_smul] using (P.continuous.tendsto w).comp hcd
  have hlim := hΦ.hasFDerivWithinAt (s := univ).lim hPd
    (Eventually.of_forall fun _ => mem_univ _) hPcd
  have h2 : Tendsto (fun n => c n • (Φ (y + P (d n)) - Φ y)) l (𝓝 w) :=
    hcd.congr' (hd.mono fun n hn => by
      change c n • d n = c n • (Φ (y + P (d n)) - Φ y)
      exact congrArg (c n • ·) hn)
  have := tendsto_nhds_unique h2 hlim
  exact ⟨P w, this.symm⟩

/-- The image of the differential of a rotated graph chart over an open base lies in the tangent
cone of the rotated graph. -/
lemma range_subset_tangentConeAt_rotated_graph
    {R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin 2))}
    {y : EuclideanSpace ℝ (Fin 2)} (hΩ : IsOpen Ω) (hy : y ∈ Ω) (hf : DifferentiableAt ℝ f y) :
    range (fun v => R (fderiv ℝ (graphMap f) y v)) ⊆
      tangentConeAt ℝ (R '' (graphMap f '' Ω)) (R (graphMap f y)) := by
  rintro _ ⟨v, rfl⟩
  have hmaps := ((hasFDerivAt_rotated_graphMap R hf).hasFDerivWithinAt (s := Ω)).mapsTo_tangent_cone
  rw [tangentConeAt_of_mem_nhds (hΩ.mem_nhds hy)] at hmaps
  have h' := hmaps (mem_univ v)
  rw [image_image]
  exact h'

/-- **Classical tangent plane in a rotated graph chart.** If `S ∩ U = U ∩ R '' (graphMap f '' Ω)`
with `U`, `Ω` open, `y ∈ Ω`, `R (graphMap f y) ∈ U`, and `f` differentiable at `y`, then the
tangent cone of `S` at `R (graphMap f y)` is the range of the differential of the chart. -/
theorem tangentConeAt_eq_range_of_graphChart
    {S U : Set (EuclideanSpace ℝ (Fin 3))}
    {R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hSU : S ∩ U = U ∩ R '' (graphMap f '' Ω))
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Ω) (hyU : R (graphMap f y) ∈ U)
    (hf : DifferentiableAt ℝ f y) :
    tangentConeAt ℝ S (R (graphMap f y)) = range (fun v => R (fderiv ℝ (graphMap f) y v)) := by
  have hUn := hU.mem_nhds hyU
  rw [← tangentConeAt_inter_nhds hUn, hSU, inter_comm, tangentConeAt_inter_nhds hUn]
  exact (tangentConeAt_rotated_graph_subset hf).antisymm
    (range_subset_tangentConeAt_rotated_graph hΩ hy hf)

/-- The C¹ form of `tangentConeAt_eq_range_of_graphChart`, with the chart data of
`IsCompactC1EmbeddedSurface`. -/
theorem tangentConeAt_eq_range_of_C1GraphChart
    {S U : Set (EuclideanSpace ℝ (Fin 3))}
    {R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hSU : S ∩ U = U ∩ R '' (graphMap f '' Ω))
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Ω) (hyU : R (graphMap f y) ∈ U) :
    tangentConeAt ℝ S (R (graphMap f y)) = range (fun v => R (fderiv ℝ (graphMap f) y v)) :=
  tangentConeAt_eq_range_of_graphChart hU hΩ hSU hy hyU
    ((hf.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy))

/-- **Tangent clause of the Lipschitz charts (chartwise convention).** Near each of its points a
compact embedded C¹ surface is covered by a global Lipschitz image `g '' K` of a compact planar set
with `g '' K ⊆ S`; the point lies in `g '' interior K`, and at every interior point `z` of `K` the
chart is differentiable with injective differential whose range is the classical tangent cone of
`S` at `g z`. -/
lemma IsCompactC1EmbeddedSurface.exists_local_lipschitz_chart_tangent
    {S : Set (EuclideanSpace ℝ (Fin 3))} (h : IsCompactC1EmbeddedSurface S)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ S) :
    ∃ W : Set (EuclideanSpace ℝ (Fin 3)), IsOpen W ∧ x ∈ W ∧
      ∃ (g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (L : ℝ≥0)
        (K : Set (EuclideanSpace ℝ (Fin 2))),
        LipschitzWith L g ∧ IsCompact K ∧ S ∩ W ⊆ g '' K ∧ g '' K ⊆ S ∧
        x ∈ g '' interior K ∧
        ∀ z ∈ interior K, DifferentiableAt ℝ g z ∧ Injective (fderiv ℝ g z) ∧
          range (fderiv ℝ g z) = tangentConeAt ℝ S (g z) := by
  obtain ⟨U, R, Ω, f, hU, hxU, hΩ, hf, hSU⟩ := h.2 x hx
  have hxR : x ∈ U ∩ R '' (graphMap f '' Ω) := hSU ▸ ⟨hx, hxU⟩
  obtain ⟨_, ⟨_, ⟨p, hpΩ, rfl⟩, rfl⟩⟩ := hxR
  have hfd : ∀ z ∈ Ω, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn one_ne_zero z hz).differentiableAt (hΩ.mem_nhds hz)
  have hcont : ContinuousAt (fun z => R (graphMap f z)) p :=
    (hasFDerivAt_rotated_graphMap R (hfd p hpΩ)).continuousAt
  obtain ⟨C, t, ht, hCt⟩ := (hf.contDiffAt (hΩ.mem_nhds hpΩ)).exists_lipschitzOnWith
  obtain ⟨r, hr, hrsub⟩ := (nhds_basis_closedBall (x := p)).mem_iff.mp
    (Filter.inter_mem (Filter.inter_mem ht (hΩ.mem_nhds hpΩ))
      (hcont.preimage_mem_nhds (hU.mem_nhds hxU)))
  obtain ⟨g, hg, hfg⟩ := (hCt.mono fun y hy => (hrsub hy).1.1).extend_real
  have hgf : ∀ z ∈ closedBall p r, R (graphMap g z) = R (graphMap f z) := fun z hz => by
    simp only [graphMap, hfg hz]
  refine ⟨U ∩ ball (R (graphMap f p)) r, hU.inter isOpen_ball, ⟨hxU, mem_ball_self hr⟩,
    fun q => R (graphMap g q), 1 * (1 + C), closedBall p r,
    R.isometry.lipschitzWith.comp (lipschitzWith_graphMap hg), isCompact_closedBall p r,
    ?_, ?_, ?_, ?_⟩
  · rintro y ⟨hyS, hyU, hyB⟩
    have hyR : y ∈ U ∩ R '' (graphMap f '' Ω) := hSU ▸ ⟨hyS, hyU⟩
    obtain ⟨_, ⟨_, ⟨q, _, rfl⟩, rfl⟩⟩ := hyR
    have hqp : dist q p ≤ r := by
      have h1 := (antilipschitzWith_graphMap f).le_mul_dist q p
      rw [mem_ball, R.dist_map] at hyB
      simp only [NNReal.coe_one, one_mul] at h1
      linarith
    exact ⟨q, mem_closedBall.mpr hqp, hgf q (mem_closedBall.mpr hqp)⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzS : R (graphMap f z) ∈ S ∩ U :=
      hSU ▸ ⟨(hrsub hz).2, graphMap f z, ⟨z, (hrsub hz).1.2, rfl⟩, rfl⟩
    change R (graphMap g z) ∈ S
    rw [hgf z hz]
    exact hzS.1
  · rw [interior_closedBall p hr.ne']
    exact ⟨p, mem_ball_self hr, hgf p (mem_closedBall_self hr.le)⟩
  · intro z hz
    rw [interior_closedBall p hr.ne'] at hz
    have hzK : z ∈ closedBall p r := ball_subset_closedBall hz
    have hzΩ : z ∈ Ω := (hrsub hzK).1.2
    have hzU : R (graphMap f z) ∈ U := (hrsub hzK).2
    have hev : (fun q => R (graphMap g q)) =ᶠ[𝓝 z] fun q => R (graphMap f q) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun q hq =>
        hgf q (ball_subset_closedBall hq)
    have hgΦ := (hasFDerivAt_rotated_graphMap R (hfd z hzΩ)).congr_of_eventuallyEq hev
    refine ⟨hgΦ.differentiableAt, ?_, ?_⟩
    · rw [hgΦ.fderiv]
      have hinj : Injective (fderiv ℝ (graphMap f) z) := by
        rw [fderiv_graphMap (hfd z hzΩ)]
        exact graphTangentMap_injective _
      exact R.injective.comp hinj
    · rw [hgΦ.fderiv]
      change range (fun v => R (fderiv ℝ (graphMap f) z v)) = tangentConeAt ℝ S (R (graphMap g z))
      rw [hgf z hzK, tangentConeAt_eq_range_of_graphChart hU hΩ hSU hzΩ hzU (hfd z hzΩ)]

end LiquidDrop
