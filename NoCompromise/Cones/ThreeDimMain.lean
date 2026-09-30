module

public import NoCompromise.Cones.SmoothMain
public import NoCompromise.Cones.MinimalGraphEquationMain
public import NoCompromise.Cones.MinimalGraphC2
public import NoCompromise.Cones.SmoothHomogeneous
public import NoCompromise.Cones.HomogeneousMinimalGraph
public import NoCompromise.Cones.AffineOfHessian
public import NoCompromise.Cones.LinkLocal

@[expose] public section

/-! Three-dimensional minimizing cones are halfspaces, from the pointwise
minimal-surface equation for C² weak solutions. -/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ContDiff Gradient
namespace LiquidDrop

/-- The pointwise minimal-surface equation from the weak one (proved separately). -/
def MinimalGraphPointwiseStatement : Prop :=
  ∀ ⦃U : Set (EuclideanSpace ℝ (Fin 2))⦄, IsOpen U → ∀ ⦃f : EuclideanSpace ℝ (Fin 2) → ℝ⦄,
    ContDiffOn ℝ 2 f U →
    (∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      ∫ y, inner ℝ (gradient f y) (gradient φ y) / Real.sqrt (1 + ‖gradient f y‖ ^ 2) = 0) →
    ∀ x ∈ U, LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 2))
      ((fderiv ℝ (fun y => mcFlux (gradient f y)) x :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = 0

/-- A square-root modulus for the derivative supplies the C¹ hypothesis. -/
lemma cone_graph_contDiffOn_one {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hd : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hh : ∀ x ∈ U, ∀ y ∈ U,
      ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ Real.sqrt ‖x - y‖) :
    ContDiffOn ℝ 1 f U := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx => (hd x hx).differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  apply Metric.continuousOn_iff.mpr
  intro x hx ε hε
  refine ⟨ε ^ 2, sq_pos_of_pos hε, fun y hy hyx => ?_⟩
  rw [dist_eq_norm] at hyx ⊢
  exact (hh y hy x hx).trans_lt ((Real.sqrt_lt' hε).2 hyx)

/-- Blueprint `thm:cone-3d`, from `MinimalGraphPointwiseStatement`. -/
theorem cone3d_halfspace_of_pointwise (hpw : MinimalGraphPointwiseStatement)
    {C : Set AmbientSpace} (hC : IsNontrivialMinimizingCone C) :
    ∃ μ : AmbientSpace, ‖μ‖ = 1 ∧ densityOne C = {x | 0 < inner ℝ μ x} := by
  apply cone3d_halfspace_of_locally_flat hC
  intro p hp hp0
  obtain ⟨ν, hν, hνp, hreg⟩ := cone_C1half_graph_of_ne_zero hC hp hp0
  obtain ⟨s, hs, hsp, hs1, f, νΩ, hiff, hcyl, hf8, hfd, _hn, hhol⟩ :=
    hreg (δ := 1) (s₀ := ‖p‖) one_pos (norm_pos_iff.mpr hp0)
  have hC1 : ContDiffOn ℝ 1 f (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4)) :=
    cone_graph_contDiffOn_one isOpen_ball (fun x hx => (hfd x hx).differentiableAt)
      (by simpa only [one_mul] using hhol)
  have hE : IsOmegaMinimal (excessDecayCoordinates C p s ν) 0 := by
    simpa only [zero_mul] using hC.minimizing.isOmegaMinimal.excessDecayCoordinates p hs hs1 ν
  have hgraph : frontier (densityOne (excessDecayCoordinates C p s ν)) ∩ standardCylinder (1 / 4) =
      (fun x => graphAppendN x (f x)) '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4) := by
    ext y
    constructor
    · rintro ⟨hyf, hy⟩
      rw [mem_frontier_densityOne_excessDecayCoordinates C p ν y hs, hiff y hy] at hyf
      exact hyf
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, hcyl x hx⟩
      rw [mem_frontier_densityOne_excessDecayCoordinates C p ν _ hs, hiff _ (hcyl x hx)]
      exact ⟨x, hx, rfl⟩
  have hweak : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 φ →
      HasCompactSupport φ → tsupport φ ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4) →
      ∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2) = 0 := by
    intro φ hφ hcφ hsφ
    exact minimal_graph_weak_equation hE (by norm_num) (by norm_num) hgraph
      (by convert hf8 using 1; norm_num) hC1 hφ hcφ hsφ
  have hC2 : ContDiffOn ℝ 2 f (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8)) := by
    have hh := mc_graph_C2_holder_of_weak_zero (by norm_num : (0 : ℝ) < 1 / 4)
      hC1 hhol (fun φ hφ hcφ hsφ => hweak φ (hφ.of_le (by simp)) hcφ hsφ)
    convert hh.contDiff using 1; norm_num
  have hsmall : ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8) ⊆ ball 0 (1 / 4) :=
    ball_subset_ball (by norm_num)
  have hmse := hpw isOpen_ball hC2 (fun φ hφ hcφ hsφ =>
    hweak φ hφ hcφ (hsφ.trans hsmall))
  have hv : coneVertexBase p ν s ∉ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8) := by
    rw [mem_ball_zero_iff, norm_coneVertexBase hν hνp hs]
    have : (1 : ℝ) ≤ ‖p‖ / s := (le_div_iff₀ hs).2 (by simpa using hsp)
    linarith
  have hhom : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8),
      ∀ᶠ l in nhds (1 : ℝ),
        f (coneVertexBase p ν s + l • (x - coneVertexBase p ν s)) = l * f x := by
    intro x hx
    have hcont : Continuous (fun l : ℝ =>
        graphAppendN (coneVertexBase p ν s + l • (x - coneVertexBase p ν s)) (l * f x)) := by
      unfold graphAppendN
      fun_prop
    have he : ∀ᶠ l in nhds (1 : ℝ),
        graphAppendN (coneVertexBase p ν s + l • (x - coneVertexBase p ν s)) (l * f x) ∈
          standardCylinder (1 / 4) := by
      apply hcont.continuousAt.eventually (isOpen_standardCylinder _ |>.mem_nhds ?_)
      simpa using hcyl x (hsmall hx)
    filter_upwards [he, eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with l hl hl0
    exact cone_graph_homogeneous hC hν hνp hs hiff hcyl (hsmall hx) hl0 hl
  have hessian := hessian_eq_zero_of_homogeneous_minimal isOpen_ball hC2 hv hhom hmse
  have hf0 : f 0 = 0 := by
    have hz : (0 : AmbientSpace) ∈ standardCylinder (1 / 4) := by
      constructor <;> norm_num
    have hp' : p + s • verticalAxisIsometry ν 0 ∈ frontier (densityOne C) := by simpa using hp
    obtain ⟨x, hx, he⟩ := (hiff 0 hz).1 hp'
    have hx0 : x = 0 := by simpa using congrArg (graphProjectionN 2) he
    simpa [hx0] using congrArg (fun y : AmbientSpace => y 2) he
  have ha : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8), f x = fderiv ℝ f 0 x := by
    intro x hx
    simpa [hf0] using affine_of_fderiv_fderiv_eq_zero isOpen_ball (convex_ball _ _)
      hC2 hessian (by simp : (0 : EuclideanSpace ℝ (Fin 2)) ∈ ball 0 (1 / 8)) x hx
  let T : AmbientSpace →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3) -
    (fderiv ℝ f 0).comp (graphProjectionN 2)
  let m : AmbientSpace := (toDual ℝ AmbientSpace).symm T
  have hm (y : AmbientSpace) : inner ℝ m y = y 2 - fderiv ℝ f 0 (graphProjectionN 2 y) :=
    toDual_symm_apply
  have hm0 : m ≠ 0 := by
    intro he
    have hh := hm (graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) 1)
    simp [he] at hh
  refine ⟨s / 8, by positivity, verticalAxisIsometry ν m,
    fun h => hm0 ((verticalAxisIsometry ν).injective (by simpa using h)), ?_⟩
  ext z
  by_cases hz : z ∈ ball p (s / 8)
  · let y : AmbientSpace := (verticalAxisIsometry ν).symm (s⁻¹ • (z - p))
    have hy : ‖y‖ < 1 / 8 := by
      dsimp [y]
      rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_of_nonneg (by positivity)]
      have hdist : ‖z - p‖ < s / 8 := by simpa only [mem_ball, dist_eq_norm] using hz
      calc s⁻¹ * ‖z - p‖ < s⁻¹ * (s / 8) := mul_lt_mul_of_pos_left hdist (inv_pos.2 hs)
        _ = 1 / 8 := by field_simp
    have hyp : graphProjectionN 2 y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8) :=
      mem_ball_zero_iff.mpr ((norm_graphProjectionN_le y).trans_lt hy)
    have hyc : y ∈ standardCylinder (1 / 4) := by
      exact ⟨(norm_graphProjectionN_le y).trans_lt (hy.trans (by norm_num)),
        (abs_last_le_norm y).trans_lt (hy.trans (by norm_num))⟩
    have hzy : p + s • verticalAxisIsometry ν y = z := by
      simp [y, smul_inv_smul₀ hs.ne']
    have hinner : inner ℝ (verticalAxisIsometry ν m) (z - p) = s * inner ℝ m y := by
      have hsub : z - p = s • verticalAxisIsometry ν y := by rw [← hzy]; abel
      rw [hsub, real_inner_smul_right, LinearIsometryEquiv.inner_map_map]
    have heq : z ∈ frontier (densityOne C) ↔ inner ℝ (verticalAxisIsometry ν m) (z - p) = 0 := by
      rw [← hzy, hiff y hyc]
      rw [hzy, hinner, mul_eq_zero, or_iff_right hs.ne', hm, sub_eq_zero]
      constructor
      · rintro ⟨x, hx, he⟩
        have hxp : x = graphProjectionN 2 y := by simpa using congrArg (graphProjectionN 2) he
        have hheight : f x = y 2 := by simpa using congrArg (fun w : AmbientSpace => w 2) he
        rw [← hheight, hxp, ha _ hyp]
      · intro hh
        refine ⟨graphProjectionN 2 y, hsmall hyp, ?_⟩
        rw [ha _ hyp, ← hh]
        exact graphAppendN_projection y
    simp only [mem_inter_iff, mem_ofPred_eq, hz, and_true]
    exact heq
  · simp only [mem_inter_iff, mem_ofPred_eq, hz, and_false]

end LiquidDrop
