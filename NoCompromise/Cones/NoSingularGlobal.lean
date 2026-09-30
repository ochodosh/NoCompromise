module

public import NoCompromise.Cones.NoSingularDefs
public import NoCompromise.DeGiorgi.SmoothBoundary

@[expose] public section

/-!
# Global consequences of regular boundary charts (`prop:no-singular-points`)

If every boundary point of `Ω` is regular (`IsRegularBoundaryPoint`), then `Ω` has a `C¹`
boundary, `Ω` is regular open, a bounded such `Ω` has finitely many boundary components, and
the perimeter of an open such `Ω` is the Hausdorff area of its topological boundary.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace LiquidDrop

variable {Ω : Set AmbientSpace}

/-- A function differentiable on a ball with `1/2`-Hölder derivative is `C¹` there. -/
lemma contDiffOn_one_of_fderiv_holder {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K r : ℝ}
    (hd : ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) r, DifferentiableAt ℝ f x')
    (hh : ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) r,
      ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) r,
        ‖fderiv ℝ f x' - fderiv ℝ f y'‖ ≤ K * Real.sqrt ‖x' - y'‖) :
    ContDiffOn ℝ 1 f (ball 0 r) := by
  have h1 : ContDiffOn ℝ ((0 : ℕ∞) + 1 : WithTop ℕ∞) f (ball 0 r) := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    refine ⟨fun x hx => (hd x hx).differentiableWithinAt, by simp, ?_⟩
    rw [WithTop.coe_zero, contDiffOn_zero]
    intro x hx
    have hlim : Tendsto (fun y => K * Real.sqrt ‖y - x‖) (𝓝[ball 0 r] x) (𝓝 0) := by
      have hc : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => K * Real.sqrt ‖y - x‖) := by
        fun_prop
      have h0 := hc.tendsto x
      simp only [sub_self, norm_zero, Real.sqrt_zero, mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hh y hy x hx
  simpa using h1

/-- Chart inversion: `x + s • Q (s⁻¹ • Q.symm (z - x)) = z`. -/
lemma chart_apply_inv (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (x z : AmbientSpace) {s : ℝ}
    (hs : s ≠ 0) : x + s • Q (s⁻¹ • Q.symm (z - x)) = z := by
  simp [hs]

lemma chart_inv_apply (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (x y : AmbientSpace) {s : ℝ}
    (hs : s ≠ 0) : s⁻¹ • Q.symm (x + s • Q y - x) = y := by
  simp [hs]

lemma continuous_chart_inv (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (x : AmbientSpace) (s : ℝ) :
    Continuous fun z : AmbientSpace => s⁻¹ • Q.symm (z - x) :=
  (Q.symm.continuous.comp (continuous_sub_right x)).const_smul s⁻¹

lemma zero_mem_standardCylinder : (0 : AmbientSpace) ∈ standardCylinder (1 / 4) := by
  refine ⟨?_, ?_⟩ <;> norm_num

lemma graphAppendN_two (x' : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : graphAppendN x' t 2 = t :=
  graphAppendN_last x' t

lemma graphAppendN_mem_standardCylinder {x' : EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    (hx' : ‖x'‖ < 1 / 4) (ht : |t| < 1 / 4) :
    graphAppendN x' t ∈ standardCylinder (1 / 4) := by
  refine ⟨?_, ?_⟩
  · rwa [graphProjectionN_append]
  · rwa [graphAppendN_two]

/-- Regular boundary charts give a `C¹` boundary in the sense of `HasC1Boundary`. -/
theorem hasC1Boundary_of_isRegularBoundaryPoint
    (hreg : ∀ x ∈ frontier Ω, IsRegularBoundaryPoint Ω x) : HasC1Boundary Ω := by
  apply hasC1Boundary_of_local_graphs
  intro x hx
  obtain ⟨ν, s, K, f, -, hs, -, hd, hh, hin, -⟩ := hreg x hx
  have hs0 : s ≠ 0 := hs.ne'
  set Q := verticalAxisIsometry ν
  let a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace :=
    Q.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ AmbientSpace x)
  have ha : ∀ z, a.symm z = Q.symm (z - x) := by
    intro z
    apply a.injective
    rw [a.apply_symm_apply]
    simp [a]
  have hC := contDiffOn_one_of_fderiv_holder hd hh
  have hmaps : MapsTo (fun w' : EuclideanSpace ℝ (Fin 2) => s⁻¹ • w') (ball 0 (s / 4))
      (ball 0 (1 / 4)) := by
    intro w' hw'
    rw [mem_ball_zero_iff] at hw' ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
    calc s⁻¹ * ‖w'‖ < s⁻¹ * (s / 4) := mul_lt_mul_of_pos_left hw' (inv_pos.2 hs)
      _ = 1 / 4 := by field_simp
  refine ⟨a, fun w' => s * f (s⁻¹ • w'), ball 0 (s / 4),
    (fun z => s⁻¹ • Q.symm (z - x)) ⁻¹' standardCylinder (1 / 4), isOpen_ball,
    contDiffOn_const.mul (hC.comp (contDiff_const_smul s⁻¹).contDiffOn hmaps), ?_,
    (isOpen_standardCylinder _).preimage (continuous_chart_inv Q x s), ?_, ?_⟩
  · rw [ha, sub_self, map_zero, map_zero]
    exact mem_ball_self (by positivity)
  · simpa only [mem_preimage, sub_self, map_zero, smul_zero] using zero_mem_standardCylinder
  · intro z hz
    obtain ⟨y, rfl⟩ : ∃ y, z = x + s • Q y := ⟨_, (chart_apply_inv Q x z hs0).symm⟩
    have hy : y ∈ standardCylinder (1 / 4) := by
      simpa only [mem_preimage, chart_inv_apply Q x y hs0] using hz
    have hsy : a.symm (x + s • Q y) = s • y := by
      rw [ha, add_sub_cancel_left, map_smul, LinearIsometryEquiv.symm_apply_apply]
    rw [hin y hy, hsy]
    simp only [map_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul, PiLp.smul_apply,
      smul_eq_mul]
    exact (mul_lt_mul_iff_of_pos_left hs).symm

/-- A domain all of whose boundary points are regular is regular open. -/
theorem interior_closure_eq_of_isRegularBoundaryPoint (hΩ : IsOpen Ω)
    (hreg : ∀ x ∈ frontier Ω, IsRegularBoundaryPoint Ω x) : interior (closure Ω) = Ω := by
  refine Subset.antisymm ?_ (hΩ.subset_interior_iff.2 subset_closure)
  intro z hz
  by_contra hzΩ
  have hzf : z ∈ frontier Ω := by
    rw [frontier, hΩ.interior_eq]
    exact ⟨interior_subset hz, hzΩ⟩
  obtain ⟨ν, s, K, f, -, hs, -, hd, -, hin, hfr⟩ := hreg z hzf
  have hs0 : s ≠ 0 := hs.ne'
  set Q := verticalAxisIsometry ν
  have hcont : ContinuousOn f (ball 0 (1 / 4)) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hf0 : f 0 = 0 := by
    have h := (hfr 0 zero_mem_standardCylinder).1 (by simpa using hzf)
    simpa using h.symm
  let V := standardCylinder (1 / 4) ∩ (fun y => f (graphProjectionN 2 y) - y 2) ⁻¹' Iio 0
  have hV : IsOpen V := by
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_standardCylinder _) isOpen_Iio
    refine ContinuousOn.sub (hcont.comp (graphProjectionN 2).continuous.continuousOn
      fun y hy => mem_ball_zero_iff.2 hy.1) ?_
    exact (EuclideanSpace.proj (2 : Fin 3)).continuous.continuousOn
  let ψ := fun w : AmbientSpace => s⁻¹ • Q.symm (w - z)
  have hO : IsOpen (ψ ⁻¹' V) := hV.preimage (continuous_chart_inv Q z s)
  have hdisj : Disjoint (ψ ⁻¹' V) (closure Ω) := by
    refine Disjoint.closure_right (Set.disjoint_left.2 fun w hw hwΩ => ?_) hO
    have h := (hin (ψ w) hw.1).1 (by rwa [chart_apply_inv Q z w hs0])
    have h2 : f (graphProjectionN 2 (ψ w)) - ψ w 2 < 0 := hw.2
    linarith
  let c : ℝ → AmbientSpace := fun t => z + s • Q (graphAppendN 0 t)
  have hc : Continuous c := by
    have : Continuous fun t : ℝ => graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) t := by
      unfold graphAppendN
      fun_prop
    exact continuous_const.add ((Q.continuous.comp this).const_smul s)
  have hc0 : c 0 = z := by simp [c, graphAppendN]
  have hlim : Tendsto c (𝓝[>] 0) (𝓝 z) := hc0 ▸ (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), c t ∈ closure Ω :=
    hlim.eventually (mem_interior_iff_mem_nhds.1 hz)
  obtain ⟨t, htc, ht⟩ := (hev.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))).exists
  have hψc : ψ (c t) = graphAppendN 0 t := chart_inv_apply Q z _ hs0
  have hmem : c t ∈ ψ ⁻¹' V := by
    rw [mem_preimage, hψc]
    refine ⟨graphAppendN_mem_standardCylinder (by simp) ?_, ?_⟩
    · rw [abs_of_pos ht.1]; exact ht.2
    · show f (graphProjectionN 2 (graphAppendN 0 t)) - graphAppendN 0 t 2 < 0
      rw [graphProjectionN_append, graphAppendN_two, hf0]
      linarith [ht.1]
  exact Set.disjoint_left.1 hdisj hmem htc

/-- Every point of the boundary has a preconnected open neighbourhood in the boundary. -/
lemma exists_isOpen_isPreconnected_frontier_of_isRegularBoundaryPoint
    (hreg : ∀ x ∈ frontier Ω, IsRegularBoundaryPoint Ω x) (p : frontier Ω) :
    ∃ U : Set (frontier Ω), IsOpen U ∧ p ∈ U ∧ IsPreconnected U := by
  obtain ⟨x, hx⟩ := p
  obtain ⟨ν, s, K, f, -, hs, hf8, hd, -, -, hfr⟩ := hreg x hx
  have hs0 : s ≠ 0 := hs.ne'
  set Q := verticalAxisIsometry ν
  let ψ := fun w : AmbientSpace => s⁻¹ • Q.symm (w - x)
  let W := ψ ⁻¹' standardCylinder (1 / 4)
  have hW : IsOpen W := (isOpen_standardCylinder _).preimage (continuous_chart_inv Q x s)
  let Γ := fun x' : EuclideanSpace ℝ (Fin 2) => x + s • Q (graphAppendN x' (f x'))
  have hcont : ContinuousOn f (ball 0 (1 / 4)) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hΓ : ContinuousOn Γ (ball 0 (1 / 4)) := by
    have h1 : ContinuousOn (fun x' : EuclideanSpace ℝ (Fin 2) => graphAppendN x' (f x'))
        (ball 0 (1 / 4)) := by
      unfold graphAppendN
      exact (graphBaseN 2).continuous.continuousOn.add (hcont.smul continuousOn_const)
    exact continuousOn_const.add ((Q.continuous.comp_continuousOn h1).const_smul s)
  have heq : frontier Ω ∩ W = Γ '' ball 0 (1 / 4) := by
    ext w
    constructor
    · rintro ⟨hwf, hwW⟩
      have hw' : x + s • Q (ψ w) = w := chart_apply_inv Q x w hs0
      have hy2 := (hfr (ψ w) hwW).1 (by rw [hw']; exact hwf)
      refine ⟨graphProjectionN 2 (ψ w), mem_ball_zero_iff.2 hwW.1, ?_⟩
      change x + s • Q (graphAppendN (graphProjectionN 2 (ψ w)) (f (graphProjectionN 2 (ψ w))))
        = w
      rw [← hy2]
      exact (congrArg (fun y => x + s • Q y) (graphAppendN_projection (ψ w))).trans hw'
    · rintro ⟨x', hx', rfl⟩
      have hx'4 : ‖x'‖ < 1 / 4 := mem_ball_zero_iff.1 hx'
      have hy : graphAppendN x' (f x') ∈ standardCylinder (1 / 4) :=
        graphAppendN_mem_standardCylinder hx'4 (by linarith [hf8 x' hx'])
      refine ⟨(hfr _ hy).2 (by rw [graphAppendN_two, graphProjectionN_append]), ?_⟩
      change ψ (x + s • Q (graphAppendN x' (f x'))) ∈ standardCylinder (1 / 4)
      rw [show ψ (x + s • Q (graphAppendN x' (f x'))) = graphAppendN x' (f x') from
        chart_inv_apply Q x _ hs0]
      exact hy
  refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, ?_, ?_⟩
  · change ψ x ∈ standardCylinder (1 / 4)
    simpa only [ψ, sub_self, map_zero, smul_zero] using zero_mem_standardCylinder
  · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe, heq]
    exact (convex_ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4)).isPreconnected.image Γ hΓ

/-- A bounded domain with regular boundary charts has finitely many boundary components. -/
theorem finite_connectedComponents_frontier_of_isRegularBoundaryPoint
    (hb : Bornology.IsBounded Ω)
    (hreg : ∀ x ∈ frontier Ω, IsRegularBoundaryPoint Ω x) :
    Finite (ConnectedComponents (frontier Ω)) := by
  have hc : IsCompact (frontier Ω) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have : CompactSpace (frontier Ω) := isCompact_iff_compactSpace.mp hc
  have : DiscreteTopology (ConnectedComponents (frontier Ω)) := by
    rw [ConnectedComponents.discreteTopology_iff]
    intro q
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨U, hUo, hpU, hUc⟩ :=
      exists_isOpen_isPreconnected_frontier_of_isRegularBoundaryPoint hreg p
    refine ⟨U, ?_, hUo, hpU⟩
    rw [connectedComponent_eq hp]
    exact hUc.subset_connectedComponent hpU
  exact finite_of_compact_of_discrete

/-- For an open domain with regular boundary charts, perimeter is boundary area. -/
theorem perimeter_eq_of_isRegularBoundaryPoint (hΩ : IsOpen Ω)
    (hreg : ∀ x ∈ frontier Ω, IsRegularBoundaryPoint Ω x) :
    perimeter Ω = hausdorffMeasure2 3 (frontier Ω) :=
  (hasC1Boundary_of_isRegularBoundaryPoint hreg).perimeter_eq_boundaryArea hΩ

end LiquidDrop
