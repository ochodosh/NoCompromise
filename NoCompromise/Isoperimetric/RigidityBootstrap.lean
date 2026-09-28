import NoCompromise.Isoperimetric.RigidityEulerLagrange
import NoCompromise.Stationary.MinimizerC1Holder
import NoCompromise.Stationary.BootstrapGlobal
import NoCompromise.Stationary.BootstrapC3Global

/-!
# The regularity bootstrap for a perimeter minimiser

Blueprint `thm:isoperimetric-rigidity`, Step 2: the bootstrap of `sec:bootstrap` with
`v_Ω` replaced by `0`. The `C^{1,1/2}` boundary comes from `thm:eps-regularity` through the
unit-scale `ω`-minimality of Step 1; the graph equation of a perimeter minimiser has the
constant forcing `2P / (3V)`, so the `C^{2,β}` and `C³` steps of chapter 28 apply verbatim.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ENNReal Gradient RealInnerProductSpace
namespace LiquidDrop

/-! ### `C^{1,1/2}` boundary from `ω`-minimality -/

/-- An open `C¹` `ω`-minimal set is exactly its density-one representative, also after a rigid
change of coordinates. -/
theorem HasC1Boundary.densityOne_preimage_eq_perim {E : Set AmbientSpace} {ω : ℝ}
    (h : HasC1Boundary E) (hE : IsOpen E) (hω : IsOmegaMinimal E ω)
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    densityOne (a ⁻¹' E) = a ⁻¹' E := by
  rw [densityOne_preimage_affineIsometry, h.densityOne_eq hE hω]

/-- Rigid coordinates identify the two boundaries of an open `C¹` `ω`-minimal set. -/
theorem HasC1Boundary.frontier_densityOne_preimage_eq_perim {E : Set AmbientSpace} {ω : ℝ}
    (h : HasC1Boundary E) (hE : IsOpen E) (hω : IsOmegaMinimal E ω)
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    frontier (densityOne (a ⁻¹' E)) = a ⁻¹' frontier E := by
  rw [frontier_densityOne_preimage_affineIsometry, h.densityOne_eq hE hω]

/-- A rigid motion centred at a boundary point of an open `C¹` `ω`-minimal set aligns the
chart normal with the vertical axis and makes the ε-regularity excess hypothesis hold at all
small radii (the proof of `MinimizerRep.exists_small_excess_rigid`). -/
theorem HasC1Boundary.exists_small_excess_rigid_perim {E : Set AmbientSpace} {ω : ℝ}
    (h : HasC1Boundary E) (hE : IsOpen E) (hω : IsOmegaMinimal E ω)
    {p : AmbientSpace} (hp : p ∈ frontier E) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : C1BoundaryChart, c.IsChartFor E ∧ p ∈ c.region ∧
      ∃ a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace,
        a 0 = p ∧ a.linearIsometryEquiv (EuclideanSpace.single 2 1) = c.outwardNormal p ∧
        ∃ hω' : IsOmegaMinimal (a ⁻¹' E) ω,
          (0 : AmbientSpace) ∈ frontier (densityOne (a ⁻¹' E)) ∧
          ∃ ρ > 0, ρ ≤ 1 ∧ ∀ r, 0 < r → r ≤ ρ →
            cylindricalExcess (a ⁻¹' E) hω'.locallyFinite hω'.nullMeasurable 0 r
              (EuclideanSpace.single 2 1) + ω * r ≤ ε := by
  obtain ⟨c, hc, hpc⟩ := h p hp
  let Q := verticalAxisIsometry (c.outwardNormal p)
  let a := Q.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ p)
  have ha : a 0 = p := by simp [a]
  have hlin : a.linearIsometryEquiv (EuclideanSpace.single 2 1) = c.outwardNormal p := by
    change Q (EuclideanSpace.single 2 1) = c.outwardNormal p
    exact verticalAxisIsometry_apply_vertical (c.norm_outwardNormal p)
  have hF := hω.preimage_affineIsometry a
  have he : excessDecayCoordinates E p 1 (c.outwardNormal p) = a ⁻¹' E := by
    ext y
    simp [excessDecayCoordinates, blowupSet, a, Q, add_comm]
  obtain ⟨ρ, hρ, hρ1, hsmall⟩ := hc.exists_small_excess h hE hω hpc hε
  have h0 : (0 : AmbientSpace) ∈ frontier (densityOne (a ⁻¹' E)) := by
    rw [h.frontier_densityOne_preimage_eq_perim hE hω, mem_preimage, ha]
    exact hp
  refine ⟨c, hc, hpc, a, ha, hlin, hF, h0, ρ, hρ, hρ1, ?_⟩
  intro r hr hrρ
  have hexc := cylindricalExcess_excessDecayCoordinates hω p (c.outwardNormal p)
    (r := 1) zero_lt_one le_rfl r (EuclideanSpace.single 2 1)
  simp only [he, one_mul, verticalAxisIsometry_apply_vertical (c.norm_outwardNormal p)] at hexc
  rw [hexc]
  exact hsmall r hr hrρ

/-- ε-regularity makes a chart normal of an open `C¹` `ω`-minimal set one-half Hölder on the
boundary near its centre (the proof of `MinimizerRep.exists_chart_normal_holder`). -/
theorem HasC1Boundary.exists_chart_normal_holder_perim {E : Set AmbientSpace} {ω : ℝ}
    (h : HasC1Boundary E) (hE : IsOpen E) (hω₀ : IsOmegaMinimal E ω)
    {p : AmbientSpace} (hp : p ∈ frontier E) :
    ∃ c : C1BoundaryChart, c.IsChartFor E ∧ p ∈ c.region ∧
      ∃ δ > 0, ball p δ ⊆ c.region ∧ ∃ M ≥ 0,
        ∀ x ∈ frontier E ∩ ball p δ, ∀ y ∈ frontier E ∩ ball p δ,
          ‖c.outwardNormal x - c.outwardNormal y‖ ≤ M * Real.sqrt ‖x - y‖ := by
  obtain ⟨ε, hε, C, hC, hreg⟩ := eps_regularity
  obtain ⟨c, hc, hpc, a, ha, _, hω, h0, r, hr, hr1, hsmall⟩ :=
    h.exists_small_excess_rigid_perim hE hω₀ hp hε
  obtain ⟨f, ν, _, _, _, _, _, hred, hhold⟩ :=
    hreg (a ⁻¹' E) ω hω r h0 hr hr1 (hsmall r hr le_rfl)
  have hD := h.preimage_affineIsometry a
  have ho := hE.preimage a.continuous
  have hdeq : densityOne (a ⁻¹' E) = a ⁻¹' E := h.densityOne_preimage_eq_perim hE hω₀ a
  have hrbeq := hD.reducedBoundary_eq_frontier ho hω
  obtain ⟨t, ht, htreg⟩ := Metric.mem_nhds_iff.mp (c.isOpen_region.mem_nhds hpc)
  let δ := min t (r / 4)
  have hδ : 0 < δ := lt_min ht (by positivity)
  have hδreg : ball p δ ⊆ c.region :=
    (ball_subset_ball (min_le_left _ _)).trans htreg
  let X := cylindricalExcess (a ⁻¹' E) hω.locallyFinite hω.nullMeasurable 0 r
    (EuclideanSpace.single 2 1) + ω * r
  let M := C * Real.sqrt X / Real.sqrt r
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpoint (x : AmbientSpace) (hx : x ∈ frontier E ∩ ball p δ) :
      a.symm x ∈ frontier (densityOne (a ⁻¹' E)) ∩ standardCylinder (r / 4) := by
    refine ⟨?_, ?_⟩
    · rw [h.frontier_densityOne_preimage_eq_perim hE hω₀]
      simpa only [mem_preimage, a.apply_symm_apply] using hx.1
    · rw [standardCylinder_eq_cylinder]
      apply ball_subset_cylinder 0 (r / 4) (by simp)
      have hd : dist (a.symm x) 0 = dist x p := by
        rw [← a.dist_map, a.apply_symm_apply, ha]
      rw [mem_ball, hd]
      exact (mem_ball.mp hx.2).trans_le (min_le_right _ _)
  have hnormal (x : AmbientSpace) (hx : x ∈ frontier E ∩ ball p δ) :
      ν (a.symm x) = (c.preimage a).outwardNormal (a.symm x) := by
    have hxp := hpoint x hx
    have hxr : a.symm x ∈ reducedBoundary (a ⁻¹' E) hω.locallyFinite hω.nullMeasurable := by
      rw [hrbeq]
      simpa only [hdeq] using hxp.1
    exact (hred _ ⟨hxr, hxp.2⟩).trans
      ((hc.preimage a).reduced_normal_eq hD ho hω.locallyFinite hxr
        (by simpa only [C1BoundaryChart.preimage, mem_preimage, a.apply_symm_apply]
            using hδreg hx.2))
  refine ⟨c, hc, hpc, δ, hδ, hδreg, M, hM, ?_⟩
  intro x hx y hy
  have hh := hhold _ (hpoint x hx) _ (hpoint y hy)
  rw [hnormal x hx, hnormal y hy, c.outwardNormal_preimage, c.outwardNormal_preimage,
    a.apply_symm_apply, a.apply_symm_apply, ← map_sub, a.linearIsometryEquiv.symm.norm_map] at hh
  have hdist : ‖a.symm x - a.symm y‖ = ‖x - y‖ := by
    simpa only [dist_eq_norm] using a.symm.dist_map x y
  rw [hdist, Real.sqrt_div (norm_nonneg _)] at hh
  calc
    _ ≤ C * (Real.sqrt ‖x - y‖ / Real.sqrt r) * Real.sqrt X := hh
    _ = M * Real.sqrt ‖x - y‖ := by dsimp [M]; ring

/-- An open `C¹` `ω`-minimal set has `C^{1,1/2}` boundary, by `thm:eps-regularity`. -/
theorem HasC1Boundary.hasC1HolderBoundary_of_isOmegaMinimal {E : Set AmbientSpace} {ω : ℝ}
    (h : HasC1Boundary E) (hE : IsOpen E) (hω : IsOmegaMinimal E ω) :
    HasC1HolderBoundary (1 / 2) E := by
  intro p hp
  obtain ⟨c, hc, hpc, δ, hδ, hδreg, M, hM, hhold⟩ := h.exists_chart_normal_holder_perim hE hω hp
  exact ⟨c, hc, hpc, hc.height_hasC1HolderOn_of_normal_holder hp hpc hδ hδreg hM hhold⟩

/-- Blueprint `thm:isoperimetric-rigidity`, Step 2: a fixed-volume perimeter minimiser with
open `C¹` representative has `C^{1,1/2}` boundary. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.hasC1HolderBoundary {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω) :
    HasC1HolderBoundary (1 / 2) Ω :=
  hC1.hasC1HolderBoundary_of_isOmegaMinimal hΩo (hmin.isOmegaMinimal_explicit hV)

/-! ### Constant forcing -/

/-- A constant function is `C^{1,α}` on every set. -/
lemma hasC1HolderOn_const_perim {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (b : F) (U : Set E) :
    HasC1HolderOn α (fun _ : E => b) U := by
  refine ⟨contDiffOn_const, ?_, ?_⟩
  · apply HasFiniteHolderNormOn.of_bounds (A := ‖b‖) (B := 0) (norm_nonneg _) le_rfl
    · intro x _
      exact le_rfl
    · intro x _ y _
      simp
  · apply HasFiniteHolderNormOn.of_bounds (A := 0) (B := 0) le_rfl le_rfl
    · intro x _
      simp
    · intro x _ y _
      simp

/-! ### The `C^{2,β}` step -/

/-- The graph point over the base point of a chart through `p` is `p`. -/
lemma C1BoundaryChart.IsChartFor.placement_graph_base_perim {E : Set AmbientSpace}
    {c : C1BoundaryChart} (hc : c.IsChartFor E) {p : AmbientSpace} (hp : p ∈ frontier E)
    (hpc : p ∈ c.region) :
    c.placement (graphMapN c.height (graphProjectionN 2 (c.placement.symm p))) = p := by
  have hmem : p ∈ c.graphSurface ∩ c.region := by
    rw [← hc.frontier_inter_eq]
    exact ⟨hp, hpc⟩
  obtain ⟨⟨w, ⟨y, hy⟩, hw⟩, _⟩ := hmem
  have hpy : c.placement (graphMapN c.height y) = p := by rw [hy]; exact hw
  have hy0 : graphProjectionN 2 (c.placement.symm p) = y := by
    rw [← hpy, c.placement.symm_apply_apply]
    exact graphProjectionN_append y (c.height y)
  rwa [hy0]

set_option maxHeartbeats 800000 in
-- The chart/slab construction needs extra elaboration for the composed coordinate maps.
/-- The weak constant-mean-curvature equation of a perimeter minimiser holds on a small disk
around the base point of any chart through a boundary point. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.chart_weak_cmc_near {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) (hpc : p ∈ c.region) :
    ∃ R > 0, ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ ball (graphProjectionN 2 (c.placement.symm p)) R →
      (∫ y, inner ℝ (gradient c.height y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient c.height y‖ ^ 2)) =
        ∫ y, perimeterMinimizerMultiplier V Ω * φ y := by
  let y1 := graphProjectionN 2 (c.placement.symm p)
  have hy1 : c.placement (graphMapN c.height y1) = p := hc.placement_graph_base_perim hp hpc
  let Φ : (EuclideanSpace ℝ (Fin 2)) × ℝ → AmbientSpace := fun q =>
    c.placement (graphBaseN 2 q.1 + q.2 • EuclideanSpace.single (Fin.last 2) (1 : ℝ))
  have hΦ : Continuous Φ :=
    c.placement.continuous.comp (((graphBaseN 2).continuous.comp continuous_fst).add
      (continuous_snd.smul continuous_const))
  have hΦp : Φ (y1, c.height y1) = p := hy1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (c.isOpen_region.preimage hΦ)
    (y1, c.height y1)
    (by change Φ (y1, c.height y1) ∈ c.region; rw [hΦp]; exact hpc)
  obtain ⟨r, hr, hfr⟩ := Metric.continuousAt_iff.mp
    (c.height_contDiff.continuous.continuousAt (x := y1)) (ε / 2) (half_pos hε)
  let R := min r ε
  have hR : 0 < R := lt_min hr hε
  have hRr : R ≤ r := min_le_left _ _
  have hRε : R ≤ ε := min_le_right _ _
  refine ⟨R, hR, ?_⟩
  intro ζ hζ hcζ hsζ
  apply hmin.graph_prescribed_mean_curvature hV hΩo hC1 c hc hζ hcζ (half_pos hε)
  intro y hy t ht
  have hyr : dist y y1 < r := lt_of_lt_of_le (hsζ hy) hRr
  have hyε : dist y y1 < ε := lt_of_lt_of_le (hsζ hy) hRε
  have hfy := hfr hyr
  rw [Real.dist_eq] at hfy
  have htε : dist t (c.height y1) < ε := by
    rw [Real.dist_eq]
    calc
      |t - c.height y1| ≤ |t - c.height y| + |c.height y - c.height y1| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  have hmem : (y, t) ∈ ball (y1, c.height y1) ε := by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt hyε htε
  exact hball hmem

/-- `prop:bootstrap-C2` with `v_Ω = 0`: at a boundary point of a perimeter minimiser, a
`C^{1,a}` chart height becomes `C^{2,a}` on a smaller disk. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.height_C2_holder_near {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) (hpc : p ∈ c.region)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hf : ∃ ρ₀ > 0, HasC1HolderOn a c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ₀)) :
    ∃ ρ > 0, HasC2HolderOn a c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ) := by
  obtain ⟨ρ₀, hρ₀, hf⟩ := hf
  obtain ⟨R₀, hR₀, heq⟩ := hmin.chart_weak_cmc_near hV hΩo hC1 hc hp hpc
  let R := min ρ₀ R₀
  have hR : 0 < R := lt_min hρ₀ hR₀
  refine ⟨R / 2, half_pos hR, ?_⟩
  apply mc_graph_C2_holder_ball ha ha1 _ hR
    ((hf.mono (ball_subset_ball (min_le_left _ _))).1)
    (hasC1HolderOn_const_perim a (perimeterMinimizerMultiplier V Ω) _).function_holder
  intro ζ hζ hcζ hsζ
  exact heq ζ hζ hcζ (hsζ.trans (ball_subset_ball (min_le_right _ _)))

/-- `prop:bootstrap-C2` with `v_Ω = 0`: one `C^{1,a}` input at a boundary point of a
perimeter minimiser yields `C^{2,β}` nearby for every `0 < β < 1`. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.height_C2_holder_all {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) (hpc : p ∈ c.region)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hf : ∃ ρ₀ > 0, HasC1HolderOn a c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ₀)) :
    ∀ β : ℝ, 0 < β → β < 1 → ∃ ρ > 0, HasC2HolderOn β c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ) := by
  obtain ⟨r, hr, hC2⟩ := hmin.height_C2_holder_near hV hΩo hC1 hc hp hpc ha ha1 hf
  intro β hβ hβ1
  apply hmin.height_C2_holder_near hV hΩo hC1 hc hp hpc hβ hβ1
  exact ⟨r / 2, half_pos hr,
    bootstrap_c1Holder_of_contDiffOn_two hβ hβ1 _ hr hC2.contDiff⟩

/-- `prop:bootstrap-C2` with `v_Ω = 0`: at every boundary point of a perimeter minimiser
there is a chart whose height is `C^{2,β}` near the base point, for every `0 < β < 1`. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.exists_c2Holder_chart {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) :
    ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧ p ∈ c.region ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∃ ρ > 0, HasC2HolderOn β c.height
        (ball (graphProjectionN 2 (c.placement.symm p)) ρ) := by
  obtain ⟨c, hc, hpc, hf⟩ := hmin.hasC1HolderBoundary hV hΩo hC1 p hp
  exact ⟨c, hc, hpc, hmin.height_C2_holder_all hV hΩo hC1 hc hp hpc (by norm_num)
    (by norm_num) hf⟩

/-- `prop:bootstrap-C2` with `v_Ω = 0`: a perimeter minimiser has `C²` boundary. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.hasCkBoundary_two {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω) :
    HasCkBoundary 2 Ω := by
  apply hasCkBoundary_of_local
  intro p hp
  obtain ⟨c, hc, hpc, hβ⟩ := hmin.exists_c2Holder_chart hV hΩo hC1 hp
  obtain ⟨ρ, hρ, hC2⟩ := hβ (1 / 2) (by norm_num) (by norm_num)
  exact ⟨c, hc, hpc, ρ, hρ, hC2.contDiff⟩

/-! ### The `C³` step -/

/-- `prop:bootstrap-C3` with `v_Ω = 0`: at a boundary point of a perimeter minimiser, a chart
height that is `C^{2,a}` near the base point is `C³` on a smaller disk, on which the weak
constant-mean-curvature equation holds. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.height_C3_near {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) (hpc : p ∈ c.region)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hf : ∃ ρ₀ > 0, HasC2HolderOn a c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ₀)) :
    ∃ ρ > 0, ContDiffOn ℝ 3 c.height (ball (graphProjectionN 2 (c.placement.symm p)) ρ) ∧
      ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ ball (graphProjectionN 2 (c.placement.symm p)) ρ →
        (∫ y, inner ℝ (gradient c.height y) (gradient φ y) /
          Real.sqrt (1 + ‖gradient c.height y‖ ^ 2)) =
          ∫ y, perimeterMinimizerMultiplier V Ω * φ y := by
  obtain ⟨ρ₀, hρ₀, hf⟩ := hf
  obtain ⟨R₀, hR₀, heq⟩ := hmin.chart_weak_cmc_near hV hΩo hC1 hc hp hpc
  let R := min ρ₀ R₀
  have hR : 0 < R := lt_min hρ₀ hR₀
  have heqR : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ ball (graphProjectionN 2 (c.placement.symm p)) R →
      (∫ y, inner ℝ (gradient c.height y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient c.height y‖ ^ 2)) =
        ∫ y, perimeterMinimizerMultiplier V Ω * φ y :=
    fun φ hφ hcφ hsφ => heq φ hφ hcφ (hsφ.trans (ball_subset_ball (min_le_right _ _)))
  refine ⟨R / 2, half_pos hR, ?_, ?_⟩
  · exact mc_graph_C3_ball mcGraphC3UnitStatement_holds ha ha1 _ hR
      ((hf.nondiv_mono (ball_subset_ball (min_le_left _ _))).1)
      (hasC1HolderOn_const_perim a (perimeterMinimizerMultiplier V Ω) _) heqR
  · intro φ hφ hcφ hsφ
    exact heqR φ hφ hcφ (hsφ.trans (ball_subset_ball (by linarith)))

/-- `prop:bootstrap-C3` with `v_Ω = 0`: a perimeter minimiser has `C³` boundary. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.hasCkBoundary_three {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω) :
    HasCkBoundary 3 Ω := by
  apply hasCkBoundary_of_local
  intro p hp
  obtain ⟨c, hc, hpc, hβ⟩ := hmin.exists_c2Holder_chart hV hΩo hC1 hp
  obtain ⟨ρ, hρ, h3, _⟩ := hmin.height_C3_near hV hΩo hC1 hc hp hpc (a := 1 / 2)
    (by norm_num) (by norm_num) (hβ (1 / 2) (by norm_num) (by norm_num))
  exact ⟨c, hc, hpc, ρ, hρ, h3⟩

/-- Blueprint `thm:isoperimetric-rigidity`, Step 2: at every boundary point of a fixed-volume
perimeter minimiser there is a chart whose height is `C³` on a disk around the base point, on
which the weak constant-mean-curvature equation with multiplier `2P / (3V)` holds. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.exists_C3_chart_weak_cmc {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω)
    (hC1 : HasC1Boundary Ω) (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) :
    ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧ p ∈ c.region ∧ ∃ ρ > 0,
      ContDiffOn ℝ 3 c.height (Metric.ball (graphProjectionN 2 (c.placement.symm p)) ρ) ∧
      ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball (graphProjectionN 2 (c.placement.symm p)) ρ →
        (∫ y, inner ℝ (gradient c.height y) (gradient φ y) /
          Real.sqrt (1 + ‖gradient c.height y‖ ^ 2)) =
          ∫ y, perimeterMinimizerMultiplier V Ω * φ y := by
  obtain ⟨c, hc, hpc, hβ⟩ := hmin.exists_c2Holder_chart hV hΩo hC1 hp
  exact ⟨c, hc, hpc, hmin.height_C3_near hV hΩo hC1 hc hp hpc (a := 1 / 2)
    (by norm_num) (by norm_num) (hβ (1 / 2) (by norm_num) (by norm_num))⟩

end LiquidDrop
