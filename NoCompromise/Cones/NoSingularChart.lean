module

public import NoCompromise.Cones.NoSingularDefs
public import NoCompromise.Cones.SmoothGraph
public import NoCompromise.Regularity.EpsRegularityMain
public import NoCompromise.Regularity.ExcessDecayCoordinates
public import NoCompromise.Regularity.GraphTwoPointCaps
public import NoCompromise.Regularity.HeightBound
public import NoCompromise.Regularity.SlabGeometry

@[expose] public section

/-!
# Regular boundary points from vanishing excess (`prop:no-singular-points`)

If the cylindrical excess of an `ω`-minimal set at a boundary point `x` of `densityOne E` tends to
zero along scales `r j → 0` (for a fixed unit axis `ν`), then `x` is a regular boundary point: in
the rotated, rescaled cylinder `x + s • Q (standardCylinder (1/4))` the set `densityOne E` is the
strict subgraph of a `C^{1,1/2}` function `f` and its boundary is the graph of `f`.

* `regular_chart_unit` : the chart at the origin at unit scale, from `thm:eps-regularity`,
  the two phase caps of `graph_two_point_lipschitz` and the height bound (one-sidedness);
* `IsOmegaMinimal.isRegularBoundaryPoint_of_tendsto_excess` : the transported statement.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace LiquidDrop

/-- A preconnected set that avoids the boundary of an open set `D` and meets `D` lies in `D`. -/
lemma subset_of_isPreconnected_of_avoid_frontier {D S : Set AmbientSpace} (hD : IsOpen D)
    (hS : IsPreconnected S) (havoid : ∀ q ∈ S, q ∉ frontier D) {a : AmbientSpace}
    (ha : a ∈ S) (haD : a ∈ D) : S ⊆ D := by
  refine hS.subset_of_closure_inter_subset hD ⟨a, ha, haD⟩ ?_
  rintro q ⟨hqc, hqS⟩
  by_contra hqD
  exact havoid q hqS (by rw [hD.frontier_eq]; exact ⟨hqc, hqD⟩)

/-- **The one-sided graph chart at the origin at unit scale.**  If `0` is a boundary point of
`densityOne F` for an `ω`-minimal `F` and the unit-scale excess plus `ω` is small, then inside
`standardCylinder (1/4)` the set `densityOne F` is the strict subgraph `{y 2 < f y'}` and its
boundary is the graph `{y 2 = f y'}` of a `C^{1,1/2}` function with `|f| < 1/8`. -/
theorem regular_chart_unit :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Set AmbientSpace) (ω : ℝ) (hF : IsOmegaMinimal F ω),
      (0 : AmbientSpace) ∈ frontier (densityOne F) →
      cylindricalExcess F hF.locallyFinite hF.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      ∃ (K : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), |f x'| < 1 / 8) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), DifferentiableAt ℝ f x') ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
            ‖fderiv ℝ f x' - fderiv ℝ f y'‖ ≤ K * Real.sqrt ‖x' - y'‖) ∧
        (∀ y ∈ standardCylinder (1 / 4),
          (y ∈ densityOne F ↔ y 2 < f (graphProjectionN 2 y))) ∧
        (∀ y ∈ standardCylinder (1 / 4),
          (y ∈ frontier (densityOne F) ↔ y 2 = f (graphProjectionN 2 y))) := by
  obtain ⟨ε₀, hε₀, C, _hC, hreg⟩ := eps_regularity
  obtain ⟨_c, _hc, ε₁, hε₁, hcaps⟩ :=
    graph_two_point_lipschitz (γ := (1 / 16 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨ε₂, hε₂, hheight⟩ := height_bound (η := (1 / 8 : ℝ)) (by norm_num)
  refine ⟨min ε₀ (min ε₁ ε₂), lt_min hε₀ (lt_min hε₁ hε₂), ?_⟩
  intro F ω hF h0 he
  set X := cylindricalExcess F hF.locallyFinite hF.nullMeasurable 0 1
    (EuclideanSpace.single 2 1) with hX
  have he0 : X + ω * 1 ≤ ε₀ := by rw [mul_one]; exact he.trans (min_le_left _ _)
  have he1 : X + ω ≤ ε₁ := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have he2 : X + ω * 1 ≤ ε₂ := by
    rw [mul_one]; exact he.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨f, _νΩ, hgraph, hf8, hfd, hhol, _⟩ := hreg F ω hF 1 h0 one_pos le_rfl he0
  obtain ⟨_, _, hbottom, htop, _⟩ := hcaps F ω hF h0 he1
  set D := densityOne F with hDdef
  have hDopen : IsOpen D := hF.isOpen_densityOne
  -- a boundary point on a vertical line over the quarter disk, at height in `[-1/2, 1/2]`,
  -- is the graph point
  have hvert : ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), ∀ τ : ℝ, |τ| ≤ 1 / 2 →
      graphAppendN x' τ ∈ frontier D → τ = f x' := by
    intro x' hx' τ hτ hfr
    have hx'n : ‖x'‖ < 1 / 4 := by simpa only [mem_ball, dist_zero_right] using hx'
    have hC34 : graphAppendN x' τ ∈ standardCylinder (3 * 1 / 4) := by
      change ‖graphProjectionN 2 (graphAppendN x' τ)‖ < 3 * 1 / 4 ∧
        |graphAppendN x' τ 2| < 3 * 1 / 4
      rw [graphProjectionN_append, graphAppendN_height_three]
      constructor <;> linarith
    have hsmall : |τ| < 1 / 8 := by
      have hh := hheight F ω hF h0 1 one_pos le_rfl he2 (graphAppendN x' τ) ⟨hfr, hC34⟩
      simpa only [graphAppendN_height_three, mul_one] using hh
    have hC14 : graphAppendN x' τ ∈ standardCylinder (1 / 4) := by
      change ‖graphProjectionN 2 (graphAppendN x' τ)‖ < 1 / 4 ∧
        |graphAppendN x' τ 2| < 1 / 4
      rw [graphProjectionN_append, graphAppendN_height_three]
      constructor <;> linarith
    have hmem : graphAppendN x' τ ∈ frontier D ∩ standardCylinder (1 / 4) := ⟨hfr, hC14⟩
    rw [hgraph] at hmem
    obtain ⟨z', _, hz⟩ := hmem
    have hz' : z' = x' := by
      simpa only [graphProjectionN_append] using congrArg (graphProjectionN 2) hz
    subst hz'
    simpa only [graphAppendN_height_three] using (congrArg (fun p => p 2) hz).symm
  -- the frontier clause
  have hfront : ∀ y ∈ standardCylinder (1 / 4),
      (y ∈ frontier D ↔ y 2 = f (graphProjectionN 2 y)) := by
    intro y hy
    have hrec : graphAppendN (graphProjectionN 2 y) (y 2) = y := graphAppendN_projection y
    have hyb : graphProjectionN 2 y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4) := by
      simpa only [mem_ball, dist_zero_right] using hy.1
    constructor
    · intro hyf
      have hmem : y ∈ frontier D ∩ standardCylinder (1 / 4) := ⟨hyf, hy⟩
      rw [hgraph] at hmem
      obtain ⟨x', _, rfl⟩ := hmem
      simp only [graphProjectionN_append, graphAppendN_height_three]
    · intro hyt
      have hmem : y ∈ (fun x' => graphAppendN x' (f x')) ''
          ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4) :=
        ⟨graphProjectionN 2 y, hyb, by
          change graphAppendN _ (f _) = y; rw [← hyt]; exact hrec⟩
      rw [← hgraph] at hmem
      exact hmem.1
  refine ⟨C * Real.sqrt (X + ω * 1), f, ?_, ?_, ?_, ?_, hfront⟩
  · intro x' hx'
    simpa using hf8 x' hx'
  · intro x' hx'
    exact (hfd x' hx').differentiableAt
  · intro x' hx' y' hy'
    have h := hhol x' hx' y' hy'
    rw [div_one] at h
    calc ‖fderiv ℝ f x' - fderiv ℝ f y'‖
        ≤ C * Real.sqrt ‖x' - y'‖ * Real.sqrt (X + ω * 1) := h
      _ = C * Real.sqrt (X + ω * 1) * Real.sqrt ‖x' - y'‖ := by ring
  · intro y hy
    set x' := graphProjectionN 2 y with hx'def
    set t := y 2 with htdef
    have hrec : graphAppendN x' t = y := graphAppendN_projection y
    have hx'b : x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4) := by
      simpa only [mem_ball, dist_zero_right] using hy.1
    have hx'b2 : x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) :=
      ball_subset_ball (by norm_num) hx'b
    have ht4 : |t| < 1 / 4 := hy.2
    have hcont : Continuous (fun τ : ℝ => graphAppendN x' τ) :=
      continuous_const.add (continuous_id.smul continuous_const)
    rcases lt_trichotomy t (f x') with hlt | heq | hgt
    · -- below the graph: the segment down to the bottom cap stays in `D`
      refine ⟨fun _ => hlt, fun _ => ?_⟩
      let S : Set AmbientSpace := (fun τ : ℝ => graphAppendN x' τ) '' Icc (-(1 / 2 : ℝ)) t
      have hconn : IsPreconnected S := isPreconnected_Icc.image _ hcont.continuousOn
      have havoid : ∀ q ∈ S, q ∉ frontier D := by
        rintro q ⟨τ, hτ, rfl⟩ hq
        have hτ' : |τ| ≤ 1 / 2 := abs_le.mpr ⟨hτ.1, by linarith [hτ.2, (abs_lt.mp ht4).2]⟩
        have := hvert x' hx'b τ hτ' hq
        linarith [hτ.2]
      have hbS : graphAppendN x' (-(1 / 2 : ℝ)) ∈ S :=
        ⟨-(1 / 2 : ℝ), ⟨le_rfl, by linarith [(abs_lt.mp ht4).1]⟩, rfl⟩
      have hbD : graphAppendN x' (-(1 / 2 : ℝ)) ∈ D := hbottom ⟨x', hx'b2, rfl⟩
      have hyS : y ∈ S := ⟨t, ⟨by linarith [(abs_lt.mp ht4).1], le_rfl⟩, hrec⟩
      exact subset_of_isPreconnected_of_avoid_frontier hDopen hconn havoid hbS hbD hyS
    · -- on the graph: a boundary point of the open set `D` is not in `D`
      refine ⟨fun hyD => ?_, fun h => absurd h (by rw [heq]; exact lt_irrefl _)⟩
      have hyf : y ∈ frontier D := (hfront y hy).mpr heq
      rw [hDopen.frontier_eq] at hyf
      exact absurd hyD hyf.2
    · -- above the graph: the segment up to the top cap avoids the boundary and ends outside `D`
      refine ⟨fun hyD => ?_, fun h => absurd h (not_lt.mpr hgt.le)⟩
      exfalso
      let S : Set AmbientSpace := (fun τ : ℝ => graphAppendN x' τ) '' Icc t (1 / 2 : ℝ)
      have hconn : IsPreconnected S := isPreconnected_Icc.image _ hcont.continuousOn
      have havoid : ∀ q ∈ S, q ∉ frontier D := by
        rintro q ⟨τ, hτ, rfl⟩ hq
        have hτ' : |τ| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hτ.1, (abs_lt.mp ht4).1], hτ.2⟩
        have := hvert x' hx'b τ hτ' hq
        linarith [hτ.1]
      have htS : graphAppendN x' (1 / 2 : ℝ) ∈ S :=
        ⟨(1 / 2 : ℝ), ⟨by linarith [(abs_lt.mp ht4).2], le_rfl⟩, rfl⟩
      have htD : graphAppendN x' (1 / 2 : ℝ) ∉ D :=
        disjoint_left.mp (disjoint_densityZero_densityOne F) (htop ⟨x', hx'b2, rfl⟩)
      have hyS : y ∈ S := ⟨t, ⟨le_rfl, by linarith [(abs_lt.mp ht4).2]⟩, hrec⟩
      exact htD (subset_of_isPreconnected_of_avoid_frontier hDopen hconn havoid hyS hyD htS)

/-- The density-one representative of the excess-decay coordinates is the exact rigid-and-dilation
pullback of the density-one representative. -/
lemma mem_densityOne_excessDecayCoordinates (E : Set AmbientSpace) (x ν y : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    y ∈ densityOne (excessDecayCoordinates E x r ν) ↔
      x + r • verticalAxisIsometry ν y ∈ densityOne E := by
  rw [excessDecayCoordinates, densityOne_preimage_affineIsometry, mem_preimage]
  change verticalAxisIsometry ν y ∈ densityOne (blowupSet E x r) ↔ _
  rw [mem_densityOne_blowupSet E x _ hr]

/-- **`prop:no-singular-points`, the chart step.**  A boundary point of the density-one
representative of an `ω`-minimal set at which the cylindrical excess (for a fixed unit axis `ν`)
tends to zero along scales `r j → 0` is a regular boundary point. -/
theorem IsOmegaMinimal.isRegularBoundaryPoint_of_tendsto_excess {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {x ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (hx : x ∈ frontier (densityOne E)) {r : ℕ → ℝ} (hr : ∀ j, 0 < r j)
    (hr0 : Tendsto r atTop (𝓝 0))
    (hexc : Tendsto (fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (r j) ν)
      atTop (𝓝 0)) :
    IsRegularBoundaryPoint (densityOne E) x := by
  obtain ⟨ε, hε, hchart⟩ := regular_chart_unit
  have hsum : Tendsto (fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (r j) ν
      + ω * r j) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hexc.add (hr0.const_mul ω)
  have hev : ∀ᶠ j in atTop,
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (r j) ν + ω * r j < ε ∧
        r j < 1 :=
    (hsum.eventually (gt_mem_nhds hε)).and (hr0.eventually (gt_mem_nhds one_pos))
  obtain ⟨j, hj, hj1⟩ := hev.exists
  set s := r j with hsdef
  have hs : 0 < s := hr j
  have hs1 : s ≤ 1 := hj1.le
  have hF := hE.excessDecayCoordinates x hs hs1 ν
  have h0 : (0 : AmbientSpace) ∈
      frontier (densityOne (LiquidDrop.excessDecayCoordinates E x s ν)) :=
    (excessDecayCoordinates_origin_frontier E x ν hs).2 hx
  have hexc' : cylindricalExcess (LiquidDrop.excessDecayCoordinates E x s ν) hF.locallyFinite
      hF.nullMeasurable 0 1 (EuclideanSpace.single 2 1) =
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x s ν :=
    cylindricalExcess_excessDecayCoordinates_unit hE x ν hs hs1 hν
  obtain ⟨K, f, hf8, hfd, hhol, hΩ, hfr⟩ :=
    hchart _ (ω * s) hF h0 (by rw [hexc']; exact hj.le)
  refine ⟨ν, s, K, f, hν, hs, hf8, hfd, hhol, ?_, ?_⟩
  · intro y hy
    rw [← mem_densityOne_excessDecayCoordinates E x ν y hs]
    exact hΩ y hy
  · intro y hy
    rw [← mem_frontier_densityOne_excessDecayCoordinates E x ν y hs]
    exact hfr y hy

end LiquidDrop
