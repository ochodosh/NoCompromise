module

public import NoCompromise.Regularity.EpsRegularityHeight
public import NoCompromise.Regularity.EpsRegularityCone
public import NoCompromise.Regularity.EpsRegularityGraph
public import NoCompromise.Regularity.EpsRegularityNormalField
public import NoCompromise.Regularity.EpsRegularityFlat

@[expose] public section

/-!
# ε-regularity (`thm:eps-regularity`)

Blueprint `thm:eps-regularity`. The boundary of the density-one representative in
`C_{r/4}` is exactly the graph of a `C^{1,1/2}` height over the base disk of
radius `r/4` (graph direction `e₃`, so the rotation is the identity), with the
normal field equal to the reduced normal on `∂*E` and `1/2`-Hölder with the
bound `C (‖p - q‖ / r)^{1/2} (Exc + ω r)^{1/2}` on all of `∂Ω ∩ C_{r/4}`.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Blueprint `thm:eps-regularity`: under `Exc(E,0,r,e₃) + ω r ≤ ε₀`, the
boundary `∂Ω ∩ C_{r/4}` is the graph of a differentiable height `f` whose
derivative is `1/2`-Hölder with constant `C r^{-1/2} (Exc + ω r)^{1/2}`; the
normal field is the reduced normal on `∂*E` and satisfies `eq:eps-reg-holder`
on `∂Ω ∩ C_{r/4}` (which contains `C_{r/8}`). The constants are absolute. -/
theorem eps_regularity :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω) (r : ℝ),
      (0 : AmbientSpace) ∈ frontier (densityOne E) → 0 < r → r ≤ 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
        (EuclideanSpace.single 2 1) + ω * r ≤ ε₀ →
      ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (νΩ : AmbientSpace → AmbientSpace),
        frontier (densityOne E) ∩ standardCylinder (r / 4) =
          (fun x' => graphAppendN x' (f x')) '' ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4), |f x'| < r / 8) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4),
          HasFDerivAt f (-(νΩ (graphAppendN x' (f x')) 2)⁻¹ •
            innerSL ℝ (graphProjectionN 2 (νΩ (graphAppendN x' (f x'))))) x') ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4),
          ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4),
          ‖fderiv ℝ f x' - fderiv ℝ f y'‖ ≤ C * Real.sqrt (‖x' - y'‖ / r) *
            Real.sqrt (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
              (EuclideanSpace.single 2 1) + ω * r)) ∧
        (∀ p ∈ frontier (densityOne E) ∩ standardCylinder (r / 4),
          ‖νΩ p‖ = 1 ∧ ‖νΩ p - EuclideanSpace.single 2 1‖ ≤ C * Real.sqrt
            (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
              (EuclideanSpace.single 2 1) + ω * r)) ∧
        (∀ p ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (r / 4),
          νΩ p = reducedNormal E hE.locallyFinite hE.nullMeasurable p) ∧
        (∀ p ∈ frontier (densityOne E) ∩ standardCylinder (r / 4),
         ∀ q ∈ frontier (densityOne E) ∩ standardCylinder (r / 4),
          ‖νΩ p - νΩ q‖ ≤ C * Real.sqrt (‖p - q‖ / r) * Real.sqrt
            (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
              (EuclideanSpace.single 2 1) + ω * r)) := by
  have hH := fun (η : ℝ) (hη : 0 < η) => height_bound_general hη
  obtain ⟨εc, hεc, hcone⟩ := boundary_cone_estimate hH
  obtain ⟨εx, hεx, hcross⟩ := frontier_vertical_crossing
  obtain ⟨θ, hθ, hθ32, ε₁, hε₁, A, hA, hfield⟩ := quarter_normal_field
  have hθ1 : θ < 1 := by linarith
  have hεA : 0 < 1 / (4 * A ^ 2) := by positivity
  refine ⟨min (min εc εx) (min ε₁ (1 / (4 * A ^ 2))),
    lt_min (lt_min hεc hεx) (lt_min hε₁ hεA), 16 * A, by positivity, ?_⟩
  intro E ω hE r h0 hr hr1 hsmall
  set X := cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
    (EuclideanSpace.single 2 1) + ω * r with hX
  have hsc : X ≤ εc := hsmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hsx : X ≤ εx := hsmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs1 : X ≤ ε₁ := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsA : X ≤ 1 / (4 * A ^ 2) :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr4 : 0 < r / 4 := by linarith
  have hr41 : r / 4 ≤ 1 := by linarith
  obtain ⟨f, hfb, hfL, hgraph⟩ := boundary_graph_of_cone_crossing hr
    (hcone E ω hE r h0 hr hr1 hsc) (hcross E ω hE r h0 hr hr1 hsx)
  obtain ⟨νΩ, hfld, hred, hhold⟩ := hfield E ω hE r hr hr1 hs1
  have hAX : A * Real.sqrt X ≤ 1 / 2 := by
    have h1 : Real.sqrt X ≤ Real.sqrt ((1 / (2 * A)) ^ 2) := by
      apply Real.sqrt_le_sqrt
      calc X ≤ 1 / (4 * A ^ 2) := hsA
        _ = (1 / (2 * A)) ^ 2 := by field_simp; ring
    rw [Real.sqrt_sq (by positivity)] at h1
    calc A * Real.sqrt X ≤ A * (1 / (2 * A)) := mul_le_mul_of_nonneg_left h1 hA.le
      _ = 1 / 2 := by field_simp
  have hg : ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4),
      graphAppendN x' (f x') ∈ frontier (densityOne E) ∩ standardCylinder (r / 4) := by
    intro x' hx'
    rw [hgraph]
    exact ⟨x', hx', rfl⟩
  have hν2 : ∀ p ∈ frontier (densityOne E) ∩ standardCylinder (r / 4), 1 / 2 ≤ νΩ p 2 := by
    intro p hp
    have h := (hfld p hp).2.1
    have hc : |νΩ p 2 - 1| ≤ ‖νΩ p - EuclideanSpace.single 2 1‖ := by
      have he : νΩ p 2 - 1 = inner ℝ (EuclideanSpace.single 2 1 : AmbientSpace)
          (νΩ p - EuclideanSpace.single 2 1) := by
        rw [inner_single_two_eq]; simp
      rw [he]
      calc _ ≤ ‖(EuclideanSpace.single 2 1 : AmbientSpace)‖ *
            ‖νΩ p - EuclideanSpace.single 2 1‖ := abs_real_inner_le_norm _ _
        _ = _ := by simp
    have := (abs_le.mp (hc.trans (h.trans hAX))).1
    linarith
  have hderiv : ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4),
      HasFDerivAt f (-(νΩ (graphAppendN x' (f x')) 2)⁻¹ •
        innerSL ℝ (graphProjectionN 2 (νΩ (graphAppendN x' (f x'))))) x' := by
    intro x' hx'
    have hp := hg x' hx'
    obtain ⟨_, _, ν, hνu, hνt, hdec⟩ := hfld _ hp
    have hflat := boundary_flatness_of_iteration hH E ω hE _ hp.1 hθ hθ1 hr4 hr41
      hνu hνt hdec
    refine hasFDerivAt_of_graph_flat isOpen_ball hfL hx' (by linarith [hν2 _ hp]) ?_
    intro δ hδ
    obtain ⟨ρ, hρ, hq⟩ := hflat δ hδ
    exact ⟨ρ, hρ, fun y hy hyρ => hq _ (hg y hy).1 hyρ⟩
  have hgd : ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4),
      ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4),
      ‖graphAppendN x' (f x') - graphAppendN y' (f y')‖ ≤ 2 * ‖x' - y'‖ := by
    intro x' hx' y' hy'
    have h := norm_sq_graphProjectionN (graphAppendN x' (f x') - graphAppendN y' (f y'))
    rw [map_sub, graphProjectionN_append, graphProjectionN_append, PiLp.sub_apply,
      graphAppendN_last, graphAppendN_last] at h
    have hL := hfL x' hx' y' hy'
    have hL2 : (f x' - f y') ^ 2 ≤ ‖x' - y'‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hL 2
    have h2 : ‖graphAppendN x' (f x') - graphAppendN y' (f y')‖ ^ 2 ≤ (2 * ‖x' - y'‖) ^ 2 := by
      nlinarith [sq_nonneg ‖x' - y'‖]
    have := abs_le_of_sq_le_sq h2 (by positivity)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hX0 : 0 ≤ X := by
    have h1 : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
        (EuclideanSpace.single 2 1) :=
      div_nonneg (normalExcessIntegral_nonneg _ _ _ _ _) (sq_nonneg _)
    have h2 : 0 ≤ ω * r := mul_nonneg hE.nonneg hr.le
    rw [hX]; linarith
  refine ⟨f, νΩ, hgraph, hfb, hderiv, ?_, fun p hp => ⟨(hfld p hp).1, ?_⟩, hred, ?_⟩
  · intro x' hx' y' hy'
    have hpx := hg x' hx'
    have hpy := hg y' hy'
    rw [(hderiv x' hx').fderiv, (hderiv y' hy').fderiv]
    have hsl := graphSlope_sub_norm_le (hfld _ hpx).1 (hfld _ hpy).1 (hν2 _ hpx) (hν2 _ hpy)
    have hh := hhold _ hpx _ hpy
    have hsq : Real.sqrt (‖graphAppendN x' (f x') - graphAppendN y' (f y')‖ / r) ≤
        2 * Real.sqrt (‖x' - y'‖ / r) := by
      calc _ ≤ Real.sqrt (2 ^ 2 * (‖x' - y'‖ / r)) := by
            apply Real.sqrt_le_sqrt
            rw [show (2 : ℝ) ^ 2 * (‖x' - y'‖ / r) = 4 * ‖x' - y'‖ / r by ring]
            apply div_le_div_of_nonneg_right _ hr.le
            nlinarith [hgd x' hx' y' hy', norm_nonneg (x' - y')]
        _ = 2 * Real.sqrt (‖x' - y'‖ / r) := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    have hsX := Real.sqrt_nonneg X
    calc _ ≤ 8 * ‖νΩ (graphAppendN x' (f x')) - νΩ (graphAppendN y' (f y'))‖ := hsl
      _ ≤ 8 * (A * Real.sqrt (‖graphAppendN x' (f x') - graphAppendN y' (f y')‖ / r) *
            Real.sqrt X) := by linarith
      _ ≤ 8 * (A * (2 * Real.sqrt (‖x' - y'‖ / r)) * Real.sqrt X) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsq hA.le) hsX) (by norm_num)
      _ = 16 * A * Real.sqrt (‖x' - y'‖ / r) * Real.sqrt X := by ring
  · have hsX := Real.sqrt_nonneg X
    calc _ ≤ A * Real.sqrt X := (hfld p hp).2.1
      _ ≤ 16 * A * Real.sqrt X := by nlinarith [mul_nonneg hA.le hsX]
  · intro p hp q hq
    have hsq := mul_nonneg (Real.sqrt_nonneg (‖p - q‖ / r)) (Real.sqrt_nonneg X)
    calc _ ≤ A * Real.sqrt (‖p - q‖ / r) * Real.sqrt X := hhold p hp q hq
      _ ≤ 16 * A * Real.sqrt (‖p - q‖ / r) * Real.sqrt X := by
          nlinarith [mul_nonneg hA.le hsq]

end LiquidDrop
