import NoCompromise.Regularity.EpsRegularityCone
import NoCompromise.Regularity.EpsRegularityNormalHolder
import NoCompromise.Regularity.LimitingNormal
import NoCompromise.Regularity.GraphGoodSet

/-!
# The limiting normal field on the quarter cylinder

Blueprint `thm:eps-regularity`, Steps 2–4. Under the ε-regularity smallness
hypothesis at the origin, every boundary point of the density-one
representative in the quarter cylinder carries a limiting normal. The field is
unit, close to `e₃`, equal to the reduced normal on the reduced boundary, and
`1/2`-Hölder with the scale-invariant bound of `eq:eps-reg-holder`. The
geometric decay data at each centre are kept for the flatness argument.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Blueprint `thm:eps-regularity`, Steps 2–4: the limiting normal field on
`∂Ω ∩ C_{r/4}` with absolute constants. -/
theorem quarter_normal_field :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 32 ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ A : ℝ, 0 < A ∧
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω) (r : ℝ),
      0 < r → r ≤ 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
        (EuclideanSpace.single 2 1) + ω * r ≤ ε₁ →
      ∃ νΩ : AmbientSpace → AmbientSpace,
        (∀ p ∈ frontier (densityOne E) ∩ standardCylinder (r / 4),
          ‖νΩ p‖ = 1 ∧
          ‖νΩ p - EuclideanSpace.single 2 1‖ ≤ A * Real.sqrt
            (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
              (EuclideanSpace.single 2 1) + ω * r) ∧
          ∃ ν : ℕ → AmbientSpace, (∀ j, ‖ν j‖ = 1) ∧ Tendsto ν atTop (𝓝 (νΩ p)) ∧
            ∀ j, cylindricalExcess E hE.locallyFinite hE.nullMeasurable p
              (θ ^ j * (r / 4)) (ν j) + ω * (θ ^ j * (r / 4)) ≤
              A * θ ^ j * (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
                (EuclideanSpace.single 2 1) + ω * r)) ∧
        (∀ p ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (r / 4),
          νΩ p = reducedNormal E hE.locallyFinite hE.nullMeasurable p) ∧
        (∀ p ∈ frontier (densityOne E) ∩ standardCylinder (r / 4),
         ∀ q ∈ frontier (densityOne E) ∩ standardCylinder (r / 4),
          ‖νΩ p - νΩ q‖ ≤ A * Real.sqrt (‖p - q‖ / r) * Real.sqrt
            (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
              (EuclideanSpace.single 2 1) + ω * r)) := by
  obtain ⟨θ, hθ, hθ32, ε₀', hε₀', C, hC, hb⟩ := normals_cauchy_quarter_centers
  obtain ⟨K, hK, hhol⟩ := limiting_normals_two_centre_holder
  have hθ1 : θ < 1 := by linarith
  set B : ℝ := (2 * C + Real.sqrt (2 * K * C)) * (2 / Real.sqrt θ) with hB
  have hBpos : 0 < B := by
    have h1 : 0 < 2 * C + Real.sqrt (2 * K * C) := by
      have := Real.sqrt_nonneg (2 * K * C); linarith
    have h2 : 0 < 2 / Real.sqrt θ := div_pos two_pos (Real.sqrt_pos.mpr hθ)
    exact mul_pos h1 h2
  refine ⟨θ, hθ, hθ32, min ε₀' 1, lt_min hε₀' one_pos, 16 * C + 8 * B, by linarith, ?_⟩
  intro E ω hE r hr hr1 hsmall
  set X := cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
    (EuclideanSpace.single 2 1) + ω * r with hX
  have he₃ : ‖(EuclideanSpace.single 2 1 : AmbientSpace)‖ = 1 := by simp
  have hω : 0 ≤ ω := hE.nonneg
  have hωr : 0 ≤ ω * r := mul_nonneg hω hr.le
  have hExc0 : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
      (EuclideanSpace.single 2 1) :=
    div_nonneg (normalExcessIntegral_nonneg _ _ _ _ _) (sq_nonneg _)
  have hX0 : 0 ≤ X := by rw [hX]; linarith
  have hs1 : X ≤ ε₀' := hsmall.trans (min_le_left _ _)
  have hωr1 : ω * r ≤ 1 := by
    have := hsmall.trans (min_le_right _ _); rw [hX] at this; linarith
  have hr4 : 0 < r / 4 := by linarith
  have hr41 : r / 4 ≤ 1 := by linarith
  have hωr4 : ω * (r / 4) ≤ 1 := by
    have : ω * (r / 4) = ω * r / 4 := by ring
    rw [this]; linarith
  have hsq16 : Real.sqrt (16 * X) = 4 * Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16) X,
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  -- the iteration at every centre of the quarter cylinder
  have hdata : ∀ p ∈ frontier (densityOne E) ∩ standardCylinder (r / 4),
      ∃ (ν : ℕ → AmbientSpace) (νlim : AmbientSpace),
        ν 0 = EuclideanSpace.single 2 1 ∧ (∀ j, ‖ν j‖ = 1) ∧ ‖νlim‖ = 1 ∧
        Tendsto ν atTop (𝓝 νlim) ∧
        (∀ j, cylindricalExcess E hE.locallyFinite hE.nullMeasurable p
          (θ ^ j * (r / 4)) (ν j) + ω * (θ ^ j * (r / 4)) ≤ C * θ ^ j * (16 * X)) ∧
        (∀ j, ‖ν j - νlim‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt (16 * X)) := by
    intro p hp
    have hpc : p ∈ cylinder 0 (r / 4) (EuclideanSpace.single 2 1) := by
      rw [← standardCylinder_eq_cylinder]; exact hp.2
    obtain ⟨ν, νlim, hinit, hunit, hnlim, htend, hrest⟩ :=
      hb E ω hE 0 r (EuclideanSpace.single 2 1) hr hr1 he₃ hs1 p ⟨hp.1, hpc⟩
    dsimp only at hrest
    have he0 : cylindricalExcess E hE.locallyFinite hE.nullMeasurable p
        (θ ^ 0 * (r / 4)) (ν 0) + ω * (r / 4) ≤ 16 * X := by
      have hc := excess_change_center_quarter E hE.locallyFinite hE.nullMeasurable hr he₃ hpc
      have h4 : ω * (r / 4) = ω * r / 4 := by ring
      rw [pow_zero, one_mul, hinit, h4, hX]
      linarith
    refine ⟨ν, νlim, hinit, hunit, hnlim, htend, fun j => ?_, fun j => ?_⟩
    · obtain ⟨_, henergy, _, _⟩ := hrest j
      exact henergy.trans
        (mul_le_mul_of_nonneg_left he0 (mul_nonneg hC.le (pow_nonneg hθ.le j)))
    · obtain ⟨_, _, _, hrate⟩ := hrest j
      exact hrate.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he0)
        (mul_nonneg hC.le (Real.rpow_nonneg hθ.le _)))
  choose! νs νΩ hinit hunit hnlim htend hdec hrate using hdata
  refine ⟨νΩ, fun p hp => ⟨hnlim p hp, ?_, νs p, hunit p hp, htend p hp, fun j => ?_⟩,
    fun p hp => ?_, fun p hp q hq => ?_⟩
  · -- closeness to the vertical axis
    have h0 := hrate p hp 0
    rw [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one, hsq16, hinit p hp,
      norm_sub_rev] at h0
    have hsX := Real.sqrt_nonneg X
    calc ‖νΩ p - EuclideanSpace.single 2 1‖ ≤ C * (4 * Real.sqrt X) := h0
      _ ≤ (16 * C + 8 * B) * Real.sqrt X := by
          nlinarith [mul_nonneg hC.le hsX, mul_nonneg hBpos.le hsX]
  · -- geometric decay
    have hθX : 0 ≤ θ ^ j * X := mul_nonneg (pow_nonneg hθ.le j) hX0
    calc _ ≤ C * θ ^ j * (16 * X) := hdec p hp j
      _ ≤ (16 * C + 8 * B) * θ ^ j * X := by nlinarith [mul_nonneg hBpos.le hθX]
  · -- identification with the reduced normal
    have hp' : p ∈ frontier (densityOne E) ∩ standardCylinder (r / 4) :=
      ⟨hE.reducedBoundary_subset_frontier hp.1, hp.2⟩
    refine limiting_normal_eq_reducedNormal E hE.locallyFinite hE.nullMeasurable hp.1
      hθ hθ1 hr4 C (16 * X) (hunit p hp') (hnlim p hp') (htend p hp') (fun j => ?_)
    have hd := hdec p hp' j
    have hωj : 0 ≤ ω * (θ ^ j * (r / 4)) := mul_nonneg hω (mul_pos (pow_pos hθ j) hr4).le
    linarith
  · -- the Hölder estimate
    have h16 : (0 : ℝ) ≤ 16 * X := by linarith
    have hh := hhol E ω hE p q hp.1 hθ hθ1 hC.le h16 hr4 hr41 hωr4
      ((hinit p hp).trans (hinit q hq).symm) (hunit p hp) (hunit q hq)
      (hdec p hp) (hdec q hq) (hrate p hp) (hrate q hq)
    have hd4 : Real.sqrt (‖p - q‖ / (r / 4)) = 2 * Real.sqrt (‖p - q‖ / r) := by
      rw [show ‖p - q‖ / (r / 4) = 2 ^ 2 * (‖p - q‖ / r) by
          rw [div_div_eq_mul_div]; ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hprod := mul_nonneg (Real.sqrt_nonneg (‖p - q‖ / r)) (Real.sqrt_nonneg X)
    calc ‖νΩ p - νΩ q‖ ≤ B * Real.sqrt (‖p - q‖ / (r / 4)) * Real.sqrt (16 * X) := hh
      _ = 8 * B * (Real.sqrt (‖p - q‖ / r) * Real.sqrt X) := by rw [hd4, hsq16]; ring
      _ ≤ (16 * C + 8 * B) * (Real.sqrt (‖p - q‖ / r) * Real.sqrt X) := by
          nlinarith [mul_nonneg hC.le hprod]
      _ = (16 * C + 8 * B) * Real.sqrt (‖p - q‖ / r) * Real.sqrt X := by ring

end LiquidDrop
