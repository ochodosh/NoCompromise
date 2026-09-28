import NoCompromise.Regularity.EpsRegularityAhlfors
import NoCompromise.Regularity.EpsRegularityHolder

/-!
# Hölder estimate for limiting normals at two boundary centres

Blueprint `thm:eps-regularity`, Step 4. Two iterations started from a common
axis at a common initial scale `s₀ ≤ 1`, one at a boundary centre `x` and one
at any centre `y`, with geometric excess decay and the geometric normal rate,
have limits at distance `≤ A √(‖x - y‖ / s₀) √T`. The constant `A` depends only
on the decay data `θ`, `C` and on the absolute two-centre constant.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Blueprint `thm:eps-regularity`, Step 4: the `1/2`-Hölder comparison of the
limiting normals at two centres. -/
theorem limiting_normals_two_centre_holder :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
      (x y : AmbientSpace) {θ C T s₀ : ℝ} {νx νy : ℕ → AmbientSpace} {ℓx ℓy : AmbientSpace},
      x ∈ frontier (densityOne E) → 0 < θ → θ < 1 → 0 ≤ C → 0 ≤ T →
      0 < s₀ → s₀ ≤ 1 → ω * s₀ ≤ 1 →
      νx 0 = νy 0 → (∀ j, ‖νx j‖ = 1) → (∀ j, ‖νy j‖ = 1) →
      (∀ j, cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (θ ^ j * s₀) (νx j) +
        ω * (θ ^ j * s₀) ≤ C * θ ^ j * T) →
      (∀ j, cylindricalExcess E hE.locallyFinite hE.nullMeasurable y (θ ^ j * s₀) (νy j) +
        ω * (θ ^ j * s₀) ≤ C * θ ^ j * T) →
      (∀ j, ‖νx j - ℓx‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt T) →
      (∀ j, ‖νy j - ℓy‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt T) →
      ‖ℓx - ℓy‖ ≤ (2 * C + Real.sqrt (2 * K * C)) * (2 / Real.sqrt θ) *
        Real.sqrt (‖x - y‖ / s₀) * Real.sqrt T := by
  obtain ⟨K, hK, hcompare⟩ := normals_two_centre_comparison
  refine ⟨K, hK, ?_⟩
  intro E ω hE x y θ C T s₀ νx νy ℓx ℓy hx hθ hθ1 hC hT hs₀ hs₀1 hωs₀ h0 hux huy
    hex hey hxr hyr
  have hω : 0 ≤ ω := hE.nonneg
  refine limit_holder_of_two_centre hθ hθ1 hC hK.le hT (norm_nonneg (x - y)) hs₀
    (ex := fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (θ ^ j * s₀)
      (νx j) + ω * (θ ^ j * s₀))
    (ey := fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable y (θ ^ j * s₀)
      (νy j) + ω * (θ ^ j * s₀))
    hex hey hxr hyr h0 ?_
  intro j hj
  have hθj : 0 < θ ^ j := pow_pos hθ j
  have hθj1 : θ ^ j ≤ 1 := pow_le_one₀ hθ.le hθ1.le
  have hs : 0 < θ ^ j * s₀ := mul_pos hθj hs₀
  have hs1 : θ ^ j * s₀ ≤ 1 := by
    calc θ ^ j * s₀ ≤ 1 * 1 := mul_le_mul hθj1 hs₀1 hs₀.le zero_le_one
      _ = 1 := one_mul 1
  have hωs : ω * (θ ^ j * s₀) ≤ 1 := by
    calc ω * (θ ^ j * s₀) ≤ ω * s₀ := by
          apply mul_le_mul_of_nonneg_left _ hω
          calc θ ^ j * s₀ ≤ 1 * s₀ := mul_le_mul_of_nonneg_right hθj1 hs₀.le
            _ = s₀ := one_mul s₀
      _ ≤ 1 := hωs₀
  have hωs0 : 0 ≤ ω * (θ ^ j * s₀) := mul_nonneg hω hs.le
  have h := hcompare E ω hE x y (νx j) (νy j) (θ ^ j * s₀) hx hs hs1 hωs (hux j) (huy j) hj
  have hsum : cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (θ ^ j * s₀) (νx j) +
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable y (θ ^ j * s₀) (νy j) ≤
      (cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (θ ^ j * s₀) (νx j) +
        ω * (θ ^ j * s₀)) +
      (cylindricalExcess E hE.locallyFinite hE.nullMeasurable y (θ ^ j * s₀) (νy j) +
        ω * (θ ^ j * s₀)) := by linarith
  exact h.trans (mul_le_mul_of_nonneg_left hsum hK.le)

end LiquidDrop
