import NoCompromise.Regularity.FixedNormalExcessPairing

/-! # Upgrading smooth polar pairings to compact continuous tests -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- The continuous-test upgrade derives its uniform compact mass bound from
positive-measure convergence. The only vector convergence assumed is the
actual distributional convergence on supported C¹ fields. -/
theorem tendsto_normal_pairing_of_smooth_tests {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (μs : ℕ → Measure (EuclideanSpace ℝ (Fin n))) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (σs : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hfin : ∀ j K, IsCompact K → K ⊆ U → μs j K < ∞)
    (hμfin : ∀ K, IsCompact K → K ⊆ U → μ K < ∞)
    (hmeas : ∀ j, Measurable (σs j)) (hσ : Measurable σ)
    (hunit : ∀ j, ∀ᵐ x ∂(μs j).restrict U, ‖σs j x‖ = 1)
    (hσunit : ∀ᵐ x ∂μ.restrict U, ‖σ x‖ = 1)
    (hμ : ∀ φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ,
      tsupport φ ⊆ U →
      Tendsto (fun j => ∫ x, φ x ∂μs j) atTop (𝓝 (∫ x, φ x ∂μ)))
    (ht : ∀ Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 1 Y → HasCompactSupport Y → tsupport Y ⊆ U →
      Tendsto (fun j => ∫ x, inner ℝ (Y x) (σs j x) ∂μs j) atTop
        (𝓝 (∫ x, inner ℝ (Y x) (σ x) ∂μ)))
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : Continuous X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    Tendsto (fun j => ∫ x, inner ℝ (X x) (σs j x) ∂μs j) atTop
      (𝓝 (∫ x, inner ℝ (X x) (σ x) ∂μ)) := by
  obtain ⟨K, Y, hK, hKU, hXK, hY, hYX⟩ := exists_smooth_field_approximation hU hX hcX hsX
  obtain ⟨C, hC, hmass⟩ := eventually_compact_mass_bound_of_test_convergence hU μs μ hfin hμ hK hKU
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (3 * (C + μ.real K + 1))
  have hden : 0 < C + μ.real K + 1 := by positivity
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hden)
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformly_iff.mp hYX δ hδ).exists
  have hclose : ∀ x, ‖X x - Y k x‖ ≤ δ := by
    intro x
    simpa only [dist_eq_norm, norm_sub_rev] using (hk x).le
  have hcloses : ∀ x, ‖Y k x - X x‖ ≤ δ := by
    intro x
    simpa only [norm_sub_rev] using hclose x
  have hlim := ht (Y k) (hY k).1 (hY k).2.1 ((hY k).2.2.trans hKU)
  filter_upwards [hmass, (Metric.tendsto_nhds.mp hlim) (ε / 3) (by positivity)] with j hj hmid
  let a := ∫ x, inner ℝ (X x) (σs j x) ∂μs j
  let b := ∫ x, inner ℝ (Y k x) (σs j x) ∂μs j
  let c := ∫ x, inner ℝ (Y k x) (σ x) ∂μ
  let d := ∫ x, inner ℝ (X x) (σ x) ∂μ
  have h₁ : ‖a - b‖ ≤ δ * (μs j).real K :=
    norm_normal_pairing_sub_le hK hKU (hfin j K hK hKU) (hmeas j) (hunit j)
      hX hXK (hY k).1.continuous (hY k).2.2 hclose
  have h₂ : ‖b - c‖ < ε / 3 := hmid
  have h₃ : ‖c - d‖ ≤ δ * μ.real K :=
    norm_normal_pairing_sub_le hK hKU (hμfin K hK hKU) hσ hσunit
      (hY k).1.continuous (hY k).2.2 hX hXK hcloses
  change ‖a - d‖ < ε
  have htri : ‖a - d‖ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - d‖ := by
    have he : a - d = (a - b) + (b - c) + (c - d) := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hδeq : δ * (3 * (C + μ.real K + 1)) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  have hm := mul_le_mul_of_nonneg_left hj hδ.le
  nlinarith

end LiquidDrop
