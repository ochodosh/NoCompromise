module

public import NoCompromise.Regularity.Monotonicity
public import NoCompromise.Regularity.PerimeterConvergence
public import NoCompromise.DeGiorgi.BlowupCompactness

@[expose] public section

/-!
# Constant density ratios of a tangent limit

The rescaled ball perimeters converge to θR² at each fixed positive radius.
Perimeter convergence first identifies the limiting ball masses at almost every
radius. Monotonicity of ball mass and continuity of θR² remove all exceptional
radii. No spherical trace convergence or convergence of normals is assumed.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tangent_monotone_ae_eq_continuous {f g : ℝ → ℝ}
    (hf : MonotoneOn f (Ioi 0)) (hg : Continuous g)
    (he : ∀ᵐ r : ℝ, 0 < r → f r = g r) {R : ℝ} (hR : 0 < R) : f R = g R := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have ht : ∀ᶠ s in 𝓝 R, g s < g R + ε :=
      hg.continuousAt.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp ht
    obtain ⟨s, hs, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (show volume (Ioo R (R + δ)) ≠ 0 by
        rw [Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero]; linarith)
      (ae_restrict_of_ae he)
    have hsR : 0 < s := hR.trans hs.1
    have hnear : dist s R < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hs.1)]
      linarith [hs.2]
    have h₁ := hf hR hsR hs.1.le
    rw [hgood hsR] at h₁
    exact h₁.trans (hb hnear).le
  · apply le_of_forall_pos_le_add
    intro ε hε
    have ht : ∀ᶠ s in 𝓝 R, g R - ε < g s :=
      hg.continuousAt.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp ht
    have hmR : max 0 (R - δ) < R := max_lt hR (by linarith)
    obtain ⟨s, hs, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (show volume (Ioo (max 0 (R - δ)) R) ≠ 0 by
        rw [Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero]; linarith)
      (ae_restrict_of_ae he)
    have hs0 : 0 < s := (le_max_left _ _).trans_lt hs.1
    have hsδ : R - δ < s := (le_max_right _ _).trans_lt hs.1
    have hnear : dist s R < δ := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs.2)]
      linarith
    have h₁ := hf hs0 hR hs.2.le
    rw [hgood hs0] at h₁
    linarith [hb hnear]

/-- A genuine perimeter density limit fixes every rescaled ball-mass limit. -/
lemma tendsto_perimeterIn_blowupSet_ball_of_density
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (x : AmbientSpace)
    {θ : ℝ} (hθ : Tendsto (fun s : ℝ => (perimeterIn E (ball x s)).toReal / s ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 θ)) {r : ℕ → ℝ}
    (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0)) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun j => (perimeterIn (blowupSet E x (r j)) (ball 0 R)).toReal)
      atTop (𝓝 (θ * R ^ 2)) := by
  have htR : Tendsto (fun j => r j * R) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa using ht.mul_const R, Eventually.of_forall fun j => mul_pos (hr j) hR⟩
  have h := (hθ.comp htR).mul_const (R ^ 2)
  convert h using 1
  funext j
  rw [perimeterIn_blowupSet_ball_real E hE hmE x (hr j), measureReal_def,
    canonicalPerimeterMeasure_open E hE hmE isOpen_ball]
  simp only [Function.comp_apply]
  field_simp [(hr j).ne', hR.ne']

/-- Continuity-set convergence yields the exact density identity at every
positive radius of the actual limit, including radii with initially unknown sphere mass. -/
theorem tangent_density_of_perimeter_convergence
    {E F : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (x : AmbientSpace)
    (hF : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) univ)
    {θ : ℝ} (hθ : Tendsto (fun s : ℝ => (perimeterIn E (ball x s)).toReal / s ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 θ)) {r : ℕ → ℝ}
    (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    (hper : ∀ R : ℝ, 0 < R →
      localPerimeterMeasure isOpen_univ hF (Subtype.val ⁻¹' frontier (ball 0 R)) = 0 →
      Tendsto (fun j => perimeterIn (blowupSet E x (r j)) (ball 0 R))
        atTop (𝓝 (perimeterIn F (ball 0 R)))) :
    ∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal = θ * R ^ 2 := by
  let : LocallyCompactSpace (univ : Set AmbientSpace) := isOpen_univ.locallyCompactSpace
  let μ := localPerimeterMeasure isOpen_univ hF
  let : IsFiniteMeasureOnCompacts μ := (localPerimeterMeasure_data isOpen_univ hF).2.1
  have hp (R : ℝ) : perimeterIn F (ball 0 R) < ∞ :=
    hF.2 _ isOpen_ball isBounded_ball.isCompact_closure (subset_univ _)
  have he : ∀ᵐ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal = θ * R ^ 2 := by
    filter_upwards [ae_local_measure_sphere_eq_zero μ (0 : AmbientSpace)] with R hnull hR
    have hn : μ (Subtype.val ⁻¹' frontier (ball 0 R)) = 0 :=
      measure_mono_null (preimage_mono frontier_ball_subset_sphere) hnull
    have hc := (ENNReal.tendsto_toReal (hp R).ne).comp (hper R hR hn)
    exact tendsto_nhds_unique hc
      (tendsto_perimeterIn_blowupSet_ball_of_density hE hmE x hθ hr ht hR)
  intro R hR
  apply tangent_monotone_ae_eq_continuous _ (by fun_prop) he hR
  intro a ha b hb hab
  exact ENNReal.toReal_mono (hp b).ne (variation_mono measurableSet_ball (ball_subset_ball hab))

end LiquidDrop
