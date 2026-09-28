import NoCompromise.DeGiorgi.BlowupCompactness

/-!
# Both phases persist in blow-up limits

Local L¹ convergence transfers the uniform cubic lower bounds to every fixed
ball in the limit. The statements use the actual ball volumes of the limit set.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

lemma integral_indicator_one_on {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume)
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    (∫ x in A, E.indicator (fun _ => (1 : ℝ)) x) = (volume (E ∩ A)).toReal := by
  rw [integral_indicator₀ (hE.mono Measure.restrict_le_self), integral_const]
  simp only [smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ]
  rw [Measure.restrict_apply₀ (hE.mono Measure.restrict_le_self)]

/-- L¹ convergence of indicators on a bounded region implies convergence of their volumes. -/
theorem tendsto_volume_inter_of_indicator_l1 {n : ℕ}
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))} {F A : Set (EuclideanSpace ℝ (Fin n))}
    (hE : ∀ j, NullMeasurableSet (E j) volume) (hF : NullMeasurableSet F volume)
    (hcA : IsCompact (closure A))
    (ht : Tendsto (fun j => ∫ x in A,
      |(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
      atTop (𝓝 0)) :
    Tendsto (fun j => (volume (E j ∩ A)).toReal) atTop (𝓝 (volume (F ∩ A)).toReal) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro j
  have hj := (locallyIntegrable_indicator_one (hE j)).integrableOn_isCompact hcA
  have hF' := (locallyIntegrable_indicator_one hF).integrableOn_isCompact hcA
  rw [← integral_indicator_one_on (hE j), ← integral_indicator_one_on hF,
    ← integral_sub (hj.mono_set subset_closure) (hF'.mono_set subset_closure)]
  exact norm_integral_le_integral_norm _

lemma abs_indicator_compl_sub {α : Type*} (E F : Set α) (x : α) :
    |Eᶜ.indicator (fun _ => (1 : ℝ)) x - Fᶜ.indicator (fun _ => (1 : ℝ)) x| =
      |E.indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x| := by
  by_cases hE : x ∈ E <;> by_cases hF : x ∈ F <;> simp [hE, hF]

lemma radialVolume_blowupSet (E : Set AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    radialVolume (blowupSet E x r) 0 R = (r⁻¹) ^ 3 * radialVolume E x (r * R) := by
  unfold radialVolume
  rw [volume_blowupSet_inter_ball E x hr R, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r⁻¹) ^ 3)]

/-- Any local indicator limit inherits the two-sided cubic volume bound. -/
theorem blowup_limit_volume_lower_bounds :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
      (hmE : NullMeasurableSet E volume) (x : AmbientSpace), x ∈ reducedBoundary E hE hmE →
      ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Tendsto r atTop (𝓝 0) →
      ∀ F : Set AmbientSpace, NullMeasurableSet F volume →
        (∀ K : Set AmbientSpace, IsCompact K →
          Tendsto (fun j => ∫ y in K,
            |(blowupSet E x (r j)).indicator (fun _ => (1 : ℝ)) y -
              F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0)) →
        ∀ R : ℝ, 0 < R →
          κ * R ^ 3 ≤ radialVolume F 0 R ∧ κ * R ^ 3 ≤ radialVolume Fᶜ 0 R := by
  obtain ⟨κ, hκ, hb⟩ := reduced_density_lower_bounds
  refine ⟨κ, hκ, fun E hE hmE x hx r hr ht F hF hlim R hR => ?_⟩
  obtain ⟨δ, hδ, hb⟩ := hb E hE hmE x hx
  have hsmall : ∀ᶠ j in atTop, r j * R < δ := by
    exact (ht.mul_const R).eventually (Iio_mem_nhds (show 0 * R < δ by simpa using hδ))
  have hlower : ∀ᶠ j in atTop,
      κ * R ^ 3 ≤ radialVolume (blowupSet E x (r j)) 0 R ∧
      κ * R ^ 3 ≤ radialVolume (blowupSet E x (r j))ᶜ 0 R := by
    filter_upwards [hsmall] with j hj
    have h := hb (r j * R) (mul_pos (hr j) hR) hj.le
    have hcompl : (blowupSet E x (r j))ᶜ = blowupSet Eᶜ x (r j) := rfl
    rw [hcompl, radialVolume_blowupSet E x (hr j), radialVolume_blowupSet Eᶜ x (hr j)]
    have heq : (r j)⁻¹ ^ 3 * (κ * (r j * R) ^ 3) = κ * R ^ 3 := by
      field_simp [(hr j).ne']
    constructor
    · have hm := mul_le_mul_of_nonneg_left h.1
        (pow_nonneg (inv_nonneg.mpr (hr j).le) 3)
      simpa only [heq] using hm
    · have hm := mul_le_mul_of_nonneg_left h.2
        (pow_nonneg (inv_nonneg.mpr (hr j).le) 3)
      simpa only [heq] using hm
  have hmeas (j) := nullMeasurableSet_blowupSet hmE x (hr j)
  have hball : Tendsto (fun j => ∫ y in ball (0 : AmbientSpace) R,
      |(blowupSet E x (r j)).indicator (fun _ => (1 : ℝ)) y -
        F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0) := by
    apply tendsto_l1_on_subset ball_subset_closedBall
      (fun j => (locallyIntegrable_indicator_one (hmeas j)).integrableOn_isCompact
        (isCompact_closedBall 0 R))
      ((locallyIntegrable_indicator_one hF).integrableOn_isCompact (isCompact_closedBall 0 R))
      (hlim _ (isCompact_closedBall 0 R))
  have hballc : Tendsto (fun j => ∫ y in ball (0 : AmbientSpace) R,
      |(blowupSet E x (r j))ᶜ.indicator (fun _ => (1 : ℝ)) y -
        Fᶜ.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0) := by
    simpa only [abs_indicator_compl_sub] using hball
  have htvol := tendsto_volume_inter_of_indicator_l1 hmeas hF
    isBounded_ball.isCompact_closure hball
  have htvolc := tendsto_volume_inter_of_indicator_l1 (fun j => (hmeas j).compl) hF.compl
    isBounded_ball.isCompact_closure hballc
  exact ⟨ge_of_tendsto htvol (hlower.mono fun _ h => h.1),
    ge_of_tendsto htvolc (hlower.mono fun _ h => h.2)⟩

/-- Both phases of every blow-up limit meet every positive-radius origin ball. -/
theorem blowup_limit_volume_sides_pos (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {F : Set AmbientSpace} (hF : NullMeasurableSet F volume)
    (hlim : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ y in K,
        |(blowupSet E x (r j)).indicator (fun _ => (1 : ℝ)) y -
          F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0)) :
    ∀ R : ℝ, 0 < R → 0 < volume (F ∩ ball 0 R) ∧ 0 < volume (ball 0 R \ F) := by
  obtain ⟨κ, hκ, hb⟩ := blowup_limit_volume_lower_bounds
  intro R hR
  have h := hb E hE hmE x hx r hr ht F hF hlim R hR
  have hl : 0 < radialVolume F 0 R := (mul_pos hκ (pow_pos hR 3)).trans_le h.1
  have hc : 0 < radialVolume Fᶜ 0 R := (mul_pos hκ (pow_pos hR 3)).trans_le h.2
  exact ⟨ENNReal.toReal_pos_iff.mp hl |>.1,
    by simpa only [sdiff_eq_compl_inter] using (ENNReal.toReal_pos_iff.mp hc).1⟩

end LiquidDrop
