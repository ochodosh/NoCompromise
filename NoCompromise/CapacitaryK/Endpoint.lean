import NoCompromise.CapacitaryK.Representatives

/-!
# Endpoint limits at `t ↑ 1` (chapter 31, `thm:capacitary-inequalities`, endpoint step)

`thm:capacitary-inequalities` passes to the left limits `p(1) := lim_{t↑1} p(t)` and
`F(1) := lim_{t↑1} F̂(t)` of the canonical representatives (`def:K-p`, `def:K-Fhat`). This file
proves that both limits exist, with explicit values, as soon as the collar `{t₀ < u < 1}` has
finite `μ`-mass: `p(t) → p(t₀) + μ{t₀ < u < 1}` and `F̂(t) → F̂(t₀) + ∫_{t₀}^1 p`.

For the capacitary potential, finiteness of the collar mass and the identification of the limits
with `∫_{∂K} H|∇u|` and `∫_{∂K} |∇u|²` come from regularity of `u` up to `∂K`
(`thm:capacitary-potential`, `thm:boundary-C2a`) and smooth convergence of the levels to `∂K`;
these are not formalised here.
-/

noncomputable section
open Real Set Filter MeasureTheory intervalIntegral Topology
open scoped ENNReal

namespace LiquidDrop.CapacitaryK

variable {X : Type*} [MeasurableSpace X]

/-- On the collar `t₀ ≤ t < 1`: `p(t) = p(t₀) + μ{t₀ < u < 1} - μ{t < u < 1}` when the collar
`{t₀ < u < 1}` has finite `μ`-mass. -/
lemma Kp_eq_collar_sub {μ : Measure X} {u : X → ℝ} (hu : Measurable u) {t₀ p₀ : ℝ}
    (hcollar : μ (u ⁻¹' Ioo t₀ 1) ≠ ⊤) {t : ℝ} (ht : t ∈ Ico t₀ 1) :
    Kp μ u t₀ p₀ t = p₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal - (μ (u ⁻¹' Ioo t 1)).toReal := by
  have hsplit : u ⁻¹' Ioo t₀ 1 = u ⁻¹' Ioc t₀ t ∪ u ⁻¹' Ioo t 1 := by
    rw [← preimage_union, Ioc_union_Ioo_eq_Ioo ht.1 ht.2]
  have hdisj : Disjoint (u ⁻¹' Ioc t₀ t) (u ⁻¹' Ioo t 1) :=
    Set.disjoint_left.mpr fun x hx hy => absurd hy.1 (not_lt.mpr hx.2)
  have hm := measure_union hdisj (hu measurableSet_Ioo) (μ := μ)
  rw [← hsplit] at hm
  have h1 : μ (u ⁻¹' Ioc t₀ t) ≠ ⊤ :=
    ne_top_of_le_ne_top hcollar (measure_mono (by rw [hsplit]; exact subset_union_left))
  have h2 : μ (u ⁻¹' Ioo t 1) ≠ ⊤ :=
    ne_top_of_le_ne_top hcollar (measure_mono (by rw [hsplit]; exact subset_union_right))
  have hr := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_add h1 h2] at hr
  simp only [Kp, ite_eq_left ht.1]
  linarith

/-- The upper collars `{t < u < 1}` have `μ`-mass tending to `0` as `t ↑ 1`, when
`{t₀ < u < 1}` has finite mass. -/
lemma tendsto_measure_upper_collar {μ : Measure X} {u : X → ℝ} (hu : Measurable u) {t₀ : ℝ}
    (ht₀ : t₀ < 1) (hcollar : μ (u ⁻¹' Ioo t₀ 1) ≠ ⊤) :
    Tendsto (fun t => (μ (u ⁻¹' Ioo t 1)).toReal) (𝓝[<] 1) (𝓝 0) := by
  let S : ℝ → Set X := fun r => u ⁻¹' Ioo (1 - r) 1
  have hS := tendsto_measure_biInter_gt (μ := μ) (s := S) (a := 0)
    (fun r _ => (hu measurableSet_Ioo).nullMeasurableSet)
    (fun i j _ hij => preimage_mono (Ioo_subset_Ioo_left (by linarith)))
    ⟨1 - t₀, by linarith, by simpa [S] using hcollar⟩
  have hempty : (⋂ r > (0 : ℝ), S r) = ∅ := by
    ext x
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hx
    have h1 : u x < 1 := (hx 1 one_pos).2
    have h2 : 1 - (1 - u x) < u x := (hx (1 - u x) (by linarith)).1
    linarith
  rw [hempty, measure_empty] at hS
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hS
  rw [ENNReal.toReal_zero] at hr
  have hsub : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mem_Ioi.mpr (sub_pos.mpr (show t < 1 from ht))
  refine (hr.comp hsub).congr' ?_
  exact Eventually.of_forall fun t => by simp [S, Function.comp]

/-- `thm:capacitary-inequalities`, endpoint step: if the collar `{t₀ < u < 1}` has finite
`μ`-mass then `p(t) → p(t₀) + μ{t₀ < u < 1}` and `F̂(t) → F̂(t₀) + ∫_{t₀}^1 p` as `t ↑ 1`. -/
theorem Kp_KFhat_tendsto_one {μ : Measure X} {u : X → ℝ} (hu : Measurable u) {t₀ p₀ F₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hcollar : μ (u ⁻¹' Ioo t₀ 1) ≠ ⊤) :
    Tendsto (Kp μ u t₀ p₀) (𝓝[<] 1) (𝓝 (p₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal)) ∧
      Tendsto (KFhat μ u t₀ p₀ F₀) (𝓝[<] 1) (𝓝 (F₀ + ∫ t in t₀..1, Kp μ u t₀ p₀ t)) := by
  set L := (μ (u ⁻¹' Ioo t₀ 1)).toReal
  have hcol : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo t₀ 1 := Ioo_mem_nhdsLT ht₀.2
  refine ⟨?_, ?_⟩
  · have h := (tendsto_const_nhds (x := p₀ + L)).sub
      (tendsto_measure_upper_collar hu ht₀.2 hcollar)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [hcol] with t ht
    exact (Kp_eq_collar_sub hu hcollar (p₀ := p₀) ⟨ht.1.le, ht.2⟩).symm
  · -- `p` is monotone and bounded on the collar, hence integrable on `[t₀, 1]`.
    have hval : ∀ t ∈ Ioo t₀ 1, Kp μ u t₀ p₀ t = p₀ + (μ (u ⁻¹' Ioc t₀ t)).toReal :=
      fun t ht => by simp only [Kp, ite_eq_left ht.1.le]
    have hle : ∀ t ∈ Ioo t₀ 1, μ (u ⁻¹' Ioc t₀ t) ≤ μ (u ⁻¹' Ioo t₀ 1) :=
      fun t ht => measure_mono (preimage_mono (Ioc_subset_Ioo_right ht.2))
    have hmono : MonotoneOn (Kp μ u t₀ p₀) (Ioo t₀ 1) := by
      intro a ha b hb hab
      rw [hval a ha, hval b hb]
      have := ENNReal.toReal_mono (ne_top_of_le_ne_top hcollar (hle b hb))
        (measure_mono (μ := μ) (preimage_mono (Ioc_subset_Ioc_right hab)))
      linarith
    have hbound : ∀ t ∈ Ioo t₀ 1, ‖Kp μ u t₀ p₀ t‖ ≤ |p₀| + L := by
      intro t ht
      rw [hval t ht, Real.norm_eq_abs]
      have h0 := ENNReal.toReal_nonneg (a := μ (u ⁻¹' Ioc t₀ t))
      have hL := ENNReal.toReal_mono hcollar (hle t ht)
      calc |p₀ + (μ (u ⁻¹' Ioc t₀ t)).toReal| ≤ |p₀| + |(μ (u ⁻¹' Ioc t₀ t)).toReal| :=
            abs_add_le _ _
        _ ≤ |p₀| + L := by rw [abs_of_nonneg h0]; linarith
    have hIoo : IntegrableOn (Kp μ u t₀ p₀) (Ioo t₀ 1) volume := by
      refine ⟨(aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hmono).aestronglyMeasurable,
        HasFiniteIntegral.restrict_of_bounded (C := |p₀| + L) measure_Ioo_lt_top ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using hbound t ht
    have hint : IntervalIntegrable (Kp μ u t₀ p₀) volume t₀ 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht₀.2.le,
        integrableOn_Ioc_iff_integrableOn_Ioo]
      exact hIoo
    have hcont := continuousOn_primitive_interval' hint (left_mem_uIcc (a := t₀) (b := 1))
    have hmem : (1 : ℝ) ∈ uIcc t₀ 1 := right_mem_uIcc
    have hcw : ContinuousWithinAt (fun b => ∫ x in t₀..b, Kp μ u t₀ p₀ x) (Iio 1) 1 := by
      refine (hcont 1 hmem).mono_of_mem_nhdsWithin ?_
      rw [uIcc_of_le ht₀.2.le]
      exact mem_of_superset (Ioo_mem_nhdsLT ht₀.2) Ioo_subset_Icc_self
    exact (tendsto_const_nhds (x := F₀)).add hcw.tendsto

end LiquidDrop.CapacitaryK
