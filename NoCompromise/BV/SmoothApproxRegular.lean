module

public import NoCompromise.BV.SmoothApproxLevels
public import NoCompromise.BV.SmoothApproxDilation

@[expose] public section

/-!
# Strict approximation by bounded open regular superlevels

A slowly widening level interval is combined with a subsequence of the
whole-space strict scalar approximation. Every chosen level is an actual
regular value. Lower semicontinuity supplies the matching perimeter lower bound.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma isBounded_positive_superlevel {u : AmbientSpace → ℝ} (hc : HasCompactSupport u)
    {t : ℝ} (ht : 0 < t) : Bornology.IsBounded {x | t < u x} :=
  hc.isBounded.subset (fun x hx => subset_tsupport u (by
    change u x ≠ 0
    linarith [show t < u x from hx]))

lemma tendsto_integral_norm_indicator_sub_of_eLpNorm
    {E : ℕ → Set AmbientSpace} {F : Set AmbientSpace}
    (hmE : ∀ j, NullMeasurableSet (E j) volume) (hmF : NullMeasurableSet F volume)
    (hvE : ∀ j, volume (E j) < ∞) (hvF : volume F < ∞)
    (ht : Tendsto (fun j => eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - F.indicator (fun _ => (1 : ℝ))) 1 volume)
      atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x,
      ‖(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x‖)
      atTop (𝓝 0) := by
  have hiE (j) : Integrable ((E j).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) (hvE j).ne).integrable_indicator₀ (hmE j)
  have hiF : Integrable (F.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) hvF.ne).integrable_indicator₀ hmF
  have heq (j) : (eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - F.indicator (fun _ => (1 : ℝ)))
      1 volume).toReal = ∫ x,
        ‖(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x‖ := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hiE j).sub hiF).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hiE j).sub hiF),
      ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
    rfl
  simpa only [Function.comp_def, heq, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht

lemma perimeter_le_liminf_of_global_indicator_l1
    {E : ℕ → Set AmbientSpace} {F : Set AmbientSpace}
    (hmE : ∀ j, NullMeasurableSet (E j) volume) (hmF : NullMeasurableSet F volume)
    (hvE : ∀ j, volume (E j) < ∞) (hvF : volume F < ∞)
    (ht : Tendsto (fun j => eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - F.indicator (fun _ => (1 : ℝ))) 1 volume)
      atTop (𝓝 0)) : perimeter F ≤ liminf (fun j => perimeter (E j)) atTop := by
  have hglobal := tendsto_integral_norm_indicator_sub_of_eLpNorm hmE hmF hvE hvF ht
  have hiE (j) : Integrable ((E j).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) (hvE j).ne).integrable_indicator₀ (hmE j)
  have hiF : Integrable (F.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) hvF.ne).integrable_indicator₀ hmF
  have hlsc := perimeterIn_le_liminf_of_locally_l1 isOpen_univ hmE hmF (by
    intro K _ _
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) _
      (show Tendsto (fun j => ∫ x,
        |(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
          atTop (𝓝 0) from by simpa only [Real.norm_eq_abs] using hglobal)
    intro j
    exact setIntegral_le_integral ((hiE j).sub hiF).abs
      (Eventually.of_forall fun _ => abs_nonneg _))
  change perimeterN F ≤ liminf (fun j => perimeterN (E j)) atTop at hlsc
  simpa only [perimeterN_eq_perimeter F hmF, perimeterN_eq_perimeter _ (hmE _)] using hlsc

/-- Bounded open regular superlevels approximate every finite-volume BV set
strictly. Smooth-boundary charts are supplied separately by the regular-value
geometry; no such geometric conclusion is assumed here. -/
theorem exists_bounded_regular_superlevel_approximation {E : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hvE : volume E < ∞) (hpE : HasFinitePerimeter E) :
    ∃ u : ℕ → AmbientSpace → ℝ, ∃ t : ℕ → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j) ∧ HasCompactSupport (u j) ∧
        0 < t j ∧ t j < 1 ∧ (∀ x, u j x = t j → gradient (u j) x ≠ 0) ∧
        IsOpen {x | t j < u j x} ∧ Bornology.IsBounded {x | t j < u j x}) ∧
      Tendsto (fun j => eLpNorm
        (({x | t j < u j x}).indicator (fun _ => (1 : ℝ)) -
          E.indicator (fun _ => (1 : ℝ))) 1 volume) atTop (𝓝 0) ∧
      Tendsto (fun j => perimeter {x | t j < u j x}) atTop (𝓝 (perimeter E)) := by
  have hiE : Integrable (E.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) hvE.ne).integrable_indicator₀ hmE
  have hBV : IsBVOn (E.indicator (fun _ => (1 : ℝ))) univ :=
    ⟨hiE.integrableOn, hpE⟩
  obtain ⟨v, hv, hvl1, hvgrad⟩ := strict_approximation_univ hBV
  let a (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹ / 4
  have ha (k) : 0 < a k := by dsimp [a]; positivity
  have hab (k) : a k < 1 - a k := by
    have hn : 1 ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hh : ((k : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hn
    dsimp only [a]
    linarith
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, one_div, zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 4
  let err (k j : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    ((a k)⁻¹ * ∫ x, ‖v j x - E.indicator (fun _ => (1 : ℝ)) x‖)
  have herr (k) : Tendsto (err k) atTop (𝓝 0) := by
    simpa only [err, Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hvl1.const_mul (a k)⁻¹)
  obtain ⟨σ, hσ, hdiag⟩ := exists_strictMono_diagonal_tendsto_zero herr
  choose t ht hreg hper using fun k => exists_regular_level_perimeter_le
    ((hv (σ k)).1.of_le (by simp)) (hv (σ k)).2.2.2 (hab k)
  have htp (k) : 0 < t k := (ha k).trans (ht k).1
  have htu (k) : t k < 1 := (ht k).2.trans (by linarith [ha k])
  have hmeta (k) : IsOpen {x | t k < v (σ k) x} ∧
      Bornology.IsBounded {x | t k < v (σ k) x} :=
    ⟨isOpen_lt continuous_const (hv (σ k)).1.continuous,
      isBounded_positive_superlevel (hv (σ k)).2.1 (htp k)⟩
  have hl1 : Tendsto (fun k => eLpNorm
      (({x | t k < v (σ k) x}).indicator (fun _ => (1 : ℝ)) -
        E.indicator (fun _ => (1 : ℝ))) 1 volume) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiag
      (fun _ => bot_le)
    intro k
    exact eLpNorm_superlevelIndicator_sub_indicator_le hmE hvE (hv (σ k)).1.continuous
      (hv (σ k)).2.2.1 (ha k) (ht k).1.le (ht k).2.le
  refine ⟨fun k => v (σ k), t, fun k => ⟨(hv (σ k)).1, (hv (σ k)).2.1,
    htp k, htu k, hreg k, (hmeta k).1, (hmeta k).2⟩, hl1, ?_⟩
  have hgrad : Tendsto (fun k => ENNReal.ofReal (∫ x, ‖gradient (v (σ k)) x‖))
      atTop (𝓝 (perimeter E)) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hvgrad.comp hσ.tendsto_atTop)
    have heq : ENNReal.ofReal (variation (E.indicator (fun _ => (1 : ℝ))) univ).toReal =
        perimeter E := (ENNReal.ofReal_toReal hpE.ne).trans (perimeterN_eq_perimeter E hmE)
    simpa only [Function.comp_def, heq] using hh
  have hden : Tendsto (fun k => ENNReal.ofReal ((1 - a k) - a k)) atTop (𝓝 1) := by
    simpa only [sub_zero, ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (((tendsto_const_nhds (x := (1 : ℝ))).sub hat).sub hat)
  have hup : Tendsto (fun k => ENNReal.ofReal (∫ x, ‖gradient (v (σ k)) x‖) /
      ENNReal.ofReal ((1 - a k) - a k)) atTop (𝓝 (perimeter E)) := by
    simpa only [div_one] using ENNReal.Tendsto.div hgrad (Or.inr one_ne_zero) hden
      (Or.inl ENNReal.one_ne_top)
  have hlsc := perimeter_le_liminf_of_global_indicator_l1
    (fun k => (hmeta k).1.measurableSet.nullMeasurableSet) hmE
    (fun k => (hmeta k).2.measure_lt_top) hvE hl1
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact eventually_lt_of_lt_liminf (hb.trans_le hlsc)
  · intro b hb
    exact ((tendsto_order.mp hup).2 b hb).mono fun k hk => (hper k).trans_lt hk

end LiquidDrop
