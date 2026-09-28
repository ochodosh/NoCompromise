import NoCompromise.BV.SmoothApproxRegular

/-!
# Exact-volume correction of strictly approximating sets

The correcting factors are the actual cube roots of the volume ratios. The
strong dilation theorem controls the corrected indicators, and exact perimeter
scaling controls their perimeters.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tendsto_volumeReal_of_indicator_l1 {E : ℕ → Set AmbientSpace} {G : Set AmbientSpace}
    (hmE : ∀ j, NullMeasurableSet (E j) volume) (hmG : NullMeasurableSet G volume)
    (hvE : ∀ j, volume (E j) < ∞) (hvG : volume G < ∞)
    (ht : Tendsto (fun j => eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - G.indicator (fun _ => (1 : ℝ))) 1 volume)
      atTop (𝓝 0)) : Tendsto (fun j => volume.real (E j)) atTop (𝓝 (volume.real G)) := by
  have hiE (j) : Integrable ((E j).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) (hvE j).ne).integrable_indicator₀ (hmE j)
  have hiG : Integrable (G.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) hvG.ne).integrable_indicator₀ hmG
  have hl1 := tendsto_integral_norm_indicator_sub_of_eLpNorm hmE hmG hvE hvG ht
  have heq (S : Set AmbientSpace) (hmS : NullMeasurableSet S volume) :
      (∫ x, S.indicator (fun _ => (1 : ℝ)) x) = volume.real S := by
    rw [integral_indicator₀ hmS, setIntegral_const]
    simp only [smul_eq_mul, mul_one]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hl1
  intro j
  rw [← heq (E j) (hmE j), ← heq G hmG, ← integral_sub (hiE j) hiG]
  exact norm_integral_le_integral_norm _

/-- Positive finite-volume approximants can be normalized exactly without
losing global L¹ or perimeter convergence. -/
theorem exists_volume_correcting_dilations {E : ℕ → Set AmbientSpace} {G : Set AmbientSpace}
    (hmE : ∀ j, NullMeasurableSet (E j) volume) (hmG : NullMeasurableSet G volume)
    (hvE : ∀ j, volume (E j) < ∞) (hvG : volume G < ∞)
    (hpE : ∀ j, 0 < volume (E j)) (hpG : 0 < volume G)
    (ht : Tendsto (fun j => eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - G.indicator (fun _ => (1 : ℝ))) 1 volume)
      atTop (𝓝 0))
    (hper : Tendsto (fun j => perimeter (E j)) atTop (𝓝 (perimeter G))) :
    ∃ r : ℕ → ℝ, (∀ j, 0 < r j ∧ volume ((fun x => r j • x) '' E j) = volume G) ∧
      Tendsto r atTop (𝓝 1) ∧
      Tendsto (fun j => eLpNorm
        (((fun x => r j • x) '' E j).indicator (fun _ => (1 : ℝ)) -
          G.indicator (fun _ => (1 : ℝ))) 1 volume) atTop (𝓝 0) ∧
      Tendsto (fun j => perimeter ((fun x => r j • x) '' E j)) atTop (𝓝 (perimeter G)) := by
  have hmpos : 0 < volume.real G := ENNReal.toReal_pos hpG.ne' hvG.ne
  have hjpos (j) : 0 < volume.real (E j) := ENNReal.toReal_pos (hpE j).ne' (hvE j).ne
  let r (j : ℕ) : ℝ := (volume.real G / volume.real (E j)) ^ ((1 : ℝ) / 3)
  have hr (j) : 0 < r j := Real.rpow_pos_of_pos (div_pos hmpos (hjpos j)) _
  have hr3 (j) : r j ^ 3 = volume.real G / volume.real (E j) := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hmpos.le (hjpos j).le)]
    norm_num
  have hvol := tendsto_volumeReal_of_indicator_l1 hmE hmG hvE hvG ht
  have hquot : Tendsto (fun j => volume.real G / volume.real (E j)) atTop (𝓝 1) := by
    convert (tendsto_const_nhds (x := volume.real G)).div hvol hmpos.ne' using 1
    all_goals first | rfl | rw [div_self hmpos.ne']
  have hrt : Tendsto r atTop (𝓝 1) := by
    simpa only [r, Real.one_rpow] using
      hquot.rpow_const (p := (1 : ℝ) / 3) (Or.inl one_ne_zero)
  refine ⟨r, fun j => ⟨hr j, ?_⟩, hrt,
    tendsto_eLpNorm_indicator_dilate_sub hmE hmG hvE hvG ht (fun j => (hr j).ne') hrt, ?_⟩
  · rw [volume_image_smul _ (hr j), hr3 j,
      ← ENNReal.ofReal_toReal (hvE j).ne, ← ENNReal.ofReal_mul
        (div_nonneg hmpos.le (hjpos j).le)]
    rw [show (volume (E j)).toReal = volume.real (E j) from rfl,
      div_mul_cancel₀ _ (hjpos j).ne']
    exact ENNReal.ofReal_toReal hvG.ne
  · have hc : Tendsto (fun j => ENNReal.ofReal (r j ^ 2)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, one_pow, ENNReal.ofReal_one] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hrt.pow 2)
    have hh := ENNReal.Tendsto.mul hc (Or.inl one_ne_zero) hper (Or.inr ENNReal.one_ne_top)
    simpa only [one_mul, ← perimeter_image_smul (hmE _) (hr _)] using hh

/-- Once exact volume and strict convergence have been established, the actual
Coulomb term and the total liquid-drop energy converge. -/
theorem tendsto_energy_of_exact_volume_strict {E : ℕ → Set AmbientSpace} {G : Set AmbientSpace}
    (hmE : ∀ j, NullMeasurableSet (E j) volume) (hmG : NullMeasurableSet G volume)
    (hvG : volume G < ∞) (hvE : ∀ j, volume (E j) = volume G)
    (hpG : perimeter G < ∞)
    (ht : Tendsto (fun j => eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - G.indicator (fun _ => (1 : ℝ))) 1 volume)
      atTop (𝓝 0))
    (hper : Tendsto (fun j => perimeter (E j)) atTop (𝓝 (perimeter G))) :
    Tendsto (fun j => (coulombEnergy (E j)).toReal) atTop (𝓝 (coulombEnergy G).toReal) ∧
      Tendsto (fun j => (energy (E j)).toReal) atTop (𝓝 (energy G).toReal) := by
  have hvol (j) : volume (E j) < ∞ := (hvE j) ▸ hvG
  have hl1 := tendsto_integral_norm_indicator_sub_of_eLpNorm hmE hmG hvol hvG ht
  have hbound : volume G ≤ ENNReal.ofReal (volume.real G) := by
    rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal hvG.ne]
  have hc := tendsto_coulombEnergy_of_l1 hmE hmG ENNReal.toReal_nonneg
    (fun j => (hvE j).le.trans hbound) hbound
    (by simpa only [Real.norm_eq_abs] using hl1)
  refine ⟨hc, ?_⟩
  have hp := (ENNReal.tendsto_toReal hpG.ne).comp hper
  have hsum := hp.add hc
  have hfinite : ∀ᶠ j in atTop, perimeter (E j) < ∞ :=
    (tendsto_order.mp hper).2 ∞ hpG
  have hGfin := coulombEnergy_lt_top G hvG
  have hEq : ∀ᶠ j in atTop, (energy (E j)).toReal =
      (perimeter (E j)).toReal + (coulombEnergy (E j)).toReal := by
    filter_upwards [hfinite] with j hj
    exact ENNReal.toReal_add hj.ne (coulombEnergy_lt_top (E j) (hvol j)).ne
  have htarget : (energy G).toReal = (perimeter G).toReal + (coulombEnergy G).toReal :=
    ENNReal.toReal_add hpG.ne hGfin.ne
  rw [htarget]
  exact hsum.congr' (hEq.mono fun _ hj => hj.symm)

end LiquidDrop
