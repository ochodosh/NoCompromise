import NoCompromise.BV.SmoothApproxLevelCharts
import NoCompromise.BV.SmoothApproxVolume

/-!
# Smooth bounded approximation with exact volume

The sets are genuine regular superlevels, selected by BV coarea and Sard.
After discarding finitely many zero-volume approximants, positive homotheties
correct the volume. Strong L¹ dilation continuity preserves convergence.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma image_superlevel_smul {u : AmbientSpace → ℝ} {t r : ℝ} (hr : r ≠ 0) :
    (fun x => r • x) '' {x | t < u x} = {x | t < u (r⁻¹ • x)} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_ofPred_eq, smul_smul, inv_mul_cancel₀ hr, one_smul] using hy
  · intro hx
    exact ⟨r⁻¹ • x, hx, by simp only [smul_smul, mul_inv_cancel₀ hr, one_smul]⟩

/-- Blueprint `thm:smooth-approx`: bounded open smooth-boundary sets with the
exact original volume, global L¹ convergence, and perimeter convergence. -/
theorem smooth_approximation_exact_volume {E : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hvE : volume E < ∞) (hposE : 0 < volume E)
    (hpE : HasFinitePerimeter E) :
    ∃ S : ℕ → Set AmbientSpace,
      (∀ j, IsOpen (S j) ∧ Bornology.IsBounded (S j) ∧ HasSmoothBoundary (S j) ∧
        volume (S j) = volume E) ∧
      Tendsto (fun j => eLpNorm
        ((S j).indicator (fun _ => (1 : ℝ)) - E.indicator (fun _ => (1 : ℝ))) 1 volume)
        atTop (𝓝 0) ∧
      Tendsto (fun j => perimeter (S j)) atTop (𝓝 (perimeter E)) := by
  obtain ⟨u, t, hmeta, hl1, hper⟩ := exists_bounded_regular_superlevel_approximation hmE hvE hpE
  let A (j : ℕ) : Set AmbientSpace := {x | t j < u j x}
  have hAo (j) : IsOpen (A j) := (hmeta j).2.2.2.2.2.1
  have hAb (j) : Bornology.IsBounded (A j) := (hmeta j).2.2.2.2.2.2
  have hvol : Tendsto (fun j => volume.real (A j)) atTop (𝓝 (volume.real E)) :=
    tendsto_volumeReal_of_indicator_l1
    (fun j => (hAo j).measurableSet.nullMeasurableSet) hmE
    (fun j => (hAb j).measure_lt_top) hvE hl1
  have hpositive : 0 < volume.real E := ENNReal.toReal_pos hposE.ne' hvE.ne
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hvol).1 0 hpositive)
  let F (j : ℕ) : Set AmbientSpace := A (j + N)
  have hFm (j) : NullMeasurableSet (F j) volume := (hAo (j + N)).measurableSet.nullMeasurableSet
  have hFv (j) : volume (F j) < ∞ := (hAb (j + N)).measure_lt_top
  have hFp (j) : 0 < volume (F j) :=
    (ENNReal.toReal_pos_iff.mp (hN (j + N) (Nat.le_add_left N j))).1
  have hFl1 : Tendsto (fun j => eLpNorm
      ((F j).indicator (fun _ => (1 : ℝ)) - E.indicator (fun _ => (1 : ℝ))) 1 volume)
      atTop (𝓝 0) := by
    simpa only [F, A, Function.comp_def] using hl1.comp (tendsto_add_atTop_nat N)
  have hFper : Tendsto (fun j => perimeter (F j)) atTop (𝓝 (perimeter E)) := by
    simpa only [F, A, Function.comp_def] using hper.comp (tendsto_add_atTop_nat N)
  obtain ⟨r, hr, _, hrl1, hrper⟩ :=
    exists_volume_correcting_dilations hFm hmE hFv hvE hFp hposE hFl1 hFper
  refine ⟨fun j => (fun x => r j • x) '' F j, ?_, hrl1, hrper⟩
  intro j
  refine ⟨isOpenMap_smul₀ (hr j).1.ne' _ (hAo (j + N)),
    (lipschitzWith_smul (r j)).isBounded_image (hAb (j + N)), ?_, (hr j).2⟩
  change HasSmoothBoundary ((fun x => r j • x) '' {x | t (j + N) < u (j + N) x})
  rw [image_superlevel_smul (hr j).1.ne']
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x : AmbientSpace =>
      u (j + N) ((r j)⁻¹ • x)) :=
    (hmeta (j + N)).1.comp (contDiff_id.const_smul ((r j)⁻¹))
  apply hasSmoothBoundary_superlevel_of_regular hd
  intro x hx
  rw [gradient_comp_const_smul ((hmeta (j + N)).1.of_le (by simp))]
  exact smul_ne_zero (inv_ne_zero (hr j).1.ne') ((hmeta (j + N)).2.2.2.2.1 _ hx)

/-- Blueprint `cor:smooth-approx-energy`, with the exact same smooth,
volume-preserving approximants and the unchanged Coulomb and energy definitions. -/
theorem smooth_approximation_exact_volume_energy {E : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hvE : volume E < ∞) (hposE : 0 < volume E)
    (hpE : HasFinitePerimeter E) :
    ∃ S : ℕ → Set AmbientSpace,
      (∀ j, IsOpen (S j) ∧ Bornology.IsBounded (S j) ∧ HasSmoothBoundary (S j) ∧
        volume (S j) = volume E) ∧
      Tendsto (fun j => eLpNorm
        ((S j).indicator (fun _ => (1 : ℝ)) - E.indicator (fun _ => (1 : ℝ))) 1 volume)
        atTop (𝓝 0) ∧
      Tendsto (fun j => perimeter (S j)) atTop (𝓝 (perimeter E)) ∧
      Tendsto (fun j => coulombEnergy (S j)) atTop (𝓝 (coulombEnergy E)) ∧
      Tendsto (fun j => energy (S j)) atTop (𝓝 (energy E)) := by
  obtain ⟨S, hS, hl1, hper⟩ := smooth_approximation_exact_volume hmE hvE hposE hpE
  have hp : perimeter E < ∞ := by rwa [← perimeterN_eq_perimeter E hmE]
  obtain ⟨hC, hEnergy⟩ := tendsto_energy_of_exact_volume_strict
    (fun j => (hS j).1.measurableSet.nullMeasurableSet) hmE hvE
    (fun j => (hS j).2.2.2) hp hl1 hper
  have hvS (j) : volume (S j) < ∞ := (hS j).2.2.2 ▸ hvE
  have hpS (j) : perimeter (S j) < ∞ := by
    rw [← perimeterN_eq_perimeter _ (hS j).1.measurableSet.nullMeasurableSet]
    exact (hS j).2.2.1.hasC1Boundary.hasFinitePerimeter (hS j).1 (hS j).2.1
  refine ⟨S, hS, hl1, hper, ?_, ?_⟩
  · simpa only [Function.comp_def,
      ENNReal.ofReal_toReal (coulombEnergy_lt_top _ (hvS _)).ne,
      ENNReal.ofReal_toReal (coulombEnergy_lt_top E hvE).ne] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hC
  · have hEs (j) : energy (S j) < ∞ :=
      ENNReal.add_lt_top.mpr ⟨hpS j, coulombEnergy_lt_top _ (hvS j)⟩
    have hEE : energy E < ∞ := ENNReal.add_lt_top.mpr ⟨hp, coulombEnergy_lt_top E hvE⟩
    simpa only [Function.comp_def, ENNReal.ofReal_toReal (hEs _).ne,
      ENNReal.ofReal_toReal hEE.ne] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hEnergy

end LiquidDrop
