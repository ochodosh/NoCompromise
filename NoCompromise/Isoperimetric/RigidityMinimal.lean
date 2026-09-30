module

public import NoCompromise.Regularity.PenalizationQuasiminimal

@[expose] public section

/-!
# Coulomb-free penalization and quasiminimality for perimeter minimisers

Blueprint `thm:isoperimetric-rigidity`, Step 1. A perimeter minimiser among
Lebesgue-measurable sets of prescribed volume satisfies a global volume
penalization (the proof of `lem:penalization` with the Coulomb term deleted),
and hence is unit-scale `ω`-minimal (the proof of `lem:quasiminimal` with the
Coulomb Lipschitz term deleted). Volume is corrected by a genuine positive
homothety; no regularity of the minimiser is assumed.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- `E` minimises perimeter among Lebesgue-measurable sets of volume `V`. -/
def IsLebesgueFixedVolumePerimeterMinimizer (V : ℝ) (E : Set AmbientSpace) : Prop :=
  NullMeasurableSet E volume ∧ volume E = ENNReal.ofReal V ∧ perimeter E < ∞ ∧
    ∀ F : Set AmbientSpace,
      NullMeasurableSet F volume → volume F = ENNReal.ofReal V → perimeter E ≤ perimeter F

/-- The explicit real-valued global penalty estimate for a perimeter minimiser. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.perimeter_toReal_le_volume_penalty
    {V : ℝ} {E : Set AmbientSpace} (hE : IsLebesgueFixedVolumePerimeterMinimizer V E)
    (hV : 0 < V) {F : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hvF : volume F < ∞) (hpF : HasFinitePerimeter F) :
    (perimeter E).toReal ≤ (perimeter F).toReal +
      (62 * (perimeter E).toReal / V) * |volume.real F - V| := by
  have hp : perimeter F < ∞ := by rwa [← perimeterN_eq_perimeter F hmF]
  have he0 : 0 ≤ (perimeter E).toReal := ENNReal.toReal_nonneg
  have hf0 : 0 ≤ (perimeter F).toReal := ENNReal.toReal_nonneg
  have hΛ : 0 ≤ 62 * (perimeter E).toReal / V := by positivity
  by_cases hcheap : (perimeter E).toReal ≤ (perimeter F).toReal
  · exact hcheap.trans (le_add_of_nonneg_right (mul_nonneg hΛ (abs_nonneg _)))
  have hcheap' : (perimeter F).toReal ≤ (perimeter E).toReal := le_of_lt (lt_of_not_ge hcheap)
  by_cases hfar : V / 2 ≤ |volume.real F - V|
  · have hlarge := mul_le_mul_of_nonneg_left hfar hΛ
    have hid : (62 * (perimeter E).toReal / V) * (V / 2) = 31 * (perimeter E).toReal := by
      field_simp
      ring
    rw [hid] at hlarge
    nlinarith only [hlarge, hf0, he0]
  have hnear : |volume.real F - V| < V / 2 := lt_of_not_ge hfar
  have hW : V / 2 < volume.real F := by linarith [(abs_lt.mp hnear).1]
  have hWpos : 0 < volume.real F := by linarith
  obtain ⟨r, hr, hr3, hvol⟩ := exists_positive_volume_correcting_dilation hvF hWpos hV
  have hquot : V / volume.real F ≤ 2 := (div_le_iff₀ hWpos).mpr (by linarith)
  have hr2 : r ≤ 2 := by nlinarith [sq_nonneg (r - 2)]
  let G : Set AmbientSpace := (fun x => r • x) '' F
  have hmG : NullMeasurableSet G volume :=
    nullMeasurableSet_image_of_differentiable (by fun_prop)
      (smul_right_injective AmbientSpace hr.ne') hmF
  have hGeq : (perimeter G).toReal = r ^ 2 * (perimeter F).toReal := by
    change (perimeter ((fun x => r • x) '' F)).toReal = _
    rw [perimeter_image_smul hmF hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ 2)]
  have hpG : perimeter G < ∞ := by
    change perimeter ((fun x => r • x) '' F) < ∞
    rw [perimeter_image_smul hmF hr]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hp
  have hmin : (perimeter E).toReal ≤ (perimeter G).toReal :=
    ENNReal.toReal_mono hpG.ne (hE.2.2.2 G hmG hvol)
  have hscaled : (perimeter G).toReal ≤ (perimeter F).toReal +
      31 * (perimeter F).toReal * |r ^ 3 - 1| := by
    rw [hGeq]
    have h := dilation_energy_le hr.le hr2 hf0 (le_refl (0 : ℝ))
    simpa only [mul_zero, add_zero] using h
  have herr : |r ^ 3 - 1| = |volume.real F - V| / volume.real F := by
    rw [hr3, div_sub_one hWpos.ne', abs_div, abs_of_pos hWpos, abs_sub_comm]
  have hdenom : 1 / volume.real F ≤ 2 / V := by
    apply (div_le_div_iff₀ hWpos hV).mpr
    linarith
  have hecoef :
      31 * (perimeter F).toReal / volume.real F ≤ 62 * (perimeter E).toReal / V := by
    calc
      _ ≤ 31 * (perimeter E).toReal / volume.real F :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcheap' (by norm_num)) hWpos.le
      _ = (31 * (perimeter E).toReal) * (1 / volume.real F) := by ring
      _ ≤ (31 * (perimeter E).toReal) * (2 / V) :=
        mul_le_mul_of_nonneg_left hdenom (by positivity)
      _ = _ := by ring
  rw [herr] at hscaled
  have herror := mul_le_mul_of_nonneg_right hecoef (abs_nonneg (volume.real F - V))
  have harr : 31 * (perimeter F).toReal * (|volume.real F - V| / volume.real F) =
      (31 * (perimeter F).toReal / volume.real F) * |volume.real F - V| := by ring
  rw [harr] at hscaled
  linarith only [hmin, hscaled, herror]

/-- Blueprint `thm:isoperimetric-rigidity`, Step 1, with the explicit constant
`Λ = 62 Per(E) / V`. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.global_volume_penalization_explicit
    {V : ℝ} {E : Set AmbientSpace} (hE : IsLebesgueFixedVolumePerimeterMinimizer V E)
    (hV : 0 < V) :
    ∀ F : Set AmbientSpace, NullMeasurableSet F volume → volume F < ∞ →
      HasFinitePerimeter F →
      perimeter E ≤ perimeter F +
        ENNReal.ofReal ((62 * (perimeter E).toReal / V) * |volume.real F - V|) := by
  intro F hmF hvF hpF
  have hp : perimeter F < ∞ := by rwa [← perimeterN_eq_perimeter F hmF]
  have h := ENNReal.ofReal_le_ofReal (hE.perimeter_toReal_le_volume_penalty hV hmF hvF hpF)
  rwa [ENNReal.ofReal_toReal hE.2.2.1.ne, ENNReal.ofReal_add ENNReal.toReal_nonneg
    (by positivity), ENNReal.ofReal_toReal hp.ne] at h

/-- Blueprint `thm:isoperimetric-rigidity`, Step 1: `lem:penalization` with the Coulomb term
deleted. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.global_volume_penalization
    {V : ℝ} {E : Set AmbientSpace} (hE : IsLebesgueFixedVolumePerimeterMinimizer V E)
    (hV : 0 < V) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ F : Set AmbientSpace, NullMeasurableSet F volume → volume F < ∞ →
        HasFinitePerimeter F →
        perimeter E ≤ perimeter F + ENNReal.ofReal (Λ * |volume.real F - V|) :=
  ⟨62 * (perimeter E).toReal / V, by positivity, hE.global_volume_penalization_explicit hV⟩

/-- A global volume penalty for perimeter alone gives unit-scale quasiminimality with
constant `Λ`. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.isOmegaMinimal_of_volume_penalty
    {V Λ : ℝ} {E : Set AmbientSpace} (hE : IsLebesgueFixedVolumePerimeterMinimizer V E)
    (hV : 0 < V) (hΛ : 0 ≤ Λ)
    (hpen : ∀ F : Set AmbientSpace, NullMeasurableSet F volume → volume F < ∞ →
      HasFinitePerimeter F →
      perimeter E ≤ perimeter F + ENNReal.ofReal (Λ * |volume.real F - V|)) :
    IsOmegaMinimal E Λ := by
  have hvE : volume E < ∞ := hE.2.1 ▸ ENNReal.ofReal_lt_top
  have hpE : HasFinitePerimeter E := by
    rw [HasFinitePerimeter, perimeterN_eq_perimeter E hE.1]
    exact hE.2.2.1
  have hlE := hpE.hasLocallyFinitePerimeter
  refine ⟨hΛ, by norm_num, hE.1, hlE, ?_⟩
  intro x r hr _hrr F hmF hlF _hc hs
  have hsd : F ∆ E ⊆ ball x r := subset_closure.trans hs
  have hesd : E ∆ F ⊆ ball x r := by rwa [symmDiff_comm]
  have hFB : F ⊆ E ∪ ball x r := by
    intro y hy
    by_cases he : y ∈ E
    · exact Or.inl he
    · exact Or.inr (hsd (Or.inl ⟨hy, he⟩))
  have hvF : volume F < ∞ :=
    (measure_mono hFB).trans_lt ((measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hvE, isBounded_ball.measure_lt_top⟩))
  have hvΔ : volume (E ∆ F) < ∞ := (measure_mono hesd).trans_lt isBounded_ball.measure_lt_top
  obtain ⟨hpF, hlocal⟩ := perimeter_localization_of_compact_symmDiff hE.1 hmF hpE hlF x r hs
  have hpFr : perimeter F < ∞ := by rwa [← perimeterN_eq_perimeter F hmF]
  have hP := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hpFr.ne, ENNReal.ofReal_ne_top⟩) (hpen F hmF hvF hpF)
  rw [ENNReal.toReal_add hpFr.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (mul_nonneg hΛ (abs_nonneg _))] at hP
  have hvolE : volume.real E = V := by
    rw [measureReal_def, hE.2.1, ENNReal.toReal_ofReal hV.le]
  have hvol : |volume.real F - V| ≤ volume.real (E ∆ F) := by
    rw [← hvolE, abs_sub_comm]
    exact abs_volumeReal_sub_le_symmDiff hE.1 hmF hvE hvF
  have hV' := mul_le_mul_of_nonneg_left hvol hΛ
  have hpLocal : (perimeterIn E (ball x r)).toReal ≤
      (perimeterIn F (ball x r)).toReal + Λ * volume.real (E ∆ F) := by
    linarith only [hP, hV', hlocal]
  have hpEB := hlE (ball x r) isOpen_ball isBounded_ball.isCompact_closure
  have hpFB := hlF (ball x r) isOpen_ball isBounded_ball.isCompact_closure
  have h := ENNReal.ofReal_le_ofReal hpLocal
  simp only [measureReal_def] at h
  rwa [ENNReal.ofReal_toReal hpEB.ne, ENNReal.ofReal_add ENNReal.toReal_nonneg
    (mul_nonneg hΛ ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hpFB.ne,
    ENNReal.ofReal_mul hΛ, ENNReal.ofReal_toReal hvΔ.ne] at h

/-- Explicit constant: a perimeter minimiser of volume `V` is unit-scale
`62 Per(E) / V`-minimal. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.isOmegaMinimal_explicit
    {V : ℝ} {E : Set AmbientSpace} (hE : IsLebesgueFixedVolumePerimeterMinimizer V E)
    (hV : 0 < V) :
    IsOmegaMinimal E (62 * (perimeter E).toReal / V) :=
  hE.isOmegaMinimal_of_volume_penalty hV (by positivity)
    (hE.global_volume_penalization_explicit hV)

/-- Blueprint `thm:isoperimetric-rigidity`, Step 1: `lem:quasiminimal` with the Coulomb term
deleted. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.isOmegaMinimal
    {V : ℝ} {E : Set AmbientSpace} (hE : IsLebesgueFixedVolumePerimeterMinimizer V E)
    (hV : 0 < V) :
    ∃ ω : ℝ, IsOmegaMinimal E ω :=
  ⟨_, hE.isOmegaMinimal_explicit hV⟩

end LiquidDrop
