import NoCompromise.Regularity.PenalizationDilation
import NoCompromise.Energy.NullInvariance

/-!
# Global volume penalization for liquid-drop minimizers

Volume correction is by an actual positive homothety. No smooth patch or
regularity of the minimizer is assumed. The explicit penalty depends only on
the prescribed volume and the original energy.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsLebesgueFixedVolumeMinimizer.energy_lt_top {V : ℝ} {E : Set AmbientSpace}
    (hE : IsLebesgueFixedVolumeMinimizer V E) : energy E < ∞ := by
  exact ENNReal.add_lt_top.mpr ⟨hE.2.2.1,
    coulombEnergy_lt_top E (hE.2.1 ▸ ENNReal.ofReal_lt_top)⟩

lemma IsFixedVolumeMinimizer.energy_lt_top {V : ℝ} {E : Set AmbientSpace}
    (hE : IsFixedVolumeMinimizer V E) : energy E < ∞ :=
  hE.toLebesgue.energy_lt_top

/-- A single genuine positive homothety correcting an arbitrary positive finite volume. -/
lemma exists_positive_volume_correcting_dilation {F : Set AmbientSpace} {V : ℝ}
    (hvF : volume F < ∞) (hpF : 0 < volume.real F) (hV : 0 < V) :
    ∃ r : ℝ, 0 < r ∧ r ^ 3 = V / volume.real F ∧
      volume ((fun x => r • x) '' F) = ENNReal.ofReal V := by
  let r : ℝ := (V / volume.real F) ^ ((1 : ℝ) / 3)
  have hr : 0 < r := Real.rpow_pos_of_pos (div_pos hV hpF) _
  have hr3 : r ^ 3 = V / volume.real F := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hV.le hpF.le)]
    norm_num
  refine ⟨r, hr, hr3, ?_⟩
  rw [volume_image_smul _ hr, hr3, ← ENNReal.ofReal_toReal hvF.ne,
    ← ENNReal.ofReal_mul (div_nonneg hV.le hpF.le)]
  rw [show (volume F).toReal = volume.real F from rfl, div_mul_cancel₀ _ hpF.ne']

lemma energy_smul_toReal {F : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hvF : volume F < ∞) (hpF : perimeter F < ∞) {r : ℝ} (hr : 0 < r) :
    (energy ((fun x => r • x) '' F)).toReal =
      r ^ 2 * (perimeter F).toReal + r ^ 5 * (coulombEnergy F).toReal := by
  rw [energy_smul hmF hr, ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpF.ne)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (coulombEnergy_lt_top F hvF).ne)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ 2),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ 5)]

/-- The explicit real-valued global penalty estimate, before conversion to ENNReal. -/
theorem IsLebesgueFixedVolumeMinimizer.energy_toReal_le_volume_penalty
    {V : ℝ} {E : Set AmbientSpace} (hE : IsLebesgueFixedVolumeMinimizer V E) (hV : 0 < V)
    {F : Set AmbientSpace} (hmF : NullMeasurableSet F volume) (hvF : volume F < ∞)
    (hpF : HasFinitePerimeter F) :
    (energy E).toReal ≤ (energy F).toReal +
      (62 * (energy E).toReal / V) * |volume.real F - V| := by
  have hp : perimeter F < ∞ := by rwa [← perimeterN_eq_perimeter F hmF]
  have hcf : coulombEnergy F < ∞ := coulombEnergy_lt_top F hvF
  have hef : energy F < ∞ := ENNReal.add_lt_top.mpr ⟨hp, hcf⟩
  have he0 : 0 ≤ (energy E).toReal := ENNReal.toReal_nonneg
  have hf0 : 0 ≤ (energy F).toReal := ENNReal.toReal_nonneg
  have hΛ : 0 ≤ 62 * (energy E).toReal / V := by positivity
  by_cases hcheap : (energy E).toReal ≤ (energy F).toReal
  · exact hcheap.trans (le_add_of_nonneg_right (mul_nonneg hΛ (abs_nonneg _)))
  have hcheap' : (energy F).toReal ≤ (energy E).toReal := le_of_lt (lt_of_not_ge hcheap)
  by_cases hfar : V / 2 ≤ |volume.real F - V|
  · have hlarge := mul_le_mul_of_nonneg_left hfar hΛ
    have hid : (62 * (energy E).toReal / V) * (V / 2) = 31 * (energy E).toReal := by
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
  have hpG : perimeter G < ∞ := by
    change perimeter ((fun x => r • x) '' F) < ∞
    rw [perimeter_image_smul hmF hr]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hp
  have hvG : volume G < ∞ := hvol ▸ ENNReal.ofReal_lt_top
  have heG : energy G < ∞ := ENNReal.add_lt_top.mpr ⟨hpG, coulombEnergy_lt_top G hvG⟩
  have hmin : (energy E).toReal ≤ (energy G).toReal :=
    ENNReal.toReal_mono heG.ne (hE.2.2.2 G hmG hvol)
  have hsum : (perimeter F).toReal + (coulombEnergy F).toReal = (energy F).toReal :=
    (ENNReal.toReal_add hp.ne hcf.ne).symm
  have hscaled : (energy G).toReal ≤ (energy F).toReal +
      31 * (energy F).toReal * |r ^ 3 - 1| := by
    change (energy ((fun x => r • x) '' F)).toReal ≤ _
    rw [energy_smul_toReal hmF hvF hp hr]
    simpa only [hsum] using dilation_energy_le hr.le hr2
      (ENNReal.toReal_nonneg (a := perimeter F)) (ENNReal.toReal_nonneg (a := coulombEnergy F))
  have herr : |r ^ 3 - 1| = |volume.real F - V| / volume.real F := by
    rw [hr3, div_sub_one hWpos.ne', abs_div, abs_of_pos hWpos, abs_sub_comm]
  have hdenom : 1 / volume.real F ≤ 2 / V := by
    apply (div_le_div_iff₀ hWpos hV).mpr
    linarith
  have hecoef : 31 * (energy F).toReal / volume.real F ≤ 62 * (energy E).toReal / V := by
    calc
      _ ≤ 31 * (energy E).toReal / volume.real F :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcheap' (by norm_num)) hWpos.le
      _ = (31 * (energy E).toReal) * (1 / volume.real F) := by ring
      _ ≤ (31 * (energy E).toReal) * (2 / V) :=
        mul_le_mul_of_nonneg_left hdenom (by positivity)
      _ = _ := by ring
  rw [herr] at hscaled
  have herror := mul_le_mul_of_nonneg_right hecoef (abs_nonneg (volume.real F - V))
  have harr : 31 * (energy F).toReal * (|volume.real F - V| / volume.real F) =
      (31 * (energy F).toReal / volume.real F) * |volume.real F - V| := by ring
  rw [harr] at hscaled
  linarith only [hmin, hscaled, herror]

/-- Blueprint `lem:penalization`, with an explicit finite constant depending only on
volume and energy. The competitors are all Lebesgue-measurable finite-volume
finite-perimeter sets. -/
theorem IsLebesgueFixedVolumeMinimizer.global_volume_penalization
    {V : ℝ} {E : Set AmbientSpace} (hE : IsLebesgueFixedVolumeMinimizer V E) (hV : 0 < V) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ Λ = 62 * (energy E).toReal / V ∧
      ∀ F : Set AmbientSpace, NullMeasurableSet F volume → volume F < ∞ →
        HasFinitePerimeter F →
        energy E ≤ energy F + ENNReal.ofReal (Λ * |volume.real F - V|) := by
  refine ⟨62 * (energy E).toReal / V, by positivity, rfl, ?_⟩
  intro F hmF hvF hpF
  have hp : perimeter F < ∞ := by rwa [← perimeterN_eq_perimeter F hmF]
  have hef : energy F < ∞ := ENNReal.add_lt_top.mpr ⟨hp, coulombEnergy_lt_top F hvF⟩
  have h := ENNReal.ofReal_le_ofReal (hE.energy_toReal_le_volume_penalty hV hmF hvF hpF)
  rwa [ENNReal.ofReal_toReal hE.energy_lt_top.ne, ENNReal.ofReal_add ENNReal.toReal_nonneg
    (by positivity), ENNReal.ofReal_toReal hef.ne] at h

/-- The same complete penalization theorem for the original Borel showcase minimizers. -/
theorem IsFixedVolumeMinimizer.global_volume_penalization
    {V : ℝ} {E : Set AmbientSpace} (hE : IsFixedVolumeMinimizer V E) (hV : 0 < V) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ Λ = 62 * (energy E).toReal / V ∧
      ∀ F : Set AmbientSpace, NullMeasurableSet F volume → volume F < ∞ →
        HasFinitePerimeter F →
        energy E ≤ energy F + ENNReal.ofReal (Λ * |volume.real F - V|) :=
  hE.toLebesgue.global_volume_penalization hV

end LiquidDrop
