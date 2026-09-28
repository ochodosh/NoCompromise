import NoCompromise.Binding.BallRatio
import NoCompromise.Energy.NullInvariance
import NoCompromise.Nonexistence.Slicing
import NoCompromise.Regularity.PenalizationQuasiminimal
import NoCompromise.Regularity.RepresentativeBounded
import NoCompromise.Regularity.RepresentativeOpen

/-!
# Relaxed energy-to-volume ratios

The infimum ranges over actual Lebesgue-measurable competitors of positive
volume at most A. Extended nonnegative values retain competitors of infinite
energy. Positive A admits a finite-energy ball competitor, so its infimum is finite.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LiquidDrop

/-- The relaxed ratio infimum over positive volumes bounded by A. -/
def relaxedEnergyRatio (A : ℝ) : ℝ≥0∞ :=
  ⨅ (E : Set AmbientSpace) (_ : NullMeasurableSet E volume)
    (_ : 0 < volume E) (_ : volume E ≤ ENNReal.ofReal A), energy E / volume E

/-- An actual competitor attaining the relaxed ratio infimum. -/
def IsRelaxedRatioMinimizer (A : ℝ) (E : Set AmbientSpace) : Prop :=
  NullMeasurableSet E volume ∧ 0 < volume E ∧ volume E ≤ ENNReal.ofReal A ∧
    energy E / volume E = relaxedEnergyRatio A

lemma relaxedEnergyRatio_le {A : ℝ} {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hpos : 0 < volume E)
    (hvol : volume E ≤ ENNReal.ofReal A) :
    relaxedEnergyRatio A ≤ energy E / volume E :=
  iInf_le_of_le E (iInf_le_of_le hE (iInf_le_of_le hpos (iInf_le_of_le hvol le_rfl)))

lemma relaxedEnergyRatio_antitone : Antitone relaxedEnergyRatio := by
  intro A B hAB
  refine le_iInf fun E => le_iInf fun hE => le_iInf fun hpos => le_iInf fun hvol => ?_
  exact relaxedEnergyRatio_le hE hpos (hvol.trans (ENNReal.ofReal_le_ofReal hAB))

lemma relaxedEnergyRatio_le_ball {A : ℝ} (hA : 0 < A) :
    relaxedEnergyRatio A ≤ energy (ballByVolume A) / ENNReal.ofReal A := by
  have h := relaxedEnergyRatio_le
    (show NullMeasurableSet (ballByVolume A) volume from measurableSet_ball.nullMeasurableSet)
    (by rw [volume_ballByVolume hA]; exact ENNReal.ofReal_pos.mpr hA)
    (by rw [volume_ballByVolume hA])
  simpa only [volume_ballByVolume hA] using h

lemma relaxedEnergyRatio_lt_top {A : ℝ} (hA : 0 < A) : relaxedEnergyRatio A < ∞ := by
  apply (relaxedEnergyRatio_le_ball hA).trans_lt
  apply ENNReal.div_lt_top _ (ENNReal.ofReal_pos.mpr hA).ne'
  rw [energy_ballByVolume hA]
  exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ballPerimeter_lt_top hA)).ne

lemma IsRelaxedRatioMinimizer.volume_lt_top {A : ℝ} {E : Set AmbientSpace}
    (h : IsRelaxedRatioMinimizer A E) : volume E < ∞ :=
  h.2.2.1.trans_lt ENNReal.ofReal_lt_top

lemma IsRelaxedRatioMinimizer.cap_pos {A : ℝ} {E : Set AmbientSpace}
    (h : IsRelaxedRatioMinimizer A E) : 0 < A :=
  ENNReal.ofReal_pos.mp (h.2.1.trans_le h.2.2.1)

lemma IsRelaxedRatioMinimizer.energy_lt_top {A : ℝ} {E : Set AmbientSpace}
    (h : IsRelaxedRatioMinimizer A E) : energy E < ∞ := by
  have hratio : energy E / volume E < ∞ := by
    rw [h.2.2.2]
    exact relaxedEnergyRatio_lt_top h.cap_pos
  have heq : energy E = energy E / volume E * volume E :=
    (ENNReal.div_mul_cancel h.2.1.ne' h.volume_lt_top.ne).symm
  rw [heq]
  exact ENNReal.mul_lt_top hratio h.volume_lt_top

/-- A relaxed ratio minimizer minimizes the original energy at its own volume. -/
theorem IsRelaxedRatioMinimizer.isLebesgueFixedVolumeMinimizer
    {A : ℝ} {E : Set AmbientSpace} (h : IsRelaxedRatioMinimizer A E) :
    IsLebesgueFixedVolumeMinimizer (volume E).toReal E := by
  have hvol : volume E = ENNReal.ofReal (volume E).toReal :=
    (ENNReal.ofReal_toReal h.volume_lt_top.ne).symm
  refine ⟨h.1, hvol, (le_add_right le_rfl).trans_lt h.energy_lt_top, ?_⟩
  intro F hF hvF
  have heq : volume F = volume E := hvF.trans hvol.symm
  have hcomp := relaxedEnergyRatio_le hF (heq ▸ h.2.1) (heq ▸ h.2.2.1)
  rw [heq, ← h.2.2.2] at hcomp
  have hmul := mul_le_mul hcomp (le_refl (volume E)) zero_le zero_le
  simpa only [ENNReal.div_mul_cancel h.2.1.ne' h.volume_lt_top.ne] using hmul

/-- The Borel formulation used by the original main theorem follows as well. -/
theorem IsRelaxedRatioMinimizer.isFixedVolumeMinimizer
    {A : ℝ} {E : Set AmbientSpace} (h : IsRelaxedRatioMinimizer A E)
    (hE : MeasurableSet E) : IsFixedVolumeMinimizer (volume E).toReal E := by
  have hm := h.isLebesgueFixedVolumeMinimizer
  exact ⟨hE, hm.2.1, hm.2.2.1, fun F hF => hm.2.2.2 F hF.nullMeasurableSet⟩

/-! ## Blueprint `prop:V-le-8` for fixed-volume minimisers -/

/-- Blueprint `prop:V-le-8` in minimiser form: every (Lebesgue) fixed-volume minimiser at a
volume `V > 0` has `V ≤ 8`. The density-one representative is open (`lem:open-representative`),
bounded (`lem:bounded-representative`) and still a minimiser, so the slicing inequality
`lem:slicing-inequality` (proved for bounded Borel minimisers) applies to it. -/
theorem IsLebesgueFixedVolumeMinimizer.le_eight {V : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (hΩ : IsLebesgueFixedVolumeMinimizer V Ω) : V ≤ 8 := by
  have hω := hΩ.isOmegaMinimal hV
  have hfin : volume Ω < ∞ := by rw [hΩ.2.1]; exact ENNReal.ofReal_lt_top
  have hae : densityOne Ω =ᵐ[volume] Ω := densityOne_ae_eq (by norm_num) hΩ.1
  have hopen : IsOpen (densityOne Ω) := hω.isOpen_densityOne
  have hbdd := (quasiminimal_bounded_representative hω hfin).1
  have hmin' : IsLebesgueFixedVolumeMinimizer V (densityOne Ω) :=
    (isLebesgueFixedVolumeMinimizer_congr_ae V hae).mpr hΩ
  have hB : IsFixedVolumeMinimizer V (densityOne Ω) :=
    (isFixedVolumeMinimizer_iff_lebesgue V _ hopen.measurableSet).mpr hmin'
  have h8 := volume_le_eight_of_slicing_inequality (densityOne Ω) hopen.measurableSet
    (by rw [hmin'.2.1]; exact ENNReal.ofReal_ne_top)
    (fun ν hν => (slicing_inequality hB hbdd (by simpa using hν)).mono fun _ h => h.2)
  rwa [hmin'.2.1, ENNReal.toReal_ofReal hV.le] at h8

/-- The Borel form of `IsLebesgueFixedVolumeMinimizer.le_eight`. -/
theorem IsFixedVolumeMinimizer.le_eight {V : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (hΩ : IsFixedVolumeMinimizer V Ω) : V ≤ 8 :=
  hΩ.toLebesgue.le_eight hV

/-! ## Blueprint `lem:stabilization` -/

/-- The global energy-to-volume ratio infimum `inf {𝓔(E)/|E| : 0 < |E| < ∞}` of
`eq:global-inf` and `thm:main-binding`, over Lebesgue-measurable sets. -/
def globalEnergyRatio : ℝ≥0∞ :=
  ⨅ (E : Set AmbientSpace) (_ : NullMeasurableSet E volume)
    (_ : 0 < volume E) (_ : volume E < ∞), energy E / volume E

/-- An actual competitor attaining the global ratio infimum. -/
def IsGlobalRatioOptimizer (E : Set AmbientSpace) : Prop :=
  NullMeasurableSet E volume ∧ 0 < volume E ∧ volume E < ∞ ∧
    energy E / volume E = globalEnergyRatio

lemma globalEnergyRatio_le {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    (hpos : 0 < volume E) (hfin : volume E < ∞) :
    globalEnergyRatio ≤ energy E / volume E :=
  iInf_le_of_le E (iInf_le_of_le hE (iInf_le_of_le hpos (iInf_le_of_le hfin le_rfl)))

lemma globalEnergyRatio_le_relaxedEnergyRatio (A : ℝ) :
    globalEnergyRatio ≤ relaxedEnergyRatio A :=
  le_iInf fun _ => le_iInf fun hE => le_iInf fun hpos => le_iInf fun hvol =>
    globalEnergyRatio_le hE hpos (hvol.trans_lt ENNReal.ofReal_lt_top)

/-- Blueprint `lem:stabilization`, `eq:stabilization`, from `lem:relaxed-attained` (the
hypothesis `hatt`) and `prop:V-le-8`: `e_≤(A) = e_≤(8)` for every `A ≥ 8`. -/
theorem relaxedEnergyRatio_eq_eight_of_attained
    (hatt : ∀ A : ℝ, 0 < A → ∃ E : Set AmbientSpace, IsRelaxedRatioMinimizer A E)
    {A : ℝ} (hA : 8 ≤ A) : relaxedEnergyRatio A = relaxedEnergyRatio 8 := by
  refine le_antisymm (relaxedEnergyRatio_antitone hA) ?_
  obtain ⟨E, hE⟩ := hatt A (by linarith)
  have hM : 0 < (volume E).toReal := ENNReal.toReal_pos hE.2.1.ne' hE.volume_lt_top.ne
  have h8 := hE.isLebesgueFixedVolumeMinimizer.le_eight hM
  have hvol : volume E ≤ ENNReal.ofReal 8 := by
    rw [← ENNReal.ofReal_toReal hE.volume_lt_top.ne]
    exact ENNReal.ofReal_le_ofReal h8
  rw [← hE.2.2.2]
  exact relaxedEnergyRatio_le hE.1 hE.2.1 hvol

/-- Blueprint `lem:stabilization`, `eq:global-inf`: the global ratio infimum is `e_≤(8)`. -/
theorem globalEnergyRatio_eq_eight_of_attained
    (hatt : ∀ A : ℝ, 0 < A → ∃ E : Set AmbientSpace, IsRelaxedRatioMinimizer A E) :
    globalEnergyRatio = relaxedEnergyRatio 8 := by
  refine le_antisymm (globalEnergyRatio_le_relaxedEnergyRatio 8) ?_
  refine le_iInf fun E => le_iInf fun hE => le_iInf fun hpos => le_iInf fun hfin => ?_
  have hA : 8 ≤ max 8 (volume E).toReal := le_max_left _ _
  rw [← relaxedEnergyRatio_eq_eight_of_attained hatt hA]
  refine relaxedEnergyRatio_le hE hpos ?_
  exact (ENNReal.le_ofReal_iff_toReal_le hfin.ne (by linarith)).mpr (le_max_right _ _)

/-- Blueprint `lem:stabilization`, last assertion: the global infimum is attained. -/
theorem exists_isGlobalRatioOptimizer_of_attained
    (hatt : ∀ A : ℝ, 0 < A → ∃ E : Set AmbientSpace, IsRelaxedRatioMinimizer A E) :
    ∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E := by
  obtain ⟨E, hE⟩ := hatt 8 (by norm_num)
  exact ⟨E, hE.1, hE.2.1, hE.volume_lt_top,
    by rw [hE.2.2.2, globalEnergyRatio_eq_eight_of_attained hatt]⟩

/-- Blueprint `lem:stabilization`, all assertions at once, from `lem:relaxed-attained`. -/
theorem stabilization_of_attained
    (hatt : ∀ A : ℝ, 0 < A → ∃ E : Set AmbientSpace, IsRelaxedRatioMinimizer A E) :
    Antitone relaxedEnergyRatio ∧
      (∀ A : ℝ, 8 ≤ A → relaxedEnergyRatio A = relaxedEnergyRatio 8) ∧
      globalEnergyRatio = relaxedEnergyRatio 8 ∧
      ∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E :=
  ⟨relaxedEnergyRatio_antitone, fun _ hA => relaxedEnergyRatio_eq_eight_of_attained hatt hA,
    globalEnergyRatio_eq_eight_of_attained hatt, exists_isGlobalRatioOptimizer_of_attained hatt⟩

/-- A global ratio optimiser is a relaxed ratio minimiser for the cap equal to its volume,
hence (`lem:ratio-is-fixed`) a fixed-volume minimiser at its own volume. -/
theorem IsGlobalRatioOptimizer.isRelaxedRatioMinimizer {E : Set AmbientSpace}
    (h : IsGlobalRatioOptimizer E) : IsRelaxedRatioMinimizer (volume E).toReal E := by
  have hvol : volume E ≤ ENNReal.ofReal (volume E).toReal := by
    rw [ENNReal.ofReal_toReal h.2.2.1.ne]
  refine ⟨h.1, h.2.1, hvol, le_antisymm ?_ (relaxedEnergyRatio_le h.1 h.2.1 hvol)⟩
  rw [h.2.2.2]
  exact globalEnergyRatio_le_relaxedEnergyRatio _

theorem IsGlobalRatioOptimizer.isLebesgueFixedVolumeMinimizer {E : Set AmbientSpace}
    (h : IsGlobalRatioOptimizer E) : IsLebesgueFixedVolumeMinimizer (volume E).toReal E :=
  h.isRelaxedRatioMinimizer.isLebesgueFixedVolumeMinimizer

end LiquidDrop
