module

public import NoCompromise.BV.Basic
public import NoCompromise.Energy.Defs
public import NoCompromise.Energy.Coulomb

@[expose] public section

/-! # Null-set invariance of the showcase energy

Blueprint `lem:null-invariance`, proved directly for the extended-real functionals.
The later results justify the change from Borel to Lebesgue-measurable competitors
and representatives in `def:minimizer`. None uses the unfinished main theorem.
-/

open MeasureTheory
open scoped ENNReal symmDiff

namespace LiquidDrop

theorem energy_congr_ae {E F : Set AmbientSpace} (hEF : E =ᵐ[volume] F) :
    energy E = energy F := by
  rw [energy, energy, perimeter_congr_ae hEF, coulombEnergy_congr_ae hEF]

/-- Blueprint `lem:null-invariance`. -/
theorem null_invariance {E F : Set AmbientSpace} (hEF : volume (E ∆ F) = 0) :
    volume E = volume F ∧ perimeter E = perimeter F ∧
      coulombEnergy E = coulombEnergy F ∧ energy E = energy F := by
  have h := measure_symmDiff_eq_zero_iff.mp hEF
  exact ⟨measure_congr h, perimeter_congr_ae h, coulombEnergy_congr_ae h, energy_congr_ae h⟩

/-- A Lebesgue-measurable set has a Borel representative with the same volume and energies. -/
theorem exists_borel_representative (E : Set AmbientSpace) (hE : NullMeasurableSet E volume) :
    ∃ F : Set AmbientSpace, MeasurableSet F ∧ E =ᵐ[volume] F ∧
      volume E = volume F ∧ perimeter E = perimeter F ∧
      coulombEnergy E = coulombEnergy F ∧ energy E = energy F := by
  have hEF := hE.toMeasurable_ae_eq.symm
  exact ⟨toMeasurable volume E, measurableSet_toMeasurable _ _, hEF,
    measure_congr hEF, perimeter_congr_ae hEF, coulombEnergy_congr_ae hEF,
    energy_congr_ae hEF⟩

/-- A showcase minimizer also beats every Lebesgue-measurable competitor. -/
theorem IsFixedVolumeMinimizer.energy_le_of_nullMeasurableSet
    {V : ℝ} {Ω F : Set AmbientSpace} (hΩ : IsFixedVolumeMinimizer V Ω)
    (hF : NullMeasurableSet F volume) (hvol : volume F = ENNReal.ofReal V) :
    energy Ω ≤ energy F := by
  have hrep := hF.toMeasurable_ae_eq
  have h := hΩ.2.2.2 (toMeasurable volume F) (measurableSet_toMeasurable _ _)
    ((measure_congr hrep).trans hvol)
  rwa [energy_congr_ae hrep] at h

theorem IsFixedVolumeMinimizer.toLebesgue {V : ℝ} {Ω : Set AmbientSpace}
    (hΩ : IsFixedVolumeMinimizer V Ω) : IsLebesgueFixedVolumeMinimizer V Ω := by
  exact ⟨hΩ.1.nullMeasurableSet, hΩ.2.1, hΩ.2.2.1,
    fun _ hF hvol => hΩ.energy_le_of_nullMeasurableSet hF hvol⟩

/-- On Borel sets the original and completed-measure minimizer predicates are equivalent. -/
theorem isFixedVolumeMinimizer_iff_lebesgue (V : ℝ) (Ω : Set AmbientSpace)
    (hΩ : MeasurableSet Ω) :
    IsFixedVolumeMinimizer V Ω ↔ IsLebesgueFixedVolumeMinimizer V Ω := by
  constructor
  · exact IsFixedVolumeMinimizer.toLebesgue
  · intro h
    exact ⟨hΩ, h.2.1, h.2.2.1, fun _ hF hvol => h.2.2.2 _ hF.nullMeasurableSet hvol⟩

/-- The Lebesgue formulation is invariant under null modifications of the minimizer. -/
theorem isLebesgueFixedVolumeMinimizer_congr_ae (V : ℝ) {E F : Set AmbientSpace}
    (hEF : E =ᵐ[volume] F) :
    IsLebesgueFixedVolumeMinimizer V E ↔ IsLebesgueFixedVolumeMinimizer V F := by
  have hm : NullMeasurableSet E volume ↔ NullMeasurableSet F volume :=
    ⟨fun h => h.congr hEF, fun h => h.congr hEF.symm⟩
  simp only [IsLebesgueFixedVolumeMinimizer, hm, measure_congr hEF,
    perimeter_congr_ae hEF, energy_congr_ae hEF]

/-- Taking a Borel representative turns a Lebesgue minimizer into a showcase minimizer. -/
theorem IsLebesgueFixedVolumeMinimizer.toBorel {V : ℝ} {Ω : Set AmbientSpace}
    (hΩ : IsLebesgueFixedVolumeMinimizer V Ω) :
    IsFixedVolumeMinimizer V (toMeasurable volume Ω) := by
  apply (isFixedVolumeMinimizer_iff_lebesgue V _ (measurableSet_toMeasurable _ _)).mpr
  exact (isLebesgueFixedVolumeMinimizer_congr_ae V hΩ.1.toMeasurable_ae_eq).mpr hΩ

/-- Existence, and hence nonexistence, is equivalent in the two formulations. -/
theorem exists_fixedVolumeMinimizer_iff_lebesgue (V : ℝ) :
    (∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω) ↔
      ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω := by
  constructor
  · rintro ⟨Ω, hΩ⟩
    exact ⟨Ω, hΩ.toLebesgue⟩
  · rintro ⟨Ω, hΩ⟩
    exact ⟨toMeasurable volume Ω, hΩ.toBorel⟩

end LiquidDrop
