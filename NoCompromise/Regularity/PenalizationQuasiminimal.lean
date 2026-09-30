module

public import NoCompromise.Regularity.Penalization
public import NoCompromise.Regularity.OmegaMinimal
public import NoCompromise.DeGiorgi.PolarDifferentiation

@[expose] public section

/-!
# Local perimeter quasiminimality from global volume penalization

The compactly supported competitors are initially only locally finite perimeter.
Their finite total perimeter and the cancellation of exterior perimeter follow
from locality of the genuine perimeter measures.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma HasFinitePerimeter.hasLocallyFinitePerimeter {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : HasFinitePerimeter E) :
    HasLocallyFinitePerimeter E := by
  intro A _ _
  exact (variation_mono MeasurableSet.univ (subset_univ A)).trans_lt hE

/-- Perimeter outside the comparison ball cancels exactly; finite global perimeter
of the local competitor is a conclusion. -/
lemma perimeter_localization_of_compact_symmDiff
    {E F : Set AmbientSpace} (hmE : NullMeasurableSet E volume)
    (hmF : NullMeasurableSet F volume) (hpE : HasFinitePerimeter E)
    (hpF : HasLocallyFinitePerimeter F) (x : AmbientSpace) (r : ℝ)
    (hs : closure (F ∆ E) ⊆ ball x r) :
    HasFinitePerimeter F ∧
      (perimeter E).toReal - (perimeter F).toReal =
        (perimeterIn E (ball x r)).toReal - (perimeterIn F (ball x r)).toReal := by
  obtain ⟨μ, σ, hμ⟩ := exists_ambient_outward_perimeter_polar hpE.hasLocallyFinitePerimeter hmE
  obtain ⟨ν, τ, hν⟩ := exists_ambient_outward_perimeter_polar hpF hmF
  let : μ.Regular := hμ.regular
  let : ν.Regular := hν.regular
  let : IsFiniteMeasureOnCompacts μ := hμ.finiteOnCompacts
  let : IsFiniteMeasureOnCompacts ν := hν.finiteOnCompacts
  let W : Set AmbientSpace := (closure (F ∆ E))ᶜ
  have hW : IsOpen W := isClosed_closure.isOpen_compl
  have heq : μ.restrict W = ν.restrict W := by
    apply Measure.OuterRegular.ext_isOpen
    intro O hO
    rw [Measure.restrict_apply hO.measurableSet, Measure.restrict_apply hO.measurableSet,
      hμ.open_eq _ (hO.inter hW), hν.open_eq _ (hO.inter hW)]
    apply perimeterIn_congr_ae
    filter_upwards [ae_restrict_mem (hO.inter hW).measurableSet] with y hy
    have hn : y ∉ F ∆ E := fun hyFE => hy.2 (subset_closure hyFE)
    change (y ∈ E) = (y ∈ F)
    simp only [mem_symmDiff, not_or, not_and] at hn
    apply propext
    constructor
    · intro he
      by_contra hf
      exact hn.2 he hf
    · intro hf
      by_contra he
      exact hn.1 hf he
  have hBW : (ball x r)ᶜ ⊆ W := compl_subset_compl.mpr hs
  have hext : μ (ball x r)ᶜ = ν (ball x r)ᶜ := by
    have h := congrArg (fun ρ : Measure AmbientSpace => ρ (ball x r)ᶜ) heq
    simpa only [Measure.restrict_apply isOpen_ball.measurableSet.compl,
      inter_eq_left.mpr hBW] using h
  have hμu : μ univ = perimeter E := by
    rw [hμ.open_eq _ isOpen_univ, ← perimeterN, perimeterN_eq_perimeter E hmE]
  have hνu : ν univ = perimeter F := by
    rw [hν.open_eq _ isOpen_univ, ← perimeterN, perimeterN_eq_perimeter F hmF]
  have hμfin : μ univ < ∞ := by
    rw [hμu, ← perimeterN_eq_perimeter E hmE]
    exact hpE
  have hμB : μ (ball x r) < ∞ := (measure_mono (subset_univ _)).trans_lt hμfin
  have hμC : μ (ball x r)ᶜ < ∞ := (measure_mono (subset_univ _)).trans_lt hμfin
  have hνB : ν (ball x r) < ∞ := by
    rw [hν.open_eq _ isOpen_ball]
    exact hpF _ isOpen_ball isBounded_ball.isCompact_closure
  have hνC : ν (ball x r)ᶜ < ∞ := hext ▸ hμC
  have hνfin : ν univ < ∞ := by
    rw [← measure_add_measure_compl isOpen_ball.measurableSet]
    exact ENNReal.add_lt_top.mpr ⟨hνB, hνC⟩
  refine ⟨?_, ?_⟩
  · rw [HasFinitePerimeter, perimeterN_eq_perimeter F hmF, ← hνu]
    exact hνfin
  · have hsumμ := congrArg ENNReal.toReal
      (measure_add_measure_compl (μ := μ) (s := ball x r) isOpen_ball.measurableSet)
    have hsumν := congrArg ENNReal.toReal
      (measure_add_measure_compl (μ := ν) (s := ball x r) isOpen_ball.measurableSet)
    rw [ENNReal.toReal_add hμB.ne hμC.ne, hμu, hμ.open_eq _ isOpen_ball] at hsumμ
    rw [ENNReal.toReal_add hνB.ne hνC.ne, hνu, hν.open_eq _ isOpen_ball, ← hext] at hsumν
    linarith only [hsumμ, hsumν]

lemma abs_volumeReal_sub_le_symmDiff {E F : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hmF : NullMeasurableSet F volume)
    (hvE : volume E < ∞) (hvF : volume F < ∞) :
    |volume.real E - volume.real F| ≤ volume.real (E ∆ F) := by
  have hiE : Integrable (E.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) hvE.ne).integrable_indicator₀ hmE
  have hiF : Integrable (F.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) hvF.ne).integrable_indicator₀ hmF
  have h := norm_integral_le_integral_norm
    (E.indicator (fun _ => (1 : ℝ)) - F.indicator (fun _ => (1 : ℝ))) (μ := volume)
  simp only [Pi.sub_apply] at h
  rw [integral_sub hiE hiF, integral_indicator₀ hmE, integral_indicator₀ hmF] at h
  simp only [setIntegral_const, smul_eq_mul, mul_one, Real.norm_eq_abs] at h
  exact h.trans_eq (integral_abs_indicator_sub E F hmE hmF)

/-- A global volume penalty implies the exact unit-scale local perimeter comparison.
The nonlocal Lipschitz constant is uniform over all admissible local competitors. -/
theorem IsLebesgueFixedVolumeMinimizer.isOmegaMinimal_of_volume_penalty
    {V Λ : ℝ} {E : Set AmbientSpace} (hE : IsLebesgueFixedVolumeMinimizer V E)
    (hV : 0 < V) (hΛ : 0 ≤ Λ)
    (hpen : ∀ F : Set AmbientSpace, NullMeasurableSet F volume → volume F < ∞ →
      HasFinitePerimeter F →
      energy E ≤ energy F + ENNReal.ofReal (Λ * |volume.real F - V|)) :
    IsOmegaMinimal E
      (coulombBoundConstant *
        (V + volume.real (ball (0 : AmbientSpace) 1)) ^ ((2 : ℝ) / 3) + Λ) := by
  let M : ℝ := V + volume.real (ball (0 : AmbientSpace) 1)
  let C : ℝ := coulombBoundConstant * M ^ ((2 : ℝ) / 3)
  have hM : 0 ≤ M := add_nonneg hV.le ENNReal.toReal_nonneg
  have hC : 0 ≤ C := by dsimp [C, coulombBoundConstant]; positivity
  have hω : 0 ≤ C + Λ := add_nonneg hC hΛ
  have hvE : volume E < ∞ := hE.2.1 ▸ ENNReal.ofReal_lt_top
  have hpE : HasFinitePerimeter E := by
    rw [HasFinitePerimeter, perimeterN_eq_perimeter E hE.1]
    exact hE.2.2.1
  have hlE := hpE.hasLocallyFinitePerimeter
  have hv1 : volume (ball (0 : AmbientSpace) 1) < ∞ := isBounded_ball.measure_lt_top
  have hEM : volume E ≤ ENNReal.ofReal M := by
    rw [hE.2.1]
    apply ENNReal.ofReal_le_ofReal
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  refine ⟨hω, by norm_num, hE.1, hlE, ?_⟩
  intro x r hr hrr F hmF hlF _hc hs
  have hr1 : r ≤ 1 := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa using hrr)
  have hsd : F ∆ E ⊆ ball x r := subset_closure.trans hs
  have hesd : E ∆ F ⊆ ball x r := by rwa [symmDiff_comm]
  have hFB : F ⊆ E ∪ ball x r := by
    intro y hy
    by_cases he : y ∈ E
    · exact Or.inl he
    · exact Or.inr (hsd (Or.inl ⟨hy, he⟩))
  have hball : volume (ball x r) ≤ volume (ball (0 : AmbientSpace) 1) := by
    calc
      _ ≤ volume (ball x 1) := measure_mono (ball_subset_ball hr1)
      _ = _ := by simp only [EuclideanSpace.volume_ball_fin_three]
  have hFM : volume F ≤ ENNReal.ofReal M := by
    calc
      _ ≤ volume (E ∪ ball x r) := measure_mono hFB
      _ ≤ volume E + volume (ball x r) := measure_union_le _ _
      _ ≤ ENNReal.ofReal V + volume (ball (0 : AmbientSpace) 1) := by
        rw [hE.2.1]
        exact add_le_add le_rfl hball
      _ = _ := by
        rw [← ENNReal.ofReal_toReal hv1.ne, ← ENNReal.ofReal_add hV.le ENNReal.toReal_nonneg]
        rfl
  have hvF : volume F < ∞ := hFM.trans_lt ENNReal.ofReal_lt_top
  have hvΔ : volume (E ∆ F) < ∞ := (measure_mono hesd).trans_lt isBounded_ball.measure_lt_top
  obtain ⟨hpF, hlocal⟩ := perimeter_localization_of_compact_symmDiff hE.1 hmF hpE hlF x r hs
  have hpFr : perimeter F < ∞ := by rwa [← perimeterN_eq_perimeter F hmF]
  have hcE := coulombEnergy_lt_top E hvE
  have hcF := coulombEnergy_lt_top F hvF
  have heF : energy F < ∞ := ENNReal.add_lt_top.mpr ⟨hpFr, hcF⟩
  have hP := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨heF.ne, ENNReal.ofReal_ne_top⟩) (hpen F hmF hvF hpF)
  rw [ENNReal.toReal_add heF.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (mul_nonneg hΛ (abs_nonneg _)), energy,
    ENNReal.toReal_add hE.2.2.1.ne hcE.ne, energy,
    ENNReal.toReal_add hpFr.ne hcF.ne] at hP
  have hvolE : volume.real E = V := by
    rw [measureReal_def, hE.2.1, ENNReal.toReal_ofReal hV.le]
  have hvol : |volume.real F - V| ≤ volume.real (E ∆ F) := by
    rw [← hvolE, abs_sub_comm]
    exact abs_volumeReal_sub_le_symmDiff hE.1 hmF hvE hvF
  have hD := coulombEnergy_lipschitz E F hE.1 hmF hM hEM hFM
  have hD' : (coulombEnergy F).toReal - (coulombEnergy E).toReal ≤ C * volume.real (E ∆ F) :=
    (neg_le_abs ((coulombEnergy E).toReal - (coulombEnergy F).toReal)).trans hD |>
      (by simpa only [neg_sub] using ·)
  have hV' := mul_le_mul_of_nonneg_left hvol hΛ
  have hpLocal : (perimeterIn E (ball x r)).toReal ≤
      (perimeterIn F (ball x r)).toReal + (C + Λ) * volume.real (E ∆ F) := by
    nlinarith only [hP, hD', hV', hlocal]
  have hpEB := hlE (ball x r) isOpen_ball isBounded_ball.isCompact_closure
  have hpFB := hlF (ball x r) isOpen_ball isBounded_ball.isCompact_closure
  have h := ENNReal.ofReal_le_ofReal hpLocal
  simp only [measureReal_def] at h
  rwa [ENNReal.ofReal_toReal hpEB.ne, ENNReal.ofReal_add ENNReal.toReal_nonneg
    (mul_nonneg hω ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hpFB.ne,
    ENNReal.ofReal_mul hω, ENNReal.ofReal_toReal hvΔ.ne] at h

/-- Blueprint `lem:quasiminimal`: every genuine fixed-volume minimizer has a
finite, explicit unit-scale perimeter quasiminimality constant. -/
theorem IsLebesgueFixedVolumeMinimizer.isOmegaMinimal
    {V : ℝ} {E : Set AmbientSpace} (hE : IsLebesgueFixedVolumeMinimizer V E) (hV : 0 < V) :
    IsOmegaMinimal E
      (coulombBoundConstant * (V + volume.real (ball (0 : AmbientSpace) 1)) ^ ((2 : ℝ) / 3) +
        62 * (energy E).toReal / V) := by
  obtain ⟨Λ, hΛ, rfl, hpen⟩ := hE.global_volume_penalization hV
  exact hE.isOmegaMinimal_of_volume_penalty hV hΛ hpen

/-- The corresponding unit-scale conclusion for the original Borel minimizer convention. -/
theorem IsFixedVolumeMinimizer.isOmegaMinimal
    {V : ℝ} {E : Set AmbientSpace} (hE : IsFixedVolumeMinimizer V E) (hV : 0 < V) :
    IsOmegaMinimal E
      (coulombBoundConstant * (V + volume.real (ball (0 : AmbientSpace) 1)) ^ ((2 : ℝ) / 3) +
        62 * (energy E).toReal / V) :=
  hE.toLebesgue.isOmegaMinimal hV

end LiquidDrop
