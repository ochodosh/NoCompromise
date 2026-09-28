import NoCompromise.Regularity.GraphPhaseCapsGeometry

/-!
# Small excess selects the correctly oriented cap phases

Compactness and the already proved halfspace classification rule out a wrong
constant phase on either cleared open region. No cap trace is assumed in this
argument.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma graphPhaseCaps_l1_eq_volume {E F U K : Set AmbientSpace} {a b : ℝ}
    (hE : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U] fun _ => a)
    (hF : F.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U] fun _ => b)
    (hKU : K ⊆ U) (hab : |a - b| = 1) :
    (∫ x in K, |E.indicator (fun _ => (1 : ℝ)) x -
      F.indicator (fun _ => (1 : ℝ)) x|) = volume.real K := by
  have he : (fun x => |E.indicator (fun _ => (1 : ℝ)) x -
      F.indicator (fun _ => (1 : ℝ)) x|) =ᵐ[volume.restrict K] fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKU hE,
      ae_restrict_of_ae_restrict_of_subset hKU hF] with x hx hx'
    rw [hx, hx', hab]
  rw [integral_congr_ae he, integral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply_univ]
  rfl

lemma graphPhaseCaps_halfspace_phases {F : Set AmbientSpace}
    (hF : F =ᵐ[volume.restrict (standardCylinder (3 / 4))]
      {x : AmbientSpace | x 2 < 0}) : HasGraphCapPhases F := by
  constructor
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (fun x hx => (graphLowerCapRegion_subset hx).1) hF,
      ae_restrict_mem isOpen_graphLowerCapRegion.measurableSet] with x hx hxU
    have hxF : x ∈ F := by
      apply hx.mpr
      exact (graphLowerCapRegion_subset hxU).2
    simp [hxF]
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (fun x hx => (graphUpperCapRegion_subset hx).1) hF,
      ae_restrict_mem isOpen_graphUpperCapRegion.measurableSet] with x hx hxU
    have hxF : x ∉ F := by
      intro hh
      exact (not_lt_of_gt (graphUpperCapRegion_subset hxU).2) (hx.mp hh)
    simp [hxF]

/-- Sufficiently small genuine unit excess and quasiminimality error force the actual
lower-one and upper-zero phases. The threshold precedes the set and error parameter. -/
theorem graph_phase_caps_phases :
    ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε → HasGraphCapPhases E := by
  classical
  obtain ⟨εh, hεh, hheight⟩ := height_bound (by norm_num : (0 : ℝ) < 1 / 4)
  by_contra hn
  push Not at hn
  have hex (j : ℕ) : ∃ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) ∧
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ min εh (1 / ((j : ℝ) + 1)) ∧
      ¬ HasGraphCapPhases E := hn _ (lt_min hεh (by positivity))
  choose E ω hE h0 hsmall hbad using hex
  have hnonneg (j : ℕ) : 0 ≤ cylindricalExcess (E j) (hE j).locallyFinite
      (hE j).nullMeasurable 0 1 (EuclideanSpace.single 2 1) :=
    div_nonneg (normalExcessIntegral_nonneg _ _ _ _ _) (sq_nonneg _)
  have hω (j : ℕ) : ω j ≤ 1 := by
    have ht := (hsmall j).trans (min_le_right _ _)
    have hh : 1 / ((j : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) j]
    linarith [hnonneg j]
  have hheightE (j : ℕ) :
      ∀ x ∈ frontier (densityOne (E j)) ∩ standardCylinder (3 / 4), |x 2| < 1 / 4 := by
    have he := (hsmall j).trans (min_le_left _ _)
    have hh := hheight (E j) (ω j) (hE j) (h0 j) 1 (by norm_num) le_rfl
      (by simpa only [mul_one] using he)
    simpa only [mul_one] using hh
  have hwrong (j : ℕ) :
      ((E j).indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict graphLowerCapRegion]
        fun _ => 0) ∨
      ((E j).indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict graphUpperCapRegion]
        fun _ => 1) := by
    obtain ⟨hl, hu⟩ := graphPhaseCaps_phase_dichotomy (hE j) (hheightE j)
    rcases hl with hl | hl
    · exact Or.inl hl
    · rcases hu with hu | hu
      · exact False.elim (hbad j ⟨hl, hu⟩)
      · exact Or.inr hu
  have he : Tendsto (fun j => normalExcessIntegral (E j) (hE j).locallyFinite
      (hE j).nullMeasurable (standardCylinder (3 / 4)) (EuclideanSpace.single 2 1))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun j => normalExcessIntegral_nonneg _ _ _ _ _)
      (g := fun j : ℕ => 1 / ((j : ℝ) + 1))
    · intro j
      have hm := normalExcessIntegral_mono (E j) (hE j).locallyFinite (hE j).nullMeasurable
        (U := standardCylinder (3 / 4))
        (isBounded_cylinder 0 1 (ν := EuclideanSpace.single 2 1) (by simp))
        (by rw [standardCylinder_eq_cylinder]; exact cylinder_mono (by norm_num))
        (EuclideanSpace.single 2 1)
      have hs := (hsmall j).trans (min_le_right _ _)
      have hnω := (hE j).nonneg
      simp only [cylindricalExcess, one_pow, div_one] at hs
      linarith
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨F, hmF, _, k, hk, hl1⟩ := exists_quasiminimal_subsequence hE hω
  have hhalf := height_limit_is_halfspace_zero (fun j => hE (k j)) (fun j => hω (k j))
    (fun j => h0 (k j)) (by norm_num : (0 : ℝ) < 3 / 4)
    (he.comp hk.tendsto_atTop) hmF.nullMeasurableSet hl1
  have hFp := graphPhaseCaps_halfspace_phases hhalf
  obtain ⟨KL, hKL, hcKL, hposKL⟩ := isOpen_graphLowerCapRegion.exists_lt_isCompact
    (isOpen_graphLowerCapRegion.measure_pos volume graphLowerCapRegion_nonempty)
  obtain ⟨KU, hKU, hcKU, hposKU⟩ := isOpen_graphUpperCapRegion.exists_lt_isCompact
    (isOpen_graphUpperCapRegion.measure_pos volume graphUpperCapRegion_nonempty)
  have hposL : 0 < volume.real KL := ENNReal.toReal_pos hposKL.ne' hcKL.measure_lt_top.ne
  have hposU : 0 < volume.real KU := ENNReal.toReal_pos hposKU.ne' hcKU.measure_lt_top.ne
  have hb (j : ℕ) : min (volume.real KL) (volume.real KU) ≤
      (∫ x in KL, |(E (k j)).indicator (fun _ => (1 : ℝ)) x -
        F.indicator (fun _ => (1 : ℝ)) x|) +
      (∫ x in KU, |(E (k j)).indicator (fun _ => (1 : ℝ)) x -
        F.indicator (fun _ => (1 : ℝ)) x|) := by
    rcases hwrong (k j) with hj | hj
    · rw [graphPhaseCaps_l1_eq_volume hj hFp.1 hKL (by norm_num)]
      exact (min_le_left _ _).trans (le_add_of_nonneg_right (integral_nonneg fun _ => abs_nonneg _))
    · rw [graphPhaseCaps_l1_eq_volume hj hFp.2 hKU (by norm_num)]
      exact (min_le_right _ _).trans (le_add_of_nonneg_left (integral_nonneg fun _ => abs_nonneg _))
  have ht := (hl1 KL hcKL).add (hl1 KU hcKU)
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hb)
  exact (not_le_of_gt (lt_min hposL hposU)) (by simpa only [zero_add] using hh)

end LiquidDrop
