module

public import NoCompromise.Regularity.OmegaMinimal
public import NoCompromise.Regularity.DensityRadial

@[expose] public section

/-!
# Emptying and filling comparisons for quasiminimal sets

A good-radius cut at radius `r < 1` is an admissible competitor in the unit ball.
The exact cut formula and cancellation of the finite annular perimeter give the
comparison at `r` directly, with no inadmissible touching-boundary competitor.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsOmegaMinimalAtScales.compl {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    {ω : ℝ} {r₀ : ℝ≥0∞} (hE : IsOmegaMinimalAtScales E ω r₀) :
    IsOmegaMinimalAtScales Eᶜ ω r₀ := by
  have hlocal {S : Set (EuclideanSpace ℝ (Fin n))}
      (hmS : NullMeasurableSet S volume) (hpS : HasLocallyFinitePerimeter S) :
      HasLocallyFinitePerimeter Sᶜ := by
    intro U hU hcU
    rw [perimeterIn_compl hmS hU]
    exact hpS U hU hcU
  refine ⟨hE.nonneg, hE.scale_pos, hE.nullMeasurable.compl,
    hlocal hE.nullMeasurable hE.locallyFinite, ?_⟩
  intro x r hr hrr F hmF hpF hc hs
  have heq : Fᶜ ∆ E = F ∆ Eᶜ := by ext y; simp only [mem_symmDiff, mem_compl_iff]; tauto
  have herr : E ∆ Fᶜ = Eᶜ ∆ F := by ext y; simp only [mem_symmDiff, mem_compl_iff]; tauto
  have h := hE.comparison x r hr hrr Fᶜ hmF.compl (hlocal hmF hpF)
    (heq ▸ hc) (heq ▸ hs)
  rw [perimeterIn_compl hmF isOpen_ball, herr] at h
  rwa [perimeterIn_compl hE.nullMeasurable isOpen_ball]

lemma IsOmegaMinimal.compl {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) : IsOmegaMinimal Eᶜ ω :=
  IsOmegaMinimalAtScales.compl hE

lemma IsGoodRadius.hasLocallyFinitePerimeter_cut_out {E : Set AmbientSpace}
    {hE : HasLocallyFinitePerimeter E} {hmE : NullMeasurableSet E volume}
    {x : AmbientSpace} {r : ℝ} (hg : IsGoodRadius E hE hmE x r) :
    HasLocallyFinitePerimeter (E \ ball x r) := by
  intro U hU hcU
  rw [(hg.perimeterIn_cut_identities hU).2]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact (variation_mono hU.measurableSet inter_subset_left).trans_lt (hE U hU hcU)
  · exact (measure_mono inter_subset_right).trans_lt
      (hausdorffMeasure2_spherical_section_lt_top E x r)

lemma IsGoodRadius.hasFinitePerimeter_cut_in {E : Set AmbientSpace}
    {hE : HasLocallyFinitePerimeter E} {hmE : NullMeasurableSet E volume}
    {x : AmbientSpace} {r : ℝ} (hg : IsGoodRadius E hE hmE x r) :
    HasFinitePerimeter (E ∩ ball x r) := by
  rw [HasFinitePerimeter,
    perimeterN_eq_perimeter _ (hmE.inter measurableSet_ball.nullMeasurableSet),
    hg.perimeter_cut_identities.1]
  exact ENNReal.add_lt_top.mpr
    ⟨hE _ isOpen_ball isBounded_ball.isCompact_closure,
      hausdorffMeasure2_spherical_section_lt_top E x r⟩

/-- The exact emptying comparison at every good radius strictly below the unit scale. -/
theorem IsOmegaMinimal.perimeterIn_ball_le_section_add_volume
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω) (x : AmbientSpace)
    {r : ℝ} (hg : IsGoodRadius E hE.locallyFinite hE.nullMeasurable x r) (hr1 : r < 1) :
    perimeterIn E (ball x r) ≤ hausdorffMeasure2 3 (densityOne E ∩ sphere x r) +
      ENNReal.ofReal ω * volume (E ∩ ball x r) := by
  let F : Set AmbientSpace := E \ ball x r
  have hmF : NullMeasurableSet F volume :=
    hE.nullMeasurable.diff measurableSet_ball.nullMeasurableSet
  have hpF : HasLocallyFinitePerimeter F := hg.hasLocallyFinitePerimeter_cut_out
  have hsd : F ∆ E = E ∩ ball x r := by
    ext y
    simp only [F, mem_symmDiff, Set.mem_sdiff, mem_inter_iff]
    tauto
  have hcl : closure (F ∆ E) ⊆ closedBall x r := by
    rw [hsd]
    exact closure_minimal (inter_subset_right.trans ball_subset_closedBall) isClosed_closedBall
  have hc : IsCompact (closure (F ∆ E)) :=
    (isCompact_closedBall x r).of_isClosed_subset isClosed_closure hcl
  have hs : closure (F ∆ E) ⊆ ball x 1 := hcl.trans (closedBall_subset_ball hr1)
  have hcomp := hE.comparison x 1 (by norm_num) (by simp) F hmF hpF hc hs
  have herr : E ∆ F = E ∩ ball x r := (symmDiff_comm E F).trans hsd
  rw [herr] at hcomp
  change perimeterIn E (ball x 1) ≤ perimeterIn (E \ ball x r) (ball x 1) + _ at hcomp
  rw [(hg.perimeterIn_cut_identities isOpen_ball).2] at hcomp
  have hsurf : ball x 1 ∩ (densityOne E ∩ sphere x r) = densityOne E ∩ sphere x r := by
    apply inter_eq_right.mpr
    intro y hy
    change dist y x < 1
    rw [mem_sphere.mp hy.2]
    exact hr1
  rw [hsurf] at hcomp
  let A : Set AmbientSpace := ball x 1 ∩ (closedBall x r)ᶜ
  have hA : IsOpen A := isOpen_ball.inter isClosed_closedBall.isOpen_compl
  have hAF : perimeterIn E A < ∞ :=
    (variation_mono measurableSet_ball inter_subset_left).trans_lt
      (hE.locallyFinite _ isOpen_ball isBounded_ball.isCompact_closure)
  have hp := canonicalPerimeterPolar E hE.locallyFinite hE.nullMeasurable
  let μ := canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable
  have hdis : Disjoint (ball x r) A := by
    apply Set.disjoint_left.mpr
    intro y hy hyA
    exact hyA.2 (ball_subset_closedBall hy)
  have hsub : ball x r ∪ A ⊆ ball x 1 :=
    union_subset (ball_subset_ball hr1.le) inter_subset_left
  have hsum : perimeterIn E (ball x r) + perimeterIn E A ≤ perimeterIn E (ball x 1) := by
    rw [← hp.open_eq _ isOpen_ball, ← hp.open_eq _ hA, ← hp.open_eq _ isOpen_ball]
    rw [← measure_union hdis hA.measurableSet]
    exact measure_mono hsub
  have h := hsum.trans hcomp
  apply ENNReal.le_of_add_le_add_left hAF.ne
  simpa only [add_assoc, add_comm, add_left_comm] using h

/-- The real derivative form of the emptying comparison, at almost every radius. -/
theorem IsOmegaMinimal.ae_cut_comparison {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x : AmbientSpace) :
    ∀ᵐ r : ℝ, 0 < r → r ≤ 1 →
      (perimeterIn E (ball x r)).toReal ≤
        deriv (radialVolume E x) r + ω * radialVolume E x r := by
  have hgood := (ae_restrict_iff' measurableSet_Ioi).mp
    (ae_isGoodRadius E hE.locallyFinite hE.nullMeasurable x)
  have hne : ∀ᵐ r : ℝ, r ≠ 1 := by simp [ae_iff]
  filter_upwards [hgood, ae_deriv_radialVolume hE.nullMeasurable x, hne]
    with r hg hd hn hr hrr
  have h := hE.perimeterIn_ball_le_section_add_volume x (hg hr) (lt_of_le_of_ne hrr hn)
  have hs : hausdorffMeasure2 3 (densityOne E ∩ sphere x r) < ∞ :=
    hausdorffMeasure2_spherical_section_lt_top E x r
  have hv : volume (E ∩ ball x r) < ∞ :=
    (measure_mono inter_subset_right).trans_lt isBounded_ball.measure_lt_top
  have ht := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hs.ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv.ne⟩) h
  rw [ENNReal.toReal_add hs.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hE.nonneg] at ht
  simpa only [hd hr, radialSectionArea, radialVolume] using ht

/-- Blueprint `lem:cut-comparison`, for emptying and filling simultaneously. -/
theorem IsOmegaMinimal.ae_cut_and_fill_comparison {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x : AmbientSpace) :
    ∀ᵐ r : ℝ, 0 < r → r ≤ 1 →
      (perimeterIn E (ball x r)).toReal ≤
        deriv (radialVolume E x) r + ω * radialVolume E x r ∧
      (perimeterIn E (ball x r)).toReal ≤
        deriv (radialVolume Eᶜ x) r + ω * radialVolume Eᶜ x r := by
  filter_upwards [hE.ae_cut_comparison x, hE.compl.ae_cut_comparison x] with r hcut hfill hr hrr
  exact ⟨hcut hr hrr, by
    simpa only [perimeterIn_compl hE.nullMeasurable isOpen_ball] using hfill hr hrr⟩

end LiquidDrop
