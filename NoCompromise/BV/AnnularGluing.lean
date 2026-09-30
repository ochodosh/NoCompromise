module

public import NoCompromise.BV.AnnularGluingCoarea
public import NoCompromise.BV.AnnularGluingTraces

@[expose] public section

/-!
# Annular BV gluing with vanishing mismatch

At common good radii the actual two-sided traces are the density-one
indicators. Their mismatch is exactly the spherical symmetric-difference area.
Slicing and the first-moment selection then convert actual annular L¹
convergence into radii with vanishing gluing cost.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma ofReal_integral_abs_sub_eq_symmDiff_of_ae {μ : Measure AmbientSpace}
    {T S : AmbientSpace → ℝ} {E F : Set AmbientSpace}
    (hT : Integrable T μ) (hS : Integrable S μ)
    (hmE : NullMeasurableSet E μ) (hmF : NullMeasurableSet F μ)
    (hTE : T =ᵐ[μ] E.indicator (fun _ => (1 : ℝ)))
    (hSF : S =ᵐ[μ] F.indicator (fun _ => (1 : ℝ))) :
    ENNReal.ofReal (∫ z, |T z - S z| ∂μ) = μ (E ∆ F) := by
  calc
    _ = eLpNorm (T - S) 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm (hT.sub hS).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hT.sub hS)]
      simp only [Pi.sub_apply, Real.norm_eq_abs]
    _ = eLpNorm (E.indicator (fun _ => (1 : ℝ)) -
        F.indicator (fun _ => (1 : ℝ))) 1 μ := eLpNorm_congr_ae (hTE.sub hSF)
    _ = _ := eLpNorm_indicator_sub_eq_symmDiff hmE hmF

/-- Exact trace gluing on a common good sphere, in every containing open set. -/
theorem IsGoodRadius.gluing_perimeterIn_le {E F : Set AmbientSpace}
    {hE : HasLocallyFinitePerimeter E} {hmE : NullMeasurableSet E volume}
    {hF : HasLocallyFinitePerimeter F} {hmF : NullMeasurableSet F volume}
    {c : AmbientSpace} {r : ℝ} (hgE : IsGoodRadius E hE hmE c r)
    (hgF : IsGoodRadius F hF hmF c r)
    {W : Set AmbientSpace} (hW : IsOpen W) (hBW : closedBall c r ⊆ W) :
    perimeterIn ((F ∩ ball c r) ∪ (E \ ball c r)) W ≤
      perimeterIn F (ball c r) + perimeterIn E (W \ closedBall c r) +
        hausdorffMeasure2 3 ((densityOne F ∆ densityOne E) ∩ sphere c r) := by
  have hB := hasC1Boundary_ball c hgE.1
  have hK : IsCompact (frontier (ball c r)) := by
    rw [frontier_ball c hgE.1.ne']
    exact isCompact_sphere c r
  have hcl : closure (ball c r) ⊆ W := by rwa [closure_ball c hgE.1.ne']
  obtain ⟨Tin, Tout, hi, ho, hc, hv⟩ := bv_gluing_on_open hB isOpen_ball
    (isBounded_ball (x := c) (r := r)) hW hcl
    (hE.isLocallyBVOn_indicator hmE W) (hF.isLocallyBVOn_indicator hmF W)
  have hTin : Tin =ᵐ[(hausdorffMeasure2 3).restrict (frontier (ball c r))]
      (densityOne F).indicator (fun _ => (1 : ℝ)) := by
    apply hB.ae_of_chartwise hK
    intro d hd
    have hh := hgF.2.2 d hd
    rw [← frontier_ball c hgE.1.ne'] at hh
    filter_upwards [hc d hd, hh] with z hz ht
    intro hzd
    exact (hz hzd).1.trans (ht hzd)
  have hTout : Tout =ᵐ[(hausdorffMeasure2 3).restrict (frontier (ball c r))]
      (densityOne E).indicator (fun _ => (1 : ℝ)) := by
    apply hB.ae_of_chartwise hK
    intro d hd
    have hh := hgE.upperBVTrace_eq d hd
    rw [← frontier_ball c hgE.1.ne'] at hh
    filter_upwards [hc d hd, hh] with z hz ht
    intro hzd
    exact (hz hzd).2.trans (ht hzd)
  have hcost := ofReal_integral_abs_sub_eq_symmDiff_of_ae hi ho
    (measurableSet_densityOne hmF).nullMeasurableSet
    (measurableSet_densityOne hmE).nullMeasurableSet hTin hTout
  rw [Measure.restrict_apply
    ((measurableSet_densityOne hmF).symmDiff (measurableSet_densityOne hmE)),
    frontier_ball c hgE.1.ne'] at hcost
  rw [frontier_ball c hgE.1.ne', hcost, closure_ball c hgE.1.ne'] at hv
  have he : ((F ∩ ball c r) ∪ (E \ ball c r) : Set AmbientSpace) =ᵐ[volume.restrict W]
      ((F ∩ ball c r) ∪ (E ∩ (W \ ball c r)) : Set AmbientSpace) := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with z hz
    change (z ∈ (F ∩ ball c r) ∪ (E \ ball c r)) =
      (z ∈ (F ∩ ball c r) ∪ (E ∩ (W \ ball c r)))
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, hz, true_and]
  exact (perimeterIn_congr_ae W he).le.trans hv

/-- The global gluing estimate permits infinite original perimeters. -/
theorem IsGoodRadius.gluing_perimeter_le {E F : Set AmbientSpace}
    {hE : HasLocallyFinitePerimeter E} {hmE : NullMeasurableSet E volume}
    {hF : HasLocallyFinitePerimeter F} {hmF : NullMeasurableSet F volume}
    {c : AmbientSpace} {r : ℝ} (hgE : IsGoodRadius E hE hmE c r)
    (hgF : IsGoodRadius F hF hmF c r) :
    perimeter ((F ∩ ball c r) ∪ (E \ ball c r)) ≤
      perimeterIn F (ball c r) + perimeterIn E (closedBall c r)ᶜ +
        hausdorffMeasure2 3 ((densityOne F ∆ densityOne E) ∩ sphere c r) := by
  have hh := hgE.gluing_perimeterIn_le hgF isOpen_univ (subset_univ _)
  have hmH : NullMeasurableSet ((F ∩ ball c r) ∪ (E \ ball c r)) volume :=
    (hmF.inter measurableSet_ball.nullMeasurableSet).union
    (hmE.diff measurableSet_ball.nullMeasurableSet)
  rw [← perimeterN_eq_perimeter _ hmH]
  simpa only [perimeterN, sdiff_eq, univ_inter] using hh

/-- A single full-measure family of radii works for every member of the
sequence and every containing open region. -/
theorem ae_annular_gluing_perimeter {E : ℕ → Set AmbientSpace} {F : Set AmbientSpace}
    (hE : ∀ j, HasLocallyFinitePerimeter (E j))
    (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hF : HasLocallyFinitePerimeter F) (hmF : NullMeasurableSet F volume)
    (c : AmbientSpace) {a b : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ r ∂volume.restrict (Ioo a b), ∀ j,
      (∀ W, IsOpen W → closedBall c b ⊆ W →
        perimeterIn ((F ∩ ball c r) ∪ (E j \ ball c r)) W ≤
          perimeterIn F (ball c r) + perimeterIn (E j) (W \ closedBall c r) +
            hausdorffMeasure2 3 ((densityOne F ∆ densityOne (E j)) ∩ sphere c r)) ∧
      perimeter ((F ∩ ball c r) ∪ (E j \ ball c r)) ≤
        perimeterIn F (ball c r) + perimeterIn (E j) (closedBall c r)ᶜ +
          hausdorffMeasure2 3 ((densityOne F ∆ densityOne (E j)) ∩ sphere c r) := by
  have hs : Ioo a b ⊆ Ioi (0 : ℝ) := fun r hr => ha.trans_lt hr.1
  have hgF := ae_restrict_of_ae_restrict_of_subset hs (ae_isGoodRadius F hF hmF c)
  have hgE := ae_all_iff.mpr fun j => ae_restrict_of_ae_restrict_of_subset hs
    (ae_isGoodRadius (E j) (hE j) (hmE j) c)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hgF, hgE] with r hr hFr hEr
  intro j
  exact ⟨fun W hW hbW => (hEr j).gluing_perimeterIn_le hFr hW
    ((closedBall_subset_closedBall hr.2.le).trans hbW), (hEr j).gluing_perimeter_le hFr⟩

/-- Actual annular L¹ convergence and agreement of the inside target on the
annulus give common good radii with vanishing boundary cost. -/
theorem exists_annular_gluing_radii {E : ℕ → Set AmbientSpace} {F G : Set AmbientSpace}
    (hE : ∀ j, HasLocallyFinitePerimeter (E j))
    (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hF : HasLocallyFinitePerimeter F) (hmF : NullMeasurableSet F volume)
    (hmG : NullMeasurableSet G volume)
    (c : AmbientSpace) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hFG : F =ᵐ[volume.restrict (ball c b \ closedBall c a)] G)
    (ht : Tendsto (fun j => eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - G.indicator (fun _ => (1 : ℝ)))
      1 (volume.restrict (ball c b \ closedBall c a))) atTop (𝓝 0)) :
    ∃ r : ℕ → ℝ,
      (∀ j, r j ∈ Ioo a b ∧ IsGoodRadius (E j) (hE j) (hmE j) c (r j) ∧
        IsGoodRadius F hF hmF c (r j)) ∧
      Tendsto (fun j => hausdorffMeasure2 3
        ((densityOne F ∆ densityOne (E j)) ∩ sphere c (r j))) atTop (𝓝 0) ∧
      (∀ j W, IsOpen W → closedBall c b ⊆ W →
        perimeterIn ((F ∩ ball c (r j)) ∪ (E j \ ball c (r j))) W ≤
          perimeterIn F (ball c (r j)) + perimeterIn (E j) (W \ closedBall c (r j)) +
            hausdorffMeasure2 3 ((densityOne F ∆ densityOne (E j)) ∩ sphere c (r j))) ∧
      ∀ j, perimeter ((F ∩ ball c (r j)) ∪ (E j \ ball c (r j))) ≤
        perimeterIn F (ball c (r j)) + perimeterIn (E j) (closedBall c (r j))ᶜ +
          hausdorffMeasure2 3 ((densityOne F ∆ densityOne (E j)) ∩ sphere c (r j)) := by
  have hs : Ioo a b ⊆ Ioi (0 : ℝ) := fun r hr => ha.trans_lt hr.1
  have hgood (j) : ∀ᵐ r ∂volume.restrict (Ioo a b),
      IsGoodRadius (E j) (hE j) (hmE j) c r ∧ IsGoodRadius F hF hmF c r :=
    (ae_restrict_of_ae_restrict_of_subset hs
      (ae_isGoodRadius (E j) (hE j) (hmE j) c)).and
      (ae_restrict_of_ae_restrict_of_subset hs (ae_isGoodRadius F hF hmF c))
  have hvol : Tendsto (fun j => volume ((F ∆ E j) ∩ (ball c b \ closedBall c a)))
      atTop (𝓝 0) := by
    simpa only [volume_symmDiff_inter_eq_indicator_error (hmE _) hmF hmG hFG] using ht
  obtain ⟨r, hr, hcost⟩ := exists_radii_spherical_mismatch_tendsto_zero hmE
    (fun _ => hmF) c ha hab hgood hvol
  exact ⟨r, hr, hcost, fun j W hW hbW => (hr j).2.1.gluing_perimeterIn_le (hr j).2.2 hW
    ((closedBall_subset_closedBall (hr j).1.2.le).trans hbW),
    fun j => (hr j).2.1.gluing_perimeter_le (hr j).2.2⟩

end LiquidDrop
