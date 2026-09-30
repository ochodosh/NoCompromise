module

public import NoCompromise.Surface.SurfaceChart
public import NoCompromise.Area.SmoothSurface
public import NoCompromise.Area.Rectifiable

@[expose] public section

/-!
# Compact smooth embedded surfaces are rectifiable with finite area

For a smooth embedded surface `S` (local regular level sets of a `C^∞` function), the
projection chart `IsSmoothEmbeddedSurface.exists_projection_chart` has a `C¹` inverse on an
open planar set. Near each point this inverse is Lipschitz on a closed ball and extends to a
global Lipschitz map of the plane whose image of the ball contains a neighbourhood of the
point in `S`. Compactness gives finitely many such maps, hence countable
`H²`-rectifiability and finite normalized `H²` measure.
-/

noncomputable section

open MeasureTheory Set Function Metric
open scoped ENNReal NNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Near each of its points, a smooth embedded surface is contained in a global Lipschitz
image of a compact planar set. -/
lemma IsSmoothEmbeddedSurface.exists_local_lipschitz_chart {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {q : E₃} (hq : q ∈ S) :
    ∃ W : Set E₃, IsOpen W ∧ q ∈ W ∧
      ∃ (g : EuclideanSpace ℝ (Fin 2) → E₃) (L : ℝ≥0)
        (K : Set (EuclideanSpace ℝ (Fin 2))),
        LipschitzWith L g ∧ IsCompact K ∧ S ∩ W ⊆ g '' K := by
  obtain ⟨e, P, U, hU, hqU, hsrc, hqsrc, he0, heP, hcd⟩ := hS.exists_projection_chart hq 1
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ e.target := he0 ▸ e.map_source hqsrc
  obtain ⟨C, t, ht, hCt⟩ :=
    (hcd.contDiffAt (e.open_target.mem_nhds h0)).exists_lipschitzOnWith
  obtain ⟨r, hr, hrsub⟩ :=
    (nhds_basis_closedBall (x := (0 : EuclideanSpace ℝ (Fin 2)))).mem_iff.mp
      (Filter.inter_mem ht (e.open_target.mem_nhds h0))
  obtain ⟨g, hg, hfg⟩ := (hCt.mono fun y hy => (hrsub hy).1).extend_finite_dimension
  have hcont : Continuous fun x : E₃ => P (x - q) := by fun_prop
  refine ⟨U ∩ (fun x : E₃ => P (x - q)) ⁻¹' ball 0 r,
    hU.inter (isOpen_ball.preimage hcont), ⟨hqU, by simpa using hr⟩, g, _, closedBall 0 r,
    hg, isCompact_closedBall _ _, ?_⟩
  rintro y ⟨hyS, hyU, hyB⟩
  have hys : (⟨y, hyS⟩ : S) ∈ e.source := by rw [hsrc]; exact hyU
  have hyb : e ⟨y, hyS⟩ ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) r := by
    rw [heP]; exact ball_subset_closedBall hyB
  refine ⟨e ⟨y, hyS⟩, hyb, ?_⟩
  rw [← hfg hyb]
  change ((e.symm (e ⟨y, hyS⟩) : S) : E₃) = y
  rw [e.left_inv hys]

/-- A compact smooth embedded surface is covered by finitely many global Lipschitz images of
compact planar sets. -/
lemma IsSmoothEmbeddedSurface.exists_finite_lipschitz_cover_of_isCompact {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) :
    ∃ (ι : Type) (_ : Fintype ι)
      (g : ι → EuclideanSpace ℝ (Fin 2) → E₃) (L : ι → ℝ≥0)
      (K : ι → Set (EuclideanSpace ℝ (Fin 2))),
      (∀ i, LipschitzWith (L i) (g i)) ∧ (∀ i, IsCompact (K i)) ∧ S ⊆ ⋃ i, g i '' K i := by
  classical
  have hloc := fun x (hx : x ∈ S) => hS.exists_local_lipschitz_chart hx
  choose W hWo hxW g L K hg hK hsub using hloc
  obtain ⟨t, ht⟩ := hc.elim_nhds_subcover' W fun x hx => (hWo x hx).mem_nhds (hxW x hx)
  refine ⟨t, inferInstance, fun i => g i.1.1 i.1.2, fun i => L i.1.1 i.1.2,
    fun i => K i.1.1 i.1.2, fun i => hg _ _, fun i => hK _ _, ?_⟩
  intro y hy
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (ht hy)
  exact mem_iUnion.mpr ⟨⟨i, hi⟩, hsub i.1 i.2 ⟨hy, hyi⟩⟩

/-- A compact smooth embedded surface is countably `H²`-rectifiable. -/
theorem IsSmoothEmbeddedSurface.countablyH2Rectifiable_of_isCompact {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) : CountablyH2Rectifiable S := by
  classical
  obtain ⟨ι, _, g, L, K, hg, _, hcover⟩ := hS.exists_finite_lipschitz_cover_of_isCompact hc
  obtain ⟨e, he⟩ := exists_surjective_nat (Option ι)
  refine ⟨hc.isClosed.measurableSet.nullMeasurableSet,
    fun j => (e j).elim (fun _ => 0) g, fun j => (e j).elim 0 L, ?_, ?_⟩
  · intro j
    change LipschitzWith ((e j).elim 0 L) ((e j).elim (fun _ => 0) g)
    cases e j with
    | none => exact LipschitzWith.const (0 : EuclideanSpace ℝ (Fin 3))
    | some i => exact hg i
  · refine measure_mono_null (fun y hy => ?_) measure_empty
    obtain ⟨hyS, hyn⟩ := hy
    exfalso
    apply hyn
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hyS)
    obtain ⟨j, hj⟩ := he (some i)
    refine mem_iUnion.mpr ⟨j, ?_⟩
    change y ∈ range ((e j).elim (fun _ => 0) g)
    rw [hj]
    exact image_subset_range _ _ hi

/-- A compact smooth embedded surface has finite normalized two-dimensional Hausdorff
measure. -/
theorem IsSmoothEmbeddedSurface.hausdorffMeasure2_lt_top_of_isCompact {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) : hausdorffMeasure2 3 S < ⊤ := by
  classical
  obtain ⟨ι, _, g, L, K, hg, hK, hcover⟩ := hS.exists_finite_lipschitz_cover_of_isCompact hc
  calc
    hausdorffMeasure2 3 S ≤ hausdorffMeasure2 3 (⋃ i, g i '' K i) := measure_mono hcover
    _ ≤ ∑ i, hausdorffMeasure2 3 (g i '' K i) := measure_iUnion_fintype_le _ _
    _ < ⊤ := by
      refine ENNReal.sum_lt_top.mpr fun i _ => ?_
      refine ((hausdorffMeasure2_image_le_of_lipschitzOn
        ((hg i).lipschitzOnWith (s := K i))).trans_lt ?_)
      rw [hausdorffMeasure2_plane]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) (hK i).measure_lt_top

end LiquidDrop
