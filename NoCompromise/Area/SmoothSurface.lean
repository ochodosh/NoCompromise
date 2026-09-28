import NoCompromise.Area.Rectifiable
import NoCompromise.Area.Graph
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Compact embedded C¹ surfaces are rectifiable with finite area

A compact embedded surface is described by local rotated graphs of `C¹` height
functions over open planar sets. Near each point the height is Lipschitz on a
closed ball and extends to a global Lipschitz height; compactness then yields
finitely many rotated Lipschitz graph charts over compact bases covering the
surface. This gives countable `H²`-rectifiability and finite area.
-/

noncomputable section
open MeasureTheory Set Function Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A compact embedded C¹ surface, described by local rotated graphs: near each of its points `S`
coincides, inside an open set `U`, with the image under a linear isometry `R` of the graph
`graphMap f '' Ω` of a C¹ function over an open planar set. -/
def IsCompactC1EmbeddedSurface (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsCompact S ∧ ∀ x ∈ S, ∃ (U : Set (EuclideanSpace ℝ (Fin 3)))
      (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
      (Ω : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
      IsOpen U ∧ x ∈ U ∧ IsOpen Ω ∧ ContDiffOn ℝ 1 f Ω ∧
      S ∩ U = U ∩ R '' (graphMap f '' Ω)

/-- Near each of its points, a compact embedded C¹ surface is contained in a
global Lipschitz image of a compact planar set. -/
lemma IsCompactC1EmbeddedSurface.exists_local_lipschitz_chart
    {S : Set (EuclideanSpace ℝ (Fin 3))} (h : IsCompactC1EmbeddedSurface S)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ S) :
    ∃ W : Set (EuclideanSpace ℝ (Fin 3)), IsOpen W ∧ x ∈ W ∧
      ∃ (g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (L : ℝ≥0)
        (K : Set (EuclideanSpace ℝ (Fin 2))),
        LipschitzWith L g ∧ IsCompact K ∧ S ∩ W ⊆ g '' K := by
  obtain ⟨U, R, Ω, f, hU, hxU, hΩ, hf, hSU⟩ := h.2 x hx
  have hxR : x ∈ U ∩ R '' (graphMap f '' Ω) := hSU ▸ ⟨hx, hxU⟩
  obtain ⟨_, ⟨_, ⟨p, hpΩ, rfl⟩, rfl⟩⟩ := hxR
  obtain ⟨C, t, ht, hCt⟩ := (hf.contDiffAt (hΩ.mem_nhds hpΩ)).exists_lipschitzOnWith
  obtain ⟨r, hr, hrsub⟩ :=
    (nhds_basis_closedBall (x := p)).mem_iff.mp (Filter.inter_mem ht (hΩ.mem_nhds hpΩ))
  obtain ⟨g, hg, hfg⟩ := (hCt.mono fun y hy => (hrsub hy).1).extend_real
  refine ⟨U ∩ ball (R (graphMap f p)) r, hU.inter isOpen_ball, ⟨hxU, mem_ball_self hr⟩,
    fun q => R (graphMap g q), 1 * (1 + C), closedBall p r,
    R.isometry.lipschitzWith.comp (lipschitzWith_graphMap hg), isCompact_closedBall p r, ?_⟩
  rintro y ⟨hyS, hyU, hyB⟩
  have hyR : y ∈ U ∩ R '' (graphMap f '' Ω) := hSU ▸ ⟨hyS, hyU⟩
  obtain ⟨_, ⟨_, ⟨q, _, rfl⟩, rfl⟩⟩ := hyR
  have hqp : dist q p ≤ r := by
    have h1 := (antilipschitzWith_graphMap f).le_mul_dist q p
    rw [mem_ball, R.dist_map] at hyB
    simp only [NNReal.coe_one, one_mul] at h1
    linarith
  refine ⟨q, mem_closedBall.mpr hqp, ?_⟩
  have hq : f q = g q := hfg (mem_closedBall.mpr hqp)
  simp only [graphMap, hq]

/-- A compact embedded C¹ surface is covered by finitely many global Lipschitz
images of compact planar sets. -/
lemma IsCompactC1EmbeddedSurface.exists_finite_lipschitz_cover
    {S : Set (EuclideanSpace ℝ (Fin 3))} (h : IsCompactC1EmbeddedSurface S) :
    ∃ (ι : Type) (_ : Fintype ι)
      (g : ι → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (L : ι → ℝ≥0)
      (K : ι → Set (EuclideanSpace ℝ (Fin 2))),
      (∀ i, LipschitzWith (L i) (g i)) ∧ (∀ i, IsCompact (K i)) ∧ S ⊆ ⋃ i, g i '' K i := by
  classical
  have hloc := fun x (hx : x ∈ S) => h.exists_local_lipschitz_chart hx
  choose W hWo hxW g L K hg hK hsub using hloc
  obtain ⟨t, ht⟩ := h.1.elim_nhds_subcover' W fun x hx => (hWo x hx).mem_nhds (hxW x hx)
  refine ⟨t, inferInstance, fun i => g i.1.1 i.1.2, fun i => L i.1.1 i.1.2,
    fun i => K i.1.1 i.1.2, fun i => hg _ _, fun i => hK _ _, ?_⟩
  intro y hy
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (ht hy)
  exact mem_iUnion.mpr ⟨⟨i, hi⟩, hsub i.1 i.2 ⟨hy, hyi⟩⟩

/-- A compact embedded C¹ surface is countably `H²`-rectifiable. -/
theorem IsCompactC1EmbeddedSurface.countablyH2Rectifiable
    {S : Set (EuclideanSpace ℝ (Fin 3))} (h : IsCompactC1EmbeddedSurface S) :
    CountablyH2Rectifiable S := by
  classical
  obtain ⟨ι, _, g, L, K, hg, _, hcover⟩ := h.exists_finite_lipschitz_cover
  obtain ⟨e, he⟩ := exists_surjective_nat (Option ι)
  refine ⟨h.1.isClosed.measurableSet.nullMeasurableSet,
    fun j => (e j).elim (fun _ => 0) g, fun j => (e j).elim 0 L, ?_, ?_⟩
  · intro j
    show LipschitzWith ((e j).elim 0 L) ((e j).elim (fun _ => 0) g)
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
    show y ∈ range ((e j).elim (fun _ => 0) g)
    rw [hj]
    exact image_subset_range _ _ hi

/-- A compact embedded C¹ surface has finite normalized two-dimensional
Hausdorff measure. -/
theorem IsCompactC1EmbeddedSurface.hausdorffMeasure2_lt_top
    {S : Set (EuclideanSpace ℝ (Fin 3))} (h : IsCompactC1EmbeddedSurface S) :
    hausdorffMeasure2 3 S < ⊤ := by
  classical
  obtain ⟨ι, _, g, L, K, hg, hK, hcover⟩ := h.exists_finite_lipschitz_cover
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
