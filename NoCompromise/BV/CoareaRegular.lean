import NoCompromise.BV.CoareaLocal
import NoCompromise.BV.CoareaIsometry
import Mathlib.Topology.Compactness.Lindelof

/-!
# The regular contribution to weighted C¹ coarea

Coordinate permutations and genuine inverse-function charts give local weighted
identities. A countable open subcover is disjointified into Borel patches; Tonelli
sums the actual Hausdorff level integrals. No coarea theorem is assumed.
-/

noncomputable section
open MeasureTheory Set Filter Function InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma ScalarCoareaChart.hasWeightedCoareaOn {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (d : ScalarCoareaChart u)
    {A : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hA : MeasurableSet A)
    (hAs : A ⊆ d.chart.source) : HasWeightedCoareaOn u A := by
  intro g hg
  simpa only [Nat.add_sub_cancel_right] using
    And.intro (d.measurable_lintegral_level hA hAs hg).aemeasurable
      (d.weighted_coarea hA hAs hg)

/-- Every regular point has an open neighborhood where coarea holds on every Borel subpatch. -/
lemma exists_regular_coarea_neighborhood {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {x : EuclideanSpace ℝ (Fin (k + 1))} (hx : x ∈ U) (hgrad : gradient u x ≠ 0) :
    ∃ V : Set (EuclideanSpace ℝ (Fin (k + 1))), IsOpen V ∧ x ∈ V ∧
      V ⊆ {z | z ∈ U ∧ gradient u z ≠ 0} ∧
      ∀ A, MeasurableSet A → A ⊆ V → HasWeightedCoareaOn u A := by
  have hux := (hu.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)
  obtain ⟨i, hi⟩ := exists_coareaSwap_nonzero_last hux hgrad
  let e := coareaSwap i
  have hUe : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hue : ContDiffOn ℝ 1 (u ∘ e) (e ⁻¹' U) :=
    hu.comp e.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hy => hy)
  have hxe : e.symm x ∈ e ⁻¹' U := by simpa using hx
  obtain ⟨d, hxd, hds⟩ := exists_scalarCoareaChart hUe hue hxe hi
  let V := e '' d.chart.source
  have hVU : V ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hds hy
  have hVR : V ⊆ {z | z ∈ U ∧ gradient u z ≠ 0} := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hds hy, ?_⟩
    have hdiff := (hu.differentiableOn (by norm_num) (e y) (hds hy)).differentiableAt
      (hU.mem_nhds (hds hy))
    have hn := d.last_ne_zero y hy
    rw [gradient_comp_coareaSwap_last i hdiff] at hn
    intro hz
    apply hn
    simpa only [PiLp.zero_apply] using congrArg (fun p => p i) hz
  refine ⟨V, e.toHomeomorph.isOpenMap _ d.chart.open_source,
    ⟨e.symm x, hxd, e.apply_symm_apply x⟩, hVR, ?_⟩
  intro A hA hAV
  have hpre : e ⁻¹' A ⊆ d.chart.source := by
    intro y hy
    obtain ⟨z, hz, heq⟩ := hAV hy
    exact e.injective heq ▸ hz
  exact HasWeightedCoareaOn.of_comp_linearIsometryEquiv e
    (d.hasWeightedCoareaOn (hA.preimage e.continuous.measurable) hpre) hA
    (fun y hy => (hu.differentiableOn (by norm_num) y (hVU (hAV hy))).differentiableAt
      (hU.mem_nhds (hVU (hAV hy))))

/-- A Borel patch on which the height is continuous has Borel scalar levels. -/
lemma measurableSet_coarea_level_of_continuousOn {n : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContinuousOn u A) (t : ℝ) :
    MeasurableSet (A ∩ u ⁻¹' {t}) := by
  classical
  let v := A.piecewise u (fun _ => 0)
  have hv : Measurable v := hu.measurable_piecewise continuousOn_const hA
  have heq : A ∩ u ⁻¹' {t} = A ∩ v ⁻¹' {t} := by
    ext x
    by_cases hx : x ∈ A <;> simp [v, hx]
  rw [heq]
  exact hA.inter (hv (measurableSet_singleton t))

lemma hasWeightedCoareaOn_empty {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    HasWeightedCoareaOn u ∅ := by
  intro g hg
  simp only [empty_inter, Measure.restrict_empty, lintegral_zero_measure,
    lintegral_const, zero_mul]
  exact ⟨aemeasurable_const, trivial⟩

/-- Coarea identities on disjoint Borel patches sum to the identity on their countable union. -/
lemma HasWeightedCoareaOn.iUnion {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {B : ℕ → Set (EuclideanSpace ℝ (Fin n))} (hB : ∀ j, MeasurableSet (B j))
    (huc : ∀ j, ContinuousOn u (B j)) (hd : Pairwise (Disjoint on B))
    (hco : ∀ j, HasWeightedCoareaOn u (B j)) : HasWeightedCoareaOn u (⋃ j, B j) := by
  intro g hg
  have hm (j) := (hco j g hg).1
  have he (j) := (hco j g hg).2
  have hlev (t : ℝ) :
      (∫⁻ x in (⋃ j, B j) ∩ u ⁻¹' {t},
        g x ∂Measure.euclideanHausdorffMeasure (n - 1)) =
        ∑' j, ∫⁻ x in B j ∩ u ⁻¹' {t},
          g x ∂Measure.euclideanHausdorffMeasure (n - 1) := by
    rw [iUnion_inter]
    exact lintegral_iUnion (fun j => measurableSet_coarea_level_of_continuousOn (hB j) (huc j) t)
      (fun i j hij => (hd hij).mono inter_subset_left inter_subset_left) g
  constructor
  · have heq := funext hlev
    rw [heq]
    exact AEMeasurable.tsum hm
  · rw [lintegral_iUnion hB hd]
    simp_rw [he, hlev]
    exact (lintegral_tsum hm).symm

/-- The regular locus is covered by countably many Borel patches with exact coarea. -/
theorem weighted_coarea_regular_succ {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hu : ContDiffOn ℝ 1 u U) :
    HasWeightedCoareaOn u {x | x ∈ U ∧ gradient u x ≠ 0} := by
  classical
  let R := {x | x ∈ U ∧ gradient u x ≠ 0}
  by_cases hR : R.Nonempty
  · let : Nonempty R := hR.to_subtype
    have hlocal (x : R) := exists_regular_coarea_neighborhood hU hu x.property.1 x.property.2
    choose V hVo hVx hVR hVco using hlocal
    have hL : IsLindelof R := isLindelof_iff_lindelofSpace.mpr inferInstance
    obtain ⟨c, hc⟩ := hL.indexed_countable_subcover V hVo
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩)
    let B := disjointed (fun j => V (c j))
    have hB (j) : MeasurableSet (B j) := MeasurableSet.disjointed
      (fun i => (hVo (c i)).measurableSet) j
    have hBV (j) : B j ⊆ V (c j) := disjointed_subset _ _
    have hBR (j) : B j ⊆ R := (hBV j).trans (hVR (c j))
    have hBU (j) : B j ⊆ U := fun x hx => (hBR j hx).1
    have hco (j) : HasWeightedCoareaOn u (B j) := hVco (c j) (B j) (hB j) (hBV j)
    have hUnion : (⋃ j, B j) = R := by
      rw [iUnion_disjointed]
      exact Subset.antisymm (iUnion_subset fun j => hVR (c j)) hc
    change HasWeightedCoareaOn u R
    rw [← hUnion]
    exact HasWeightedCoareaOn.iUnion hB (fun j => hu.continuousOn.mono (hBU j))
      (disjoint_disjointed _) hco
  · have hz : R = ∅ := not_nonempty_iff_eq_empty.mp hR
    change HasWeightedCoareaOn u R
    rw [hz]
    exact hasWeightedCoareaOn_empty u

/-- Blueprint `lem:coarea-regular-part`, in every requested ambient dimension. -/
theorem coarea_regular_part {n : ℕ} (hn : 2 ≤ n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U) :
    HasWeightedCoareaOn u {x | x ∈ U ∧ gradient u x ≠ 0} := by
  cases n with
  | zero => omega
  | succ k => exact weighted_coarea_regular_succ hU hu

end LiquidDrop
