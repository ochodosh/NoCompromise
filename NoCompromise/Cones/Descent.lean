module

public import NoCompromise.Regularity.OmegaMinimal
public import NoCompromise.BV.CoareaCoordinates

@[expose] public section

/-!
# Descent for vertical cylinders

`verticalCylinder L` is exactly the product of the planar set `L` with the
third coordinate axis: a point belongs to it precisely when its first two
coordinates belong to `L`.  The coordinate map is `graphProjectionN 2`.

The descent theorem requires a BV product identity and is not asserted here.
The lemmas below establish the exact geometry and measurability of its slab
competitor without additional assumptions on `L`.
-/

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal symmDiff

namespace LiquidDrop

/-- The product of a planar set with the entire third coordinate axis. -/
def verticalCylinder (L : Set (EuclideanSpace ℝ (Fin 2))) : Set AmbientSpace :=
  (graphProjectionN 2) ⁻¹' L

@[simp] lemma mem_verticalCylinder {L : Set (EuclideanSpace ℝ (Fin 2))}
    {x : AmbientSpace} : x ∈ verticalCylinder L ↔ graphProjectionN 2 x ∈ L := Iff.rfl

@[simp] lemma verticalCylinder_append (L : Set (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    graphAppendN p t ∈ verticalCylinder L ↔ p ∈ L := by
  simp [verticalCylinder]

lemma measurableSet_verticalCylinder {L : Set (EuclideanSpace ℝ (Fin 2))}
    (hL : MeasurableSet L) : MeasurableSet (verticalCylinder L) :=
  (graphProjectionN 2).measurable hL

@[simp] lemma verticalCylinder_inter (A L : Set (EuclideanSpace ℝ (Fin 2))) :
    verticalCylinder (A ∩ L) = verticalCylinder A ∩ verticalCylinder L :=
  preimage_inter

@[simp] lemma verticalCylinder_union (A L : Set (EuclideanSpace ℝ (Fin 2))) :
    verticalCylinder (A ∪ L) = verticalCylinder A ∪ verticalCylinder L :=
  preimage_union

@[simp] lemma verticalCylinder_symmDiff (A L : Set (EuclideanSpace ℝ (Fin 2))) :
    verticalCylinder (A ∆ L) = verticalCylinder A ∆ verticalCylinder L := by
  ext x
  simp [Set.symmDiff_def, verticalCylinder]

@[simp] private lemma graphAppendN_height_for_descent
    (p : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    graphAppendN p t (2 : Fin 3) = t := by
  simpa only [show Fin.last 2 = (2 : Fin 3) from rfl] using graphAppendN_last p t

/-- Replace the planar factor inside the open vertical slab of half-height `T`. -/
def slabCompetitor (L A : Set (EuclideanSpace ℝ (Fin 2))) (T : ℝ) :
    Set AmbientSpace :=
  {x | if |x 2| < T then graphProjectionN 2 x ∈ A else graphProjectionN 2 x ∈ L}

lemma slabCompetitor_mem_iff {L A : Set (EuclideanSpace ℝ (Fin 2))}
    {T : ℝ} {x : AmbientSpace} :
    x ∈ slabCompetitor L A T ↔
      (|x 2| < T ∧ graphProjectionN 2 x ∈ A) ∨
      (T ≤ |x 2| ∧ graphProjectionN 2 x ∈ L) := by
  simp only [slabCompetitor, mem_ofPred_eq]
  split_ifs with h
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

lemma measurableSet_slabCompetitor {L A : Set (EuclideanSpace ℝ (Fin 2))}
    (hL : MeasurableSet L) (hA : MeasurableSet A) (T : ℝ) :
    MeasurableSet (slabCompetitor L A T) := by
  have hh : MeasurableSet {x : AmbientSpace | |x 2| < T} :=
    (isOpen_lt (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).continuous.abs
      continuous_const).measurableSet
  rw [show slabCompetitor L A T =
      ({x : AmbientSpace | |x 2| < T} ∩ verticalCylinder A) ∪
      ({x : AmbientSpace | T ≤ |x 2|} ∩ verticalCylinder L) from by
        ext x; simp only [slabCompetitor_mem_iff, mem_union, mem_inter_iff,
          mem_ofPred_eq, mem_verticalCylinder]]
  have hhOuter : MeasurableSet {x : AmbientSpace | T ≤ |x 2|} :=
    (isClosed_le continuous_const
      (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).continuous.abs).measurableSet
  exact (hh.inter (measurableSet_verticalCylinder hA)).union
    (hhOuter.inter (measurableSet_verticalCylinder hL))

lemma slabCompetitor_symmDiff (L A : Set (EuclideanSpace ℝ (Fin 2))) (T : ℝ) :
    slabCompetitor L A T ∆ verticalCylinder L =
      {x : AmbientSpace | |x 2| < T ∧ graphProjectionN 2 x ∈ A ∆ L} := by
  ext x
  by_cases h : |x 2| < T
  · simp [slabCompetitor, h, Set.symmDiff_def, verticalCylinder]
  · simp [slabCompetitor, h, Set.symmDiff_def, verticalCylinder]

/-- Compact support in the base produces compact support for the slab change. -/
lemma slabCompetitor_compact_change {L A : Set (EuclideanSpace ℝ (Fin 2))}
    (hbase : IsCompact (closure (A ∆ L))) (T : ℝ) :
    IsCompact (closure (slabCompetitor L A T ∆ verticalCylinder L)) := by
  let K : Set (ℝ × EuclideanSpace ℝ (Fin 2)) :=
    Set.Icc (-T) T ×ˢ closure (A ∆ L)
  have hK : IsCompact ((euclideanLastEquiv 2).symm '' K) :=
    (isCompact_Icc.prod hbase).image (euclideanLastEquiv 2).symm.continuous
  have hsub : slabCompetitor L A T ∆ verticalCylinder L ⊆
      (euclideanLastEquiv 2).symm '' K := by
    intro x hx
    rw [slabCompetitor_symmDiff] at hx
    obtain ⟨ht, hb⟩ := hx
    refine ⟨(x 2, graphProjectionN 2 x), ?_, ?_⟩
    · exact ⟨(abs_le.mp ht.le), subset_closure hb⟩
    · simpa only [euclideanLastEquiv_symm_apply,
        show Fin.last 2 = (2 : Fin 3) from rfl] using (graphAppendN_projection x)
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

/-- Local minimality compares the cylinder with a BV slab competitor on some
ball enclosing the entire change. -/
lemma cylinder_le_slabCompetitor_on_ball
    {L A : Set (EuclideanSpace ℝ (Fin 2))}
    (hL : MeasurableSet L) (hA : MeasurableSet A)
    (hT : IsLocallyPerimeterMinimizing (verticalCylinder L))
    (hbase : IsCompact (closure (A ∆ L))) (T : ℝ)
    (hF : HasLocallyFinitePerimeter (slabCompetitor L A T)) :
    ∃ r : ℝ, 0 < r ∧
      closure (slabCompetitor L A T ∆ verticalCylinder L) ⊆ ball (0 : AmbientSpace) r ∧
      perimeterIn (verticalCylinder L) (ball 0 r) ≤
        perimeterIn (slabCompetitor L A T) (ball 0 r) := by
  have hc := slabCompetitor_compact_change hbase T
  obtain ⟨r, hr, hsub⟩ := hc.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  refine ⟨r, hr, hsub, ?_⟩
  have hmF : NullMeasurableSet (slabCompetitor L A T) volume :=
    (measurableSet_slabCompetitor hL hA T).nullMeasurableSet
  have h := (hT r hr).comparison 0 r hr le_rfl
    (slabCompetitor L A T) hmF hF hc hsub
  simpa using h

@[simp] lemma slabCompetitor_append_inner {L A : Set (EuclideanSpace ℝ (Fin 2))}
    {T t : ℝ} (p : EuclideanSpace ℝ (Fin 2)) (ht : |t| < T) :
    graphAppendN p t ∈ slabCompetitor L A T ↔ p ∈ A := by
  simp [slabCompetitor, ht, graphAppendN_height_for_descent]

@[simp] lemma slabCompetitor_append_outer {L A : Set (EuclideanSpace ℝ (Fin 2))}
    {T t : ℝ} (p : EuclideanSpace ℝ (Fin 2)) (ht : T ≤ |t|) :
    graphAppendN p t ∈ slabCompetitor L A T ↔ p ∈ L := by
  simp [slabCompetitor, not_lt.mpr ht, graphAppendN_height_for_descent]

set_option maxSynthPendingDepth 8

/-- Lift a horizontal test field, with a scalar cutoff in the last coordinate. -/
def cylinderTestField {k : ℕ}
    (X : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) (η : ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin (k + 1))) : EuclideanSpace ℝ (Fin (k + 1)) :=
  η (z (Fin.last k)) • graphBaseN k (X (graphProjectionN k z))

lemma divergenceN_cylinderTestField {k : ℕ}
    {X : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)} {η : ℝ → ℝ}
    (hX : ContDiff ℝ 1 X) (hη : ContDiff ℝ 1 η)
    (z : EuclideanSpace ℝ (Fin (k + 1))) :
    divergenceN (cylinderTestField X η) z =
      η (z (Fin.last k)) * divergenceN X (graphProjectionN k z) := by
  have h1 := hη.differentiable one_ne_zero
  have h2 := hX.differentiable one_ne_zero
  have hp (i : Fin k) :
      graphProjectionN k (EuclideanSpace.single i.castSucc 1) =
        EuclideanSpace.single i 1 := by
    ext j
    simp [Fin.castSucc_inj]
  have hpLast : graphProjectionN k (EuclideanSpace.single (Fin.last k) 1) = 0 := by
    ext j
    simp
  have hd := ((h1 _).hasFDerivAt.comp z
      (EuclideanSpace.proj (Fin.last k)).hasFDerivAt).smul
    ((graphBaseN k).hasFDerivAt.comp z
      ((h2 _).hasFDerivAt.comp z (graphProjectionN k).hasFDerivAt))
  have he : fderiv ℝ (cylinderTestField X η) z =
      η (z (Fin.last k)) •
          (graphBaseN k).comp ((fderiv ℝ X (graphProjectionN k z)).comp (graphProjectionN k)) +
        ((fderiv ℝ η (z (Fin.last k))).comp (EuclideanSpace.proj (Fin.last k))).smulRight
          (graphBaseN k (X (graphProjectionN k z))) := by
    change fderiv ℝ
      (fun w : EuclideanSpace ℝ (Fin (k + 1)) =>
        η (w (Fin.last k)) • graphBaseN k (X (graphProjectionN k w))) z = _
    simpa only [Pi.smul_def', Function.comp_def, EuclideanSpace.coe_proj] using hd.fderiv
  unfold divergenceN
  rw [he]
  simp only [add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.comp_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_castSucc]
  simp [hp, hpLast, Finset.mul_sum]

lemma tsupport_cylinderTestField_subset {k : ℕ}
    (X : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) (η : ℝ → ℝ) :
    tsupport (cylinderTestField X η) ⊆
      (euclideanLastEquiv k) ⁻¹' (tsupport η ×ˢ tsupport X) := by
  apply closure_minimal
  · intro z hz
    constructor
    · apply subset_closure
      intro he
      simp only [euclideanLastEquiv_apply] at he
      exact hz (by simp [cylinderTestField, he])
    · apply subset_closure
      intro he
      simp only [euclideanLastEquiv_apply] at he
      exact hz (by simp [cylinderTestField, he])
  · exact ((isClosed_tsupport η).prod (isClosed_tsupport X)).preimage
      (euclideanLastEquiv k).continuous

lemma hasCompactSupport_cylinderTestField {k : ℕ}
    {X : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)} {η : ℝ → ℝ}
    (hX : HasCompactSupport X) (hη : HasCompactSupport η) :
    HasCompactSupport (cylinderTestField X η) := by
  apply ((euclideanLastEquiv k).toHomeomorph.isCompact_preimage.mpr (hη.prod hX)).of_isClosed_subset
    (isClosed_tsupport _)
  exact tsupport_cylinderTestField_subset X η

lemma norm_graphBaseN_for_descent {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    ‖graphBaseN k x‖ = ‖x‖ := by
  have h : ‖graphBaseN k x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  nlinarith [norm_nonneg (graphBaseN k x), norm_nonneg x]

lemma isVariationTestField_cylinderTestField {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin k))} {I : Set ℝ}
    {X : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)} {η : ℝ → ℝ}
    (hX : IsVariationTestField U X) (hη : ContDiff ℝ 1 η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ I)
    (hbη : ∀ t, |η t| ≤ 1) :
    IsVariationTestField ((euclideanLastEquiv k) ⁻¹' (I ×ˢ U))
      (cylinderTestField X η) := by
  have hηproj : ContDiff ℝ 1
      (fun z : EuclideanSpace ℝ (Fin (k + 1)) => η (z (Fin.last k))) := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (hη.comp (EuclideanSpace.proj (Fin.last k)).contDiff)
  refine ⟨hηproj.smul
    ((graphBaseN k).contDiff.comp (hX.1.comp (graphProjectionN k).contDiff)),
    hasCompactSupport_cylinderTestField hX.2.1 hcη, ?_, ?_⟩
  · intro z hz
    obtain ⟨ht, hx⟩ := tsupport_cylinderTestField_subset X η hz
    exact ⟨hsη ht, hX.2.2.1 hx⟩
  · intro z
    simp only [cylinderTestField, norm_smul, Real.norm_eq_abs, norm_graphBaseN_for_descent]
    exact (mul_le_mul (hbη _) (hX.2.2.2 _) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)

/-- Fubini pairing for a horizontal product field. -/
lemma integral_cylinderTestField {L : Set (EuclideanSpace ℝ (Fin 2))}
    {X : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} {η : ℝ → ℝ}
    (hX : ContDiff ℝ 1 X) (hη : ContDiff ℝ 1 η) :
    (∫ z, (verticalCylinder L).indicator (fun _ => (1 : ℝ)) z *
      divergenceN (cylinderTestField X η) z) =
      (∫ t, η t) * ∫ x, L.indicator (fun _ => (1 : ℝ)) x * divergenceN X x := by
  let e := (euclideanLastEquiv 2).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e volume (volume.prod volume) :=
    euclideanLastEquiv_measurePreserving 2
  rw [← (MeasurePreserving.symm e he).integral_comp e.symm.measurableEmbedding]
  have hfun : (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
      (verticalCylinder L).indicator (fun _ => (1 : ℝ)) (e.symm p) *
        divergenceN (cylinderTestField X η) (e.symm p)) =
      (fun p => η p.1 * (L.indicator (fun _ => (1 : ℝ)) p.2 * divergenceN X p.2)) := by
    funext p
    rw [divergenceN_cylinderTestField hX hη]
    change (verticalCylinder L).indicator (fun _ => (1 : ℝ)) (graphAppendN p.2 p.1) *
      (η ((graphAppendN p.2 p.1) (Fin.last 2)) *
        divergenceN X (graphProjectionN 2 (graphAppendN p.2 p.1))) = _
    by_cases hp : p.2 ∈ L <;> simp [hp, verticalCylinder]
  rw [hfun]
  exact integral_prod_mul η (fun x => L.indicator (fun _ => (1 : ℝ)) x * divergenceN X x)

/-- A cutoff-weighted lower product bound; no finiteness assumption is needed. -/
theorem perimeterIn_cylinder_lower_cutoff
    {L U : Set (EuclideanSpace ℝ (Fin 2))} {I : Set ℝ} {η : ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ I)
    (hbη : ∀ t, |η t| ≤ 1) (hiη : 0 ≤ ∫ t, η t) :
    ENNReal.ofReal (∫ t, η t) * perimeterIn L U ≤
      perimeterIn (verticalCylinder L) ((euclideanLastEquiv 2) ⁻¹' (I ×ˢ U)) := by
  unfold perimeterIn variation
  simp only [ENNReal.mul_iSup]
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have ht := isVariationTestField_cylinderTestField hX hη hcη hsη hbη
  have heq {n : ℕ} {V : Set (EuclideanSpace ℝ (Fin n))}
      (f : EuclideanSpace ℝ (Fin n) → ℝ)
      {Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
      (hY : IsVariationTestField V Y) :
      (∫ z, f z * divergenceN Y z) = ∫ z in V, f z * divergenceN Y z := by
    rw [← setIntegral_univ (f := fun z => f z * divergenceN Y z)]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ V)
    intro z hz
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hz.2 (hY.2.2.1 h)), mul_zero]
  have hp := integral_cylinderTestField (L := L) hX.1 hη
  rw [heq _ ht, heq _ hX] at hp
  rw [← ENNReal.ofReal_mul hiη, ← hp]
  exact le_iSup_of_le (cylinderTestField X η) (le_iSup_of_le ht le_rfl)

/-- The full lower product bound on an open vertical interval. -/
theorem perimeterIn_verticalCylinder_lower
    (L U : Set (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a < b) :
    ENNReal.ofReal (b - a) * perimeterIn L U ≤
      perimeterIn (verticalCylinder L) ((euclideanLastEquiv 2) ⁻¹' (Ioo a b ×ˢ U)) := by
  apply ENNReal.mul_le_of_forall_lt
  intro c hc d hd
  have hcfin : c ≠ ∞ := (hc.trans_le (le_of_lt ENNReal.ofReal_lt_top)).ne
  have hcr : c.toReal < b - a := ENNReal.toReal_lt_of_lt_ofReal hc
  have hlen : 0 < b - a := sub_pos.mpr hab
  let η : ContDiffBump ((a + b) / 2) :=
    ⟨(c.toReal + (b - a)) / 4, (c.toReal + 3 * (b - a)) / 8,
      by positivity, by linarith⟩
  have hs : tsupport η ⊆ Ioo a b := by
    rw [η.tsupport_eq]
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at ht
    have hr : η.rOut < (b - a) / 2 := by dsimp [η]; linarith
    dsimp [η] at ht hr
    constructor <;> linarith [ht.1, ht.2]
  have hi : c.toReal ≤ ∫ t, η t := by
    have h := η.measure_closedBall_le_integral volume
    rw [Real.volume_real_closedBall η.rIn_pos.le] at h
    dsimp [η] at h
    linarith
  have hci : c ≤ ENNReal.ofReal (∫ t, η t) := by
    rw [← ENNReal.ofReal_toReal hcfin]
    exact ENNReal.ofReal_le_ofReal hi
  exact (mul_le_mul' hci hd.le).trans
    (perimeterIn_cylinder_lower_cutoff η.contDiff η.hasCompactSupport hs
      (fun t => by rw [abs_of_nonneg η.nonneg]; exact η.le_one) η.integral_pos.le)

/-- Local finite perimeter descends from a vertical cylinder, independently of minimality. -/
theorem hasLocallyFinitePerimeter_of_verticalCylinder
    {L : Set (EuclideanSpace ℝ (Fin 2))}
    (hT : HasLocallyFinitePerimeter (verticalCylinder L)) :
    HasLocallyFinitePerimeter L := by
  intro U hU hcU
  let V := (euclideanLastEquiv 2) ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ U)
  have hoV : IsOpen V := (isOpen_Ioo.prod hU).preimage (euclideanLastEquiv 2).continuous
  have hcV : IsCompact (closure V) := by
    have hK : IsCompact ((euclideanLastEquiv 2) ⁻¹'
        (Icc (0 : ℝ) 1 ×ˢ closure U)) :=
      (euclideanLastEquiv 2).toHomeomorph.isCompact_preimage.mpr
        (isCompact_Icc.prod hcU)
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal
    · intro z hz
      exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, subset_closure hz.2⟩
    · exact ((isClosed_Icc.prod isClosed_closure).preimage
        (euclideanLastEquiv 2).continuous)
  have h : perimeterIn L U ≤ perimeterIn (verticalCylinder L) V := by
    simpa [V] using perimeterIn_verticalCylinder_lower L U (a := 0) (b := 1) zero_lt_one
  exact h.trans_lt (hT V hoV hcV)

/-- In particular, the cylinder minimality hypothesis supplies the base's BV regularity. -/
theorem locallyFinite_of_minimizing_verticalCylinder
    {L : Set (EuclideanSpace ℝ (Fin 2))}
    (hT : IsLocallyPerimeterMinimizing (verticalCylinder L)) :
    HasLocallyFinitePerimeter L :=
  hasLocallyFinitePerimeter_of_verticalCylinder (hT 1 (by norm_num)).locallyFinite

/-- The limiting step of `lem:cone-descent`: if for every `T₀ > 1` the product comparison gives
`0 ≤ 2 T₀ (a - l) + 2 c` (horizontal cost `c = |A ∆ L|`, independent of `T₀`, with the literal
factor two of `eq:product-perimeter`), then `l ≤ a`. -/
lemma cone_descent_real_comparison {a l c : ℝ}
    (h : ∀ t : ℝ, 1 < t → 0 ≤ 2 * t * (a - l) + 2 * c) : l ≤ a := by
  by_contra hn
  have hd : 0 < l - a := sub_pos.mpr (lt_of_not_ge hn)
  have ht : 1 < (|c| + 1) / (l - a) + 2 := by
    have : 0 ≤ (|c| + 1) / (l - a) := by positivity
    linarith
  have hh := h ((|c| + 1) / (l - a) + 2) ht
  have he : (|c| + 1) / (l - a) * (l - a) = |c| + 1 :=
    div_mul_cancel₀ _ hd.ne'
  nlinarith [le_abs_self c]

end LiquidDrop

