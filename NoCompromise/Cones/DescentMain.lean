import NoCompromise.Cones.Descent

/-!
# Descent of cylinder minimality

Horizontal slicing and the fundamental theorem of calculus give the slab
upper perimeter estimate. Locality of perimeter measures transfers ball
comparisons to prisms, and sending the slab height to infinity proves descent.
Null measurability is sufficient throughout.
-/

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal symmDiff

namespace LiquidDrop

/-- The horizontal component of an ambient vector field at a fixed height. -/
def descentHorizontalSlice (Y : AmbientSpace → AmbientSpace) (t : ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  graphProjectionN 2 (Y (graphAppendN p t))

/-- Horizontal projection does not increase the Euclidean norm. -/
lemma norm_graphProjectionN_le_for_descent {k : ℕ}
    (z : EuclideanSpace ℝ (Fin (k + 1))) : ‖graphProjectionN k z‖ ≤ ‖z‖ := by
  have h := norm_sq_graphProjectionN z
  nlinarith [sq_nonneg (z (Fin.last k)), norm_nonneg z,
    norm_nonneg (graphProjectionN k z)]

/-- A slice's support lies over the ambient support at the specified height. -/
lemma tsupport_descentHorizontalSlice_subset (Y : AmbientSpace → AmbientSpace) (t : ℝ) :
    tsupport (descentHorizontalSlice Y t) ⊆
      (fun p => graphAppendN p t) ⁻¹' tsupport Y := by
  apply closure_minimal
  · intro p hp
    apply subset_closure
    intro heq
    exact hp (by simp [descentHorizontalSlice, heq])
  · exact (isClosed_tsupport Y).preimage (contDiff_graphAppendN (r := 1) t).continuous

/-- The horizontal slice of an admissible prism field is an admissible planar field. -/
lemma isVariationTestField_descentHorizontalSlice
    {Y : AmbientSpace → AmbientSpace} {U : Set (EuclideanSpace ℝ (Fin 2))}
    {I : Set ℝ} (hY : IsVariationTestField ((euclideanLastEquiv 2) ⁻¹' (I ×ˢ U)) Y)
    (t : ℝ) : IsVariationTestField U (descentHorizontalSlice Y t) := by
  refine ⟨(graphProjectionN 2).contDiff.comp (hY.1.comp (contDiff_graphAppendN t)), ?_, ?_, ?_⟩
  · apply (hY.2.1.image (graphProjectionN 2).continuous).of_isClosed_subset
      (isClosed_tsupport _)
    intro p hp
    exact ⟨graphAppendN p t, tsupport_descentHorizontalSlice_subset Y t hp,
      graphProjectionN_append p t⟩
  · intro p hp
    have h := hY.2.2.1 (tsupport_descentHorizontalSlice_subset Y t hp)
    simpa only [mem_preimage, euclideanLastEquiv_apply, mem_prod,
      graphAppendN_last, graphProjectionN_append] using h.2
  · intro p
    exact (norm_graphProjectionN_le_for_descent _).trans (hY.2.2.2 _)

/-- Divergence of a horizontal slice is the sum of the first two ambient partials. -/
lemma divergenceN_descentHorizontalSlice
    {Y : AmbientSpace → AmbientSpace} (hY : ContDiff ℝ 1 Y)
    (p : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    divergenceN (descentHorizontalSlice Y t) p =
      ∑ i : Fin 2, fderiv ℝ Y (graphAppendN p t) (EuclideanSpace.single i.castSucc 1)
        i.castSucc := by
  have hd := (graphProjectionN 2).hasFDerivAt.comp p
    ((hY.differentiable one_ne_zero _).hasFDerivAt.comp p (hasFDerivAt_graphAppendN t p))
  have hb (i : Fin 2) : graphBaseN 2 (EuclideanSpace.single i 1) =
      EuclideanSpace.single i.castSucc 1 := by
    apply PiLp.ext
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [graphBaseN_last]
      have hne : Fin.last 2 ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
      simp only [PiLp.single_apply, ite_eq_right hne]
    · simp
  have hd' : fderiv ℝ (descentHorizontalSlice Y t) p =
      (graphProjectionN 2).comp ((fderiv ℝ Y (graphAppendN p t)).comp (graphBaseN 2)) :=
    hd.fderiv
  unfold divergenceN
  rw [hd']
  simp only [ContinuousLinearMap.comp_apply, hb, graphProjectionN_apply]

/-- The last ambient partial is the ordinary derivative along a vertical line. -/
lemma deriv_descentVerticalSlice
    {Y : AmbientSpace → AmbientSpace} (hY : ContDiff ℝ 1 Y)
    (p : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    deriv (fun s => Y (graphAppendN p s) (2 : Fin 3)) t =
      fderiv ℝ Y (graphAppendN p t) (EuclideanSpace.single (2 : Fin 3) 1) (2 : Fin 3) := by
  have hline : HasDerivAt (fun s : ℝ => graphAppendN p s)
      (EuclideanSpace.single (2 : Fin 3) 1) t := by
    simpa only [graphAppendN, zero_add, Pi.add_apply, id_eq, one_smul] using!
      (hasDerivAt_const t (graphBaseN 2 p)).add
        ((hasDerivAt_id t).smul_const (EuclideanSpace.single (2 : Fin 3) 1))
  have hd := ((EuclideanSpace.proj (2 : Fin 3)).hasFDerivAt.comp (graphAppendN p t)
    (hY.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt t hline
  exact hd.deriv

/-- Divergence in a product chart splits into planar divergence and one vertical derivative. -/
lemma divergenceN_descent_split
    {Y : AmbientSpace → AmbientSpace} (hY : ContDiff ℝ 1 Y)
    (p : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    divergenceN Y (graphAppendN p t) =
      divergenceN (descentHorizontalSlice Y t) p +
        deriv (fun s => Y (graphAppendN p s) (2 : Fin 3)) t := by
  rw [divergenceN_descentHorizontalSlice hY, deriv_descentVerticalSlice hY]
  exact Fin.sum_univ_castSucc _

/-- The vertical contribution of a scalar slab profile is exactly its two face values.
The outer endpoint values vanish, as they do for a test field supported in the prism. -/
lemma integral_slab_profile_deriv {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {T b : ℝ} (hT : 0 < T) (hTb : T < b) (a l : ℝ)
    (hleft : φ (-b) = 0) (hright : φ b = 0) :
    (∫ t in Ioo (-b) b, (if |t| < T then a else l) * deriv φ t) =
      (a - l) * (φ T - φ (-T)) := by
  have hb : 0 < b := hT.trans hTb
  have hi : IntegrableOn (deriv φ) (Ioo (-b) b) :=
    hφ.continuous_deriv_one.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have heq : (fun t => (if |t| < T then a else l) * deriv φ t) =
      (fun t => l * deriv φ t +
        (a - l) * (Ioo (-T) T).indicator (deriv φ) t) := by
    funext t
    by_cases ht : |t| < T
    · have ht' : t ∈ Ioo (-T) T := abs_lt.mp ht
      rw [ite_eq_left ht, indicator_of_mem ht']
      ring
    · have ht' : t ∉ Ioo (-T) T := mt abs_lt.mpr ht
      rw [ite_eq_right ht, indicator_of_notMem ht', mul_zero, add_zero]
  rw [heq, integral_add (hi.const_mul l) ((hi.indicator measurableSet_Ioo).const_mul (a - l)),
    integral_const_mul, integral_const_mul, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (Ioo_subset_Ioo (neg_le_neg hTb.le) hTb.le)]
  have hlarge : (∫ t in Ioo (-b) b, deriv φ t) = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun t _ => hφ.differentiable one_ne_zero t)
      (hφ.continuous_deriv_one.intervalIntegrable _ _), hleft, hright, sub_self]
  have hsmall : (∫ t in Ioo (-T) T, deriv φ t) = φ T - φ (-T) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun t _ => hφ.differentiable one_ne_zero t)
      (hφ.continuous_deriv_one.intervalIntegrable _ _)
  rw [hlarge, hsmall, mul_zero, zero_add]

/-- Each horizontal slab slice is bounded by the appropriate planar perimeter.
The finiteness hypotheses are explicit because the bound is real valued. -/
lemma horizontal_slab_pairing_le
    {L A U : Set (EuclideanSpace ℝ (Fin 2))} {Y : AmbientSpace → AmbientSpace}
    {I : Set ℝ} {T : ℝ}
    (hY : IsVariationTestField ((euclideanLastEquiv 2) ⁻¹' (I ×ˢ U)) Y)
    (hA : perimeterIn A U ≠ ∞) (hL : perimeterIn L U ≠ ∞) (t : ℝ) :
    (∫ p, (slabCompetitor L A T).indicator (fun _ => (1 : ℝ)) (graphAppendN p t) *
      divergenceN (descentHorizontalSlice Y t) p) ≤
      if |t| < T then (perimeterIn A U).toReal else (perimeterIn L U).toReal := by
  have hs := isVariationTestField_descentHorizontalSlice hY t
  have hpair (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : perimeterIn E U ≠ ∞) :
      (∫ p, E.indicator (fun _ => (1 : ℝ)) p *
        divergenceN (descentHorizontalSlice Y t) p) ≤ (perimeterIn E U).toReal := by
    have h := abs_integral_mul_divergenceN_le_variation hE hs
    have heq : (∫ p, E.indicator (fun _ => (1 : ℝ)) p *
        divergenceN (descentHorizontalSlice Y t) p) =
        ∫ p in U, E.indicator (fun _ => (1 : ℝ)) p *
          divergenceN (descentHorizontalSlice Y t) p := by
      rw [← setIntegral_univ (f := fun p => E.indicator (fun _ => (1 : ℝ)) p *
        divergenceN (descentHorizontalSlice Y t) p)]
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ U)
      intro p hp
      rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hp.2 (hs.2.2.1 h)), mul_zero]
    rw [heq]
    exact (le_abs_self _).trans h
  by_cases ht : |t| < T
  · rw [ite_eq_left ht]
    convert hpair A hA using 1
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : p ∈ A <;> simp [slabCompetitor_append_inner p ht, hp]
  · rw [ite_eq_right ht]
    convert hpair L hL using 1
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : p ∈ L <;> simp [slabCompetitor_append_outer p (le_of_not_gt ht), hp]

/-- The vertical pairing at each base point costs at most twice the indicator of
the base change. This is the face term of the desired slab upper estimate. -/
lemma vertical_slab_pairing_le
    {L A U : Set (EuclideanSpace ℝ (Fin 2))} {Y : AmbientSpace → AmbientSpace}
    {T b : ℝ} (hT : 0 < T) (hTb : T < b)
    (hY : IsVariationTestField ((euclideanLastEquiv 2) ⁻¹' (Ioo (-b) b ×ˢ U)) Y)
    (p : EuclideanSpace ℝ (Fin 2)) :
    (∫ t in Ioo (-b) b,
      (slabCompetitor L A T).indicator (fun _ => (1 : ℝ)) (graphAppendN p t) *
        deriv (fun s => Y (graphAppendN p s) (2 : Fin 3)) t) ≤
      2 * ((A ∆ L) ∩ U).indicator (fun _ => (1 : ℝ)) p := by
  let φ : ℝ → ℝ := fun t => Y (graphAppendN p t) (2 : Fin 3)
  have hφ : ContDiff ℝ 1 φ :=
    (EuclideanSpace.proj (2 : Fin 3)).contDiff.comp (hY.1.comp
      (contDiff_const.add (contDiff_id.smul contDiff_const)))
  have hzero (t : ℝ) (ht : t ∉ Ioo (-b) b ∨ p ∉ U) : φ t = 0 := by
    have hn : graphAppendN p t ∉ tsupport Y := by
      intro hc
      have hh := hY.2.2.1 hc
      have hh' : t ∈ Ioo (-b) b ∧ p ∈ U := by
        simpa only [mem_preimage, euclideanLastEquiv_apply, mem_prod,
          graphAppendN_last, graphProjectionN_append] using hh
      rcases ht with ht | hp
      · exact ht hh'.1
      · exact hp hh'.2
    simp only [φ, image_eq_zero_of_notMem_tsupport hn, PiLp.zero_apply]
  have hleft : φ (-b) = 0 := hzero _ (Or.inl (by simp))
  have hright : φ b = 0 := hzero _ (Or.inl (by simp))
  have hfun : (fun t => (slabCompetitor L A T).indicator (fun _ => (1 : ℝ))
      (graphAppendN p t) * deriv φ t) =
      (fun t => (if |t| < T then A.indicator (fun _ => (1 : ℝ)) p
        else L.indicator (fun _ => (1 : ℝ)) p) * deriv φ t) := by
    funext t
    by_cases ht : |t| < T
    · by_cases hp : p ∈ A <;> simp [ht, slabCompetitor_append_inner p ht, hp]
    · by_cases hp : p ∈ L <;>
        simp [ht, slabCompetitor_append_outer p (le_of_not_gt ht), hp]
  change (∫ t in Ioo (-b) b, _ * deriv φ t) ≤ _
  rw [hfun, integral_slab_profile_deriv hφ hT hTb _ _ hleft hright]
  by_cases hpU : p ∈ U
  · have hnorm (t : ℝ) : |φ t| ≤ 1 :=
      (PiLp.norm_apply_le (Y (graphAppendN p t)) (2 : Fin 3)).trans (hY.2.2.2 _)
    have hpos := abs_le.mp (hnorm T)
    have hneg := abs_le.mp (hnorm (-T))
    by_cases hpA : p ∈ A <;> by_cases hpL : p ∈ L <;>
      simp [hpA, hpL, hpU, mem_symmDiff] <;> linarith
  · rw [hzero T (Or.inr hpU), hzero (-T) (Or.inr hpU), sub_self, mul_zero]
    simp [hpU]

/-- Integrating the horizontal slab weights gives the two interval lengths. -/
lemma integral_descent_slab_weights {T b : ℝ} (hT : 0 < T) (hTb : T < b) (a l : ℝ) :
    (∫ t in Ioo (-b) b, if |t| < T then a else l) =
      2 * T * a + 2 * (b - T) * l := by
  have heq : (fun t : ℝ => if |t| < T then a else l) =
      (fun t => l + (a - l) * (Ioo (-T) T).indicator (fun _ => (1 : ℝ)) t) := by
    funext t
    by_cases ht : t ∈ Ioo (-T) T
    · simp [abs_lt.mpr ht, ht]
    · simp [mt abs_lt.mp ht, ht]
  have hil : IntegrableOn (fun _ : ℝ => l) (Ioo (-b) b) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hi1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (-b) b) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  rw [heq, integral_add hil ((hi1.indicator measurableSet_Ioo).const_mul _),
    integral_const_mul, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (Ioo_subset_Ioo (neg_le_neg hTb.le) hTb.le)]
  rw [setIntegral_const, setIntegral_const,
    Real.volume_real_Ioo_of_le (by linarith), Real.volume_real_Ioo_of_le (by linarith)]
  simp only [smul_eq_mul]
  ring

/-- Null measurability of a vertical cylinder implies null measurability of its base. -/
lemma nullMeasurableSet_of_verticalCylinder
    {L : Set (EuclideanSpace ℝ (Fin 2))}
    (hL : NullMeasurableSet (verticalCylinder L) volume) :
    NullMeasurableSet L volume := by
  let e := (euclideanLastEquiv 2).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e volume (volume.prod volume) :=
    euclideanLastEquiv_measurePreserving 2
  have h := hL.preimage (MeasurePreserving.symm e he).quasiMeasurePreserving
  have heq : e.symm ⁻¹' verticalCylinder L = Prod.snd ⁻¹' L := by
    ext p
    exact verticalCylinder_append L p.2 p.1
  rw [heq] at h
  exact h.of_preimage_snd

/-- Null measurability is preserved by forming a vertical cylinder. -/
lemma nullMeasurableSet_verticalCylinder
    {L : Set (EuclideanSpace ℝ (Fin 2))} (hL : NullMeasurableSet L volume) :
    NullMeasurableSet (verticalCylinder L) volume := by
  have h := (Measure.nullMeasurableSet_preimage_snd (μ := (volume : Measure ℝ))).mpr hL
  exact h.preimage (euclideanLastEquiv_measurePreserving 2).quasiMeasurePreserving

/-- Slab competitors are null measurable even when neither base set is Borel measurable. -/
lemma nullMeasurableSet_slabCompetitor
    {L A : Set (EuclideanSpace ℝ (Fin 2))}
    (hL : NullMeasurableSet L volume) (hA : NullMeasurableSet A volume) (T : ℝ) :
    NullMeasurableSet (slabCompetitor L A T) volume := by
  have hh : MeasurableSet {x : AmbientSpace | |x 2| < T} :=
    (isOpen_lt (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).continuous.abs
      continuous_const).measurableSet
  have heq : slabCompetitor L A T =
      ({x : AmbientSpace | |x 2| < T} ∩ verticalCylinder A) ∪
      ({x : AmbientSpace | |x 2| < T}ᶜ ∩ verticalCylinder L) := by
    ext x
    simp only [slabCompetitor_mem_iff, mem_union, mem_inter_iff, mem_compl_iff,
      mem_ofPred_eq, mem_verticalCylinder, not_lt]
  rw [heq]
  exact (hh.nullMeasurableSet.inter (nullMeasurableSet_verticalCylinder hA)).union
    (hh.compl.nullMeasurableSet.inter (nullMeasurableSet_verticalCylinder hL))

/-- The slab competitor has the horizontal product cost and at most two faces.
This version assumes finite planar perimeters on the relatively compact open base. -/
theorem perimeterIn_slabCompetitor_upper
    {L A U : Set (EuclideanSpace ℝ (Fin 2))}
    (hmL : NullMeasurableSet L volume) (hmA : NullMeasurableSet A volume)
    (hU : IsOpen U) (hcU : IsCompact (closure U))
    (hA : perimeterIn A U < ∞) (hL : perimeterIn L U < ∞)
    {T b : ℝ} (hT : 0 < T) (hTb : T < b) :
    perimeterIn (slabCompetitor L A T) ((euclideanLastEquiv 2) ⁻¹' (Ioo (-b) b ×ˢ U)) ≤
      ENNReal.ofReal (2 * T) * perimeterIn A U +
        ENNReal.ofReal (2 * (b - T)) * perimeterIn L U + 2 * volume ((A ∆ L) ∩ U) := by
  classical
  let F := slabCompetitor L A T
  let I := Ioo (-b) b
  let Q := (euclideanLastEquiv 2) ⁻¹' (I ×ˢ U)
  let e := (euclideanLastEquiv 2).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e volume (volume.prod volume) :=
    euclideanLastEquiv_measurePreserving 2
  have hmF := nullMeasurableSet_slabCompetitor hmL hmA T
  have hvol : volume ((A ∆ L) ∩ U) < ∞ :=
    (measure_mono (inter_subset_right.trans subset_closure)).trans_lt hcU.measure_lt_top
  have hrhs : ENNReal.ofReal (2 * T) * perimeterIn A U +
        ENNReal.ofReal (2 * (b - T)) * perimeterIn L U + 2 * volume ((A ∆ L) ∩ U) ≠ ∞ := by
    finiteness
  unfold perimeterIn variation
  apply iSup_le
  intro Y
  apply iSup_le
  intro hY
  apply (ENNReal.ofReal_le_iff_le_toReal hrhs).mpr
  change (∫ z in Q, F.indicator (fun _ => (1 : ℝ)) z * divergenceN Y z) ≤ _
  let H := fun q : ℝ × EuclideanSpace ℝ (Fin 2) =>
    F.indicator (fun _ => (1 : ℝ)) (graphAppendN q.2 q.1) *
      divergenceN (descentHorizontalSlice Y q.1) q.2
  let V := fun q : ℝ × EuclideanSpace ℝ (Fin 2) =>
    F.indicator (fun _ => (1 : ℝ)) (graphAppendN q.2 q.1) *
      deriv (fun t => Y (graphAppendN q.2 t) (2 : Fin 3)) q.1
  have hcomponent (i j : Fin 3) : Integrable (fun z =>
      F.indicator (fun _ => (1 : ℝ)) z * fderiv ℝ Y z (EuclideanSpace.single i 1) j) :=
    integrable_mul_fderiv_component (locallyIntegrable_indicator_one hmF |>.locallyIntegrableOn Q)
      hY.1 hY.2.1 hY.2.2.1 i j
  have hH : Integrable H (volume.prod volume) := by
    have hi : Integrable (fun z => F.indicator (fun _ => (1 : ℝ)) z *
        ∑ i : Fin 2, fderiv ℝ Y z (EuclideanSpace.single i.castSucc 1) i.castSucc) := by
      simp only [Finset.mul_sum]
      exact integrable_finsetSum _ (fun i _ => hcomponent i.castSucc i.castSucc)
    have hh := (MeasurePreserving.symm e he).integrable_comp_of_integrable hi
    change Integrable (fun q : ℝ × EuclideanSpace ℝ (Fin 2) =>
      F.indicator (fun _ => (1 : ℝ)) (graphAppendN q.2 q.1) *
        ∑ i : Fin 2, fderiv ℝ Y (graphAppendN q.2 q.1)
          (EuclideanSpace.single i.castSucc 1) i.castSucc) _ at hh
    simpa only [Function.comp_def, H, divergenceN_descentHorizontalSlice hY.1] using hh
  have hV : Integrable V (volume.prod volume) := by
    have hh := (MeasurePreserving.symm e he).integrable_comp_of_integrable (hcomponent 2 2)
    change Integrable (fun q : ℝ × EuclideanSpace ℝ (Fin 2) =>
      F.indicator (fun _ => (1 : ℝ)) (graphAppendN q.2 q.1) *
        fderiv ℝ Y (graphAppendN q.2 q.1) (EuclideanSpace.single 2 1) 2) _ at hh
    simpa only [Function.comp_def, V, deriv_descentVerticalSlice hY.1] using hh
  have hHr : Integrable H ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hH.integrableOn
  have hVr : Integrable V ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hV.integrableOn
  have hsplit : (∫ z in Q, F.indicator (fun _ => (1 : ℝ)) z * divergenceN Y z) =
      (∫ t in I, ∫ p in U, H (t, p)) + (∫ p in U, ∫ t in I, V (t, p)) := by
    have hc := he.setIntegral_preimage_emb e.measurableEmbedding
      (fun q => F.indicator (fun _ => (1 : ℝ)) (e.symm q) * divergenceN Y (e.symm q)) (I ×ˢ U)
    simp only [e.symm_apply_apply] at hc
    change (∫ z in Q, F.indicator (fun _ => (1 : ℝ)) z * divergenceN Y z) =
      ∫ q in I ×ˢ U, F.indicator (fun _ => (1 : ℝ)) (e.symm q) *
        divergenceN Y (e.symm q) ∂volume.prod volume at hc
    rw [hc]
    have hf : (fun q => F.indicator (fun _ => (1 : ℝ)) (e.symm q) *
        divergenceN Y (e.symm q)) = (fun q => H q + V q) := by
      funext q
      exact congrArg (fun d => F.indicator (fun _ => (1 : ℝ)) (graphAppendN q.2 q.1) * d)
        (divergenceN_descent_split hY.1 q.2 q.1) |>.trans (mul_add _ _ _)
    rw [hf, integral_add hH.integrableOn hV.integrableOn,
      setIntegral_prod H hH.integrableOn, ← Measure.prod_restrict]
    rw [integral_prod_symm V hVr]
  have hiweight : IntegrableOn
      (fun t : ℝ => if |t| < T then (perimeterIn A U).toReal else (perimeterIn L U).toReal) I := by
    have hiA : IntegrableOn (fun _ : ℝ => (perimeterIn A U).toReal) I :=
      integrableOn_const (by simp [I, Real.volume_Ioo])
    have hiL : IntegrableOn (fun _ : ℝ => (perimeterIn L U).toReal) I :=
      integrableOn_const (by simp [I, Real.volume_Ioo])
    exact Integrable.piecewise (isOpen_lt continuous_abs continuous_const).measurableSet
      hiA.integrableOn hiL.integrableOn
  have hhor : (∫ t in I, ∫ p in U, H (t, p)) ≤
      2 * T * (perimeterIn A U).toReal + 2 * (b - T) * (perimeterIn L U).toReal := by
    rw [← integral_descent_slab_weights hT hTb]
    apply integral_mono hHr.integral_prod_left hiweight
    intro t
    dsimp only
    have heq : (∫ p in U, H (t, p)) = ∫ p, H (t, p) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hs := isVariationTestField_descentHorizontalSlice hY t
      dsimp [H]
      rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hp (hs.2.2.1 h)), mul_zero]
    rw [heq]
    exact horizontal_slab_pairing_le hY hA.ne hL.ne t
  have hmchange : NullMeasurableSet ((A ∆ L) ∩ U) volume :=
    (hmA.symmDiff hmL).inter hU.measurableSet.nullMeasurableSet
  have hic : Integrable (((A ∆ L) ∩ U).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const hvol.ne).integrable_indicator₀ hmchange
  have hver : (∫ p in U, ∫ t in I, V (t, p)) ≤ 2 * (volume ((A ∆ L) ∩ U)).toReal := by
    have hh := integral_mono hVr.integral_prod_right (hic.const_mul 2).integrableOn
      (fun p => vertical_slab_pairing_le hT hTb hY p)
    have heq : (∫ p in U, 2 * ((A ∆ L) ∩ U).indicator (fun _ => (1 : ℝ)) p) =
        2 * (volume ((A ∆ L) ∩ U)).toReal := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun p hp => by simp [hp]), integral_const_mul,
        integral_indicator₀ hmchange, setIntegral_const]
      simp [measureReal_def]
    exact hh.trans_eq heq
  rw [hsplit]
  have hh := add_le_add hhor hver
  apply hh.trans_eq
  symm
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * T),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (b - T)), ENNReal.toReal_ofNat]

/-- A null measurable competitor of a measurable set has a measurable representative
whose actual change is contained in the closure of the original change. -/
lemma exists_measurable_competitor
    {n : ℕ} {L A : Set (EuclideanSpace ℝ (Fin n))}
    (hL : MeasurableSet L) (hA : NullMeasurableSet A volume) :
    ∃ A' : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A' ∧
      A' =ᵐ[volume] A ∧ A' ∆ L ⊆ closure (A ∆ L) := by
  obtain ⟨M, hM, hAM⟩ := hA
  refine ⟨(M ∩ closure (A ∆ L)) ∪ (L \ closure (A ∆ L)),
    (hM.inter isClosed_closure.measurableSet).union
      (hL.diff isClosed_closure.measurableSet), ?_, ?_⟩
  · filter_upwards [hAM] with x hx
    change (x ∈ (M ∩ closure (A ∆ L)) ∪ (L \ closure (A ∆ L))) = (x ∈ A)
    have hx' : x ∈ A ↔ x ∈ M := Iff.of_eq hx
    by_cases hk : x ∈ closure (A ∆ L)
    · simp [hk, hx']
    · have hsame : x ∈ A ↔ x ∈ L := by
        have hn : x ∉ A ∆ L := fun h => hk (subset_closure h)
        simp only [mem_symmDiff] at hn
        tauto
      simp [hk, hsame]
  · intro x hx
    by_contra hk
    simp [mem_symmDiff, hk] at hx

/-- Perimeter comparisons on an open set can be localized to an open neighborhood
of the entire change, provided both original perimeter values are finite. -/
lemma perimeterIn_le_of_compact_change_localization
    {n : ℕ} {E F B Q : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) (hF : NullMeasurableSet F volume)
    (hB : IsOpen B) (hQ : IsOpen Q) (hQB : Q ⊆ B)
    (hchange : closure (E ∆ F) ⊆ Q)
    (hEB : perimeterIn E B < ∞) (hFB : perimeterIn F B < ∞)
    (hcomp : perimeterIn E B ≤ perimeterIn F B) :
    perimeterIn E Q ≤ perimeterIn F Q := by
  obtain ⟨μ, hμ⟩ := exists_perimeter_measure hE
  obtain ⟨ν, hν⟩ := exists_perimeter_measure hF
  let W := B \ closure (E ∆ F)
  have hW : IsOpen W := hB.sdiff isClosed_closure
  have hWB : W ⊆ B := sdiff_subset
  have hμW : μ W < ∞ := (measure_mono hWB).trans_lt (by rwa [← hμ B hB])
  have hνW : ν W < ∞ := (measure_mono hWB).trans_lt (by rwa [← hν B hB])
  let : IsFiniteMeasure (μ.restrict W) := ⟨by simpa using hμW⟩
  let : IsFiniteMeasure (ν.restrict W) := ⟨by simpa using hνW⟩
  have heq : μ.restrict W = ν.restrict W := by
    apply Measure.OuterRegular.ext_isOpen
    intro O hO
    rw [Measure.restrict_apply hO.measurableSet, Measure.restrict_apply hO.measurableSet,
      ← hμ (O ∩ W) (hO.inter hW), ← hν (O ∩ W) (hO.inter hW)]
    apply perimeterIn_congr_ae
    filter_upwards [ae_restrict_mem (hO.inter hW).measurableSet] with x hx
    have hn : x ∉ E ∆ F := fun hm => hx.2.2 (subset_closure hm)
    change (x ∈ E) = (x ∈ F)
    apply propext
    simp only [mem_symmDiff] at hn
    tauto
  have hdiffW : B \ Q ⊆ W := by
    intro x hx
    exact ⟨hx.1, fun hc => hx.2 (hchange hc)⟩
  have hdiff : μ (B \ Q) = ν (B \ Q) := by
    have h := congrArg (fun m : Measure (EuclideanSpace ℝ (Fin n)) => m (B \ Q)) heq
    simpa only [Measure.restrict_apply (hB.measurableSet.diff hQ.measurableSet),
      inter_eq_left.mpr hdiffW] using h
  rw [hμ B hB, hν B hB] at hcomp
  rw [← measure_sdiff_add_inter B hQ.measurableSet,
    ← measure_sdiff_add_inter B hQ.measurableSet, inter_eq_right.mpr hQB, hdiff] at hcomp
  rw [hμ Q hQ, hν Q hQ]
  exact (ENNReal.add_le_add_iff_left
    ((measure_mono sdiff_subset).trans_lt (by rwa [← hν B hB])).ne).mp hcomp

/-- Bounded vertical prisms over relatively compact bases have compact closure. -/
lemma isCompact_closure_descent_prism
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsCompact (closure U)) (b : ℝ) :
    IsCompact (closure ((euclideanLastEquiv 2) ⁻¹' (Ioo (-b) b ×ˢ U))) := by
  have hK : IsCompact ((euclideanLastEquiv 2) ⁻¹' (Icc (-b) b ×ˢ closure U)) :=
    (euclideanLastEquiv 2).toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod hU)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, subset_closure hz.2⟩
  · exact (isClosed_Icc.prod isClosed_closure).preimage (euclideanLastEquiv 2).continuous

/-- A slab change is compactly contained in any taller prism containing the base change. -/
lemma closure_slabCompetitor_change_subset_prism
    {L A U : Set (EuclideanSpace ℝ (Fin 2))} {T b : ℝ}
    (hbase : closure (A ∆ L) ⊆ U) (hTb : T < b) :
    closure (slabCompetitor L A T ∆ verticalCylinder L) ⊆
      (euclideanLastEquiv 2) ⁻¹' (Ioo (-b) b ×ˢ U) := by
  have hsub : slabCompetitor L A T ∆ verticalCylinder L ⊆
      (euclideanLastEquiv 2) ⁻¹' (Icc (-T) T ×ˢ closure (A ∆ L)) := by
    intro z hz
    rw [slabCompetitor_symmDiff] at hz
    exact ⟨abs_le.mp hz.1.le, subset_closure hz.2⟩
  have hc := closure_minimal hsub
    ((isClosed_Icc.prod isClosed_closure).preimage (euclideanLastEquiv 2).continuous)
  intro z hz
  obtain ⟨ht, hx⟩ := hc hz
  exact ⟨⟨lt_of_lt_of_le (neg_lt_neg hTb) ht.1, ht.2.trans_lt hTb⟩, hbase hx⟩

/-- A locally minimizing cylinder compares with a locally BV slab competitor directly
on a bounded open prism containing the full change. -/
lemma cylinder_le_slabCompetitor_on_prism
    {L A U : Set (EuclideanSpace ℝ (Fin 2))} {T b : ℝ}
    (hT : IsLocallyPerimeterMinimizing (verticalCylinder L))
    (hA : NullMeasurableSet A volume) (hU : IsOpen U)
    (hcU : IsCompact (closure U)) (hbase : IsCompact (closure (A ∆ L)))
    (hchange : closure (A ∆ L) ⊆ U) (hTb : T < b)
    (hF : HasLocallyFinitePerimeter (slabCompetitor L A T)) :
    perimeterIn (verticalCylinder L) ((euclideanLastEquiv 2) ⁻¹' (Ioo (-b) b ×ˢ U)) ≤
      perimeterIn (slabCompetitor L A T) ((euclideanLastEquiv 2) ⁻¹' (Ioo (-b) b ×ˢ U)) := by
  let Q := (euclideanLastEquiv 2) ⁻¹' (Ioo (-b) b ×ˢ U)
  have hQ : IsOpen Q := (isOpen_Ioo.prod hU).preimage (euclideanLastEquiv 2).continuous
  have hcQ : IsCompact (closure Q) := isCompact_closure_descent_prism hcU b
  obtain ⟨r, hr, hQB⟩ := hcQ.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  have hc : closure (slabCompetitor L A T ∆ verticalCylinder L) ⊆ Q :=
    closure_slabCompetitor_change_subset_prism hchange hTb
  have hm := hT r hr
  have hmF := nullMeasurableSet_slabCompetitor
    (nullMeasurableSet_of_verticalCylinder hm.nullMeasurable) hA T
  have hcomp := hm.comparison 0 r hr le_rfl (slabCompetitor L A T) hmF hF
    (slabCompetitor_compact_change hbase T) (hc.trans (subset_closure.trans hQB))
  simp only [ENNReal.ofReal_zero, zero_mul, add_zero] at hcomp
  apply perimeterIn_le_of_compact_change_localization hm.nullMeasurable hmF
    isOpen_ball hQ (subset_closure.trans hQB)
  · simpa only [symmDiff_comm (verticalCylinder L)] using hc
  · exact hm.locallyFinite _ isOpen_ball isBounded_ball.isCompact_closure
  · exact hF _ isOpen_ball isBounded_ball.isCompact_closure
  · exact hcomp

/-- The extended-real product estimates imply the real limiting inequality, with no
conversion of an infinite perimeter to a real number. -/
lemma cone_descent_comparison_of_product_bounds
    {l a c : ℝ≥0∞} (hl : l ≠ ∞) (ha : a ≠ ∞) (hc : c ≠ ∞)
    (h : ∀ T : ℝ, 1 < T →
      ENNReal.ofReal (2 * (T + 1)) * l ≤
        ENNReal.ofReal (2 * T) * a + ENNReal.ofReal 2 * l + 2 * c) :
    l ≤ a := by
  apply (ENNReal.toReal_le_toReal hl ha).mp
  apply cone_descent_real_comparison (c := c.toReal)
  intro T hT
  have hh := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hl⟩,
      ENNReal.mul_ne_top (by norm_num) hc⟩) (h T hT)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hl⟩)
      (ENNReal.mul_ne_top (by norm_num) hc),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hl)] at hh
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * (T + 1)),
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * T),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), ENNReal.toReal_ofNat] at hh
  nlinarith

/-- A finite upper estimate on all bounded open prisms supplies local BV regularity
of the slab competitor. Only heights larger than the fixed slab height are needed. -/
lemma hasLocallyFinitePerimeter_slabCompetitor_of_bound
    {L A : Set (EuclideanSpace ℝ (Fin 2))} {T : ℝ}
    (hL : HasLocallyFinitePerimeter L) (hA : HasLocallyFinitePerimeter A)
    (hbound : ∀ (U : Set (EuclideanSpace ℝ (Fin 2))), IsOpen U →
      IsCompact (closure U) → ∀ b : ℝ, T < b →
      perimeterIn (slabCompetitor L A T) ((euclideanLastEquiv 2) ⁻¹' (Ioo (-b) b ×ˢ U)) ≤
        ENNReal.ofReal (2 * T) * perimeterIn A U +
          ENNReal.ofReal (2 * (b - T)) * perimeterIn L U + 2 * volume ((A ∆ L) ∩ U)) :
    HasLocallyFinitePerimeter (slabCompetitor L A T) := by
  intro V _ hcV
  obtain ⟨R, hTR, hR⟩ :=
    (hcV.image (euclideanLastEquiv 2).continuous).isBounded.subset_ball_lt T
      (0 : ℝ × EuclideanSpace ℝ (Fin 2))
  have hsub : V ⊆ (euclideanLastEquiv 2) ⁻¹'
      (Ioo (-R) R ×ˢ ball (0 : EuclideanSpace ℝ (Fin 2)) R) := by
    intro z hz
    have hh := hR (mem_image_of_mem _ (subset_closure hz))
    simp only [mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff, Real.norm_eq_abs] at hh
    exact ⟨abs_lt.mp hh.1, by simpa only [mem_ball, dist_zero_right] using hh.2⟩
  have hp := hbound (ball 0 R) isOpen_ball isBounded_ball.isCompact_closure R hTR
  have ha := hA (ball 0 R) isOpen_ball isBounded_ball.isCompact_closure
  have hl := hL (ball 0 R) isOpen_ball isBounded_ball.isCompact_closure
  have hv : volume ((A ∆ L) ∩ ball 0 R) < ∞ :=
    (measure_mono inter_subset_right).trans_lt isBounded_ball.measure_lt_top
  exact (variation_mono
    ((isOpen_Ioo.prod isOpen_ball).preimage (euclideanLastEquiv 2).continuous).measurableSet
    hsub).trans_lt (hp.trans_lt (by finiteness))

/-- Assembly of cylinder descent from the slab upper perimeter estimate.
The estimate is needed only for null measurable, locally BV competitors,
relatively compact open bases, and slab heights greater than one. -/
theorem cone_descent_of_slab_upper_bound
    {L : Set (EuclideanSpace ℝ (Fin 2))}
    (hT : IsLocallyPerimeterMinimizing (verticalCylinder L))
    (hupper : ∀ (A : Set (EuclideanSpace ℝ (Fin 2))), NullMeasurableSet A volume →
      HasLocallyFinitePerimeter A → ∀ (U : Set (EuclideanSpace ℝ (Fin 2))),
      IsOpen U → IsCompact (closure U) → ∀ T b : ℝ, 1 < T → T < b →
      perimeterIn (slabCompetitor L A T) ((euclideanLastEquiv 2) ⁻¹' (Ioo (-b) b ×ˢ U)) ≤
        ENNReal.ofReal (2 * T) * perimeterIn A U +
          ENNReal.ofReal (2 * (b - T)) * perimeterIn L U + 2 * volume ((A ∆ L) ∩ U)) :
    IsLocallyPerimeterMinimizing L := by
  have hmL := nullMeasurableSet_of_verticalCylinder (hT 1 zero_lt_one).nullMeasurable
  have hpL := locallyFinite_of_minimizing_verticalCylinder hT
  intro R hR
  refine ⟨le_rfl, ENNReal.ofReal_pos.mpr hR, hmL, hpL, ?_⟩
  intro x r hr _ A hmA hpA hcA hsA
  simp only [ENNReal.ofReal_zero, zero_mul, add_zero]
  have hl := hpL (ball x r) isOpen_ball isBounded_ball.isCompact_closure
  have ha := hpA (ball x r) isOpen_ball isBounded_ball.isCompact_closure
  have hc : volume ((A ∆ L) ∩ ball x r) < ∞ :=
    (measure_mono inter_subset_right).trans_lt isBounded_ball.measure_lt_top
  apply cone_descent_comparison_of_product_bounds hl.ne ha.ne hc.ne
  intro T hheight
  have hF : HasLocallyFinitePerimeter (slabCompetitor L A T) :=
    hasLocallyFinitePerimeter_slabCompetitor_of_bound hpL hpA
      (fun U hU hcU b hb => hupper A hmA hpA U hU hcU T b hheight hb)
  have hlow := perimeterIn_verticalCylinder_lower L (ball x r)
    (a := -(T + 1)) (b := T + 1) (by linarith)
  have hcomp := cylinder_le_slabCompetitor_on_prism hT hmA isOpen_ball
    isBounded_ball.isCompact_closure hcA hsA (T := T) (b := T + 1) (by linarith) hF
  have hu := hupper A hmA hpA (ball x r) isOpen_ball
    isBounded_ball.isCompact_closure T (T + 1) hheight (by linarith)
  have hh := hlow.trans (hcomp.trans hu)
  simpa only [show T + 1 - -(T + 1) = 2 * (T + 1) by ring,
    show 2 * (T + 1 - T) = 2 by ring] using hh

/-- Blueprint `lem:cone-descent`. -/
theorem cone_descent {L : Set (EuclideanSpace ℝ (Fin 2))}
    (hT : IsLocallyPerimeterMinimizing (verticalCylinder L)) :
    IsLocallyPerimeterMinimizing L := by
  have hmL := nullMeasurableSet_of_verticalCylinder (hT 1 zero_lt_one).nullMeasurable
  have hpL := locallyFinite_of_minimizing_verticalCylinder hT
  apply cone_descent_of_slab_upper_bound hT
  intro A hmA hpA U hU hcU T b hheight hTb
  exact perimeterIn_slabCompetitor_upper hmL hmA hU hcU
    (hpA U hU hcU) (hpL U hU hcU) (zero_lt_one.trans hheight) hTb

end LiquidDrop
