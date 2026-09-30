module

public import NoCompromise.Cones.TwoDimGap
public import NoCompromise.Cones.HalfplanePerimeter
public import NoCompromise.Cones.Classification

@[expose] public section

/-!
# The local chord competitor for planar cones

Proof route for blueprint `lem:cone-2d` (chapter 25): use a single short angular
gap and remove a truncated trapezoid, rather than the blueprint's global pairing
of rays. Truncation keeps all perimeter computations away from the vertex.
The existing `TwoDimGap`, `HalfplanePerimeter`, and `Classification` results
supply the angular gap, halfspace costs, and antipodal-link endgame, respectively.

The argument: if the link is not contained in an antipodal pair, there are consecutive link points
at angles `a < b < a + π` (`cone2d_exists_short_gap`); the gap sector is one phase and thin sectors
just outside it are the other (`cone2d_gap_phases_smul`). Removing (in the phase of the gap) the
trapezoid cut from the gap sector by the chords at radii `ε` and `1` replaces two radial segments
of total length `2(1-ε)` by two chords of total length `2 sin((b-a)/2)(1+ε)`, strictly shorter
for `ε = (1 - sin((b-a)/2))/4` (`cone2d_gap_competitor`), contradicting minimality in `B₂`.
Otherwise `cone2d_halfplane_of_link_subset_antipodal` gives the halfplane.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal symmDiff

namespace LiquidDrop

/-- Local agreement with a halfspace identifies the perimeter measure on a compact set. -/
theorem measure_eq_of_ae_eq_halfspace {k : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    {μ : Measure (EuclideanSpace ℝ (Fin (k + 1)))}
    (hμ : ∀ O, IsOpen O → perimeterIn E O = μ O)
    {K : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hK : IsCompact K)
    {ν : EuclideanSpace ℝ (Fin (k + 1))} (hν : ‖ν‖ = 1) (c : ℝ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hE : E =ᵐ[volume.restrict (thickening ε₀ K)] {z | inner ℝ z ν < c}) :
    μ K = Measure.euclideanHausdorffMeasure k (K ∩ {z | inner ℝ z ν = c}) := by
  have hvol (ε : ℝ) : volume (thickening ε K) ≠ ⊤ := by
    have hc : IsCompact (closure (thickening ε K)) :=
      (hK.cthickening (r := ε)).of_isClosed_subset isClosed_closure
        (closure_thickening_subset_cthickening _ _)
    exact ((measure_mono subset_closure).trans_lt hc.measure_lt_top).ne
  have heq (ε : ℝ) (hε : ε ≤ ε₀) :
      μ (thickening ε K) = Measure.euclideanHausdorffMeasure k
        (thickening ε K ∩ {z | inner ℝ z ν = c}) := by
    rw [← hμ _ isOpen_thickening,
      perimeterIn_congr_ae _ (ae_restrict_of_ae_restrict_of_subset
        (thickening_mono hε K) hE),
      perimeterIn_halfspace_eq_hausdorff hν c isOpen_thickening (hvol ε)]
  have hμlim := tendsto_measure_thickening_of_isClosed (μ := μ)
    ⟨ε₀, hε₀, by rw [heq ε₀ le_rfl]
                 exact euclideanHausdorffMeasure_thickening_inter_hyperplane_ne_top hν c hK ε₀⟩
    hK.isClosed
  have hHlim := tendsto_measure_thickening_of_isClosed
    (μ := (Measure.euclideanHausdorffMeasure k).restrict {z | inner ℝ z ν = c})
    ⟨1, one_pos, by
      rw [Measure.restrict_apply isOpen_thickening.measurableSet]
      exact euclideanHausdorffMeasure_thickening_inter_hyperplane_ne_top hν c hK 1⟩
    hK.isClosed
  rw [Measure.restrict_apply hK.measurableSet] at hHlim
  apply tendsto_nhds_unique hμlim
  apply hHlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  rw [Measure.restrict_apply isOpen_thickening.measurableSet, heq ε hε.2.le]

/-- A compact modification with finite perimeter mass has locally finite perimeter.
The perimeter comparison on any containing relatively compact open set reduces to the compact
set itself. No local finiteness of the modified set is assumed. -/
theorem perimeterIn_lt_of_compact_modification {n : ℕ}
    {E G Q U : Set (EuclideanSpace ℝ (Fin n))}
    (hE : HasLocallyFinitePerimeter E) (hQ : IsCompact Q)
    (hU : IsOpen U) (hcU : IsCompact (closure U)) (hQU : Q ⊆ U)
    {μE μG : Measure (EuclideanSpace ℝ (Fin n))}
    (hμE : ∀ O, IsOpen O → perimeterIn E O = μE O)
    (hμG : ∀ O, IsOpen O → perimeterIn G O = μG O)
    (hGE : G =ᵐ[volume.restrict Qᶜ] E) (hsave : μG Q < μE Q) :
    HasLocallyFinitePerimeter G ∧ perimeterIn G U < perimeterIn E U := by
  have heq (V : Set (EuclideanSpace ℝ (Fin n))) (hV : IsOpen V) :
      μG (V \ Q) = μE (V \ Q) := by
    rw [← hμG _ (hV.sdiff hQ.isClosed), ← hμE _ (hV.sdiff hQ.isClosed)]
    exact perimeterIn_congr_ae _ (ae_restrict_of_ae_restrict_of_subset
      (fun _ hx => hx.2) hGE)
  have hfinE : μE Q < ⊤ :=
    (measure_mono hQU).trans_lt (by rw [← hμE U hU]; exact hE U hU hcU)
  have hfinG : μG Q < ⊤ := hsave.trans hfinE
  constructor
  · intro V hV hcV
    rw [hμG V hV]
    calc μG V ≤ μG ((V \ Q) ∪ Q) := measure_mono (by
        intro x hx
        by_cases h : x ∈ Q <;> simp [hx, h])
      _ ≤ μG (V \ Q) + μG Q := measure_union_le _ _
      _ = μE (V \ Q) + μG Q := by rw [heq V hV]
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨(measure_mono sdiff_subset).trans_lt
        (by rw [← hμE V hV]; exact hE V hV hcV), hfinG⟩
  · have hsplit (μ : Measure (EuclideanSpace ℝ (Fin n))) :
        μ (U \ Q) + μ Q = μ U := by
      simpa only [inter_eq_right.mpr hQU] using measure_sdiff_add_inter (μ := μ) U hQ.measurableSet
    rw [hμG U hU, hμE U hU, ← hsplit μG, ← hsplit μE, heq U hU]
    exact ENNReal.add_lt_add_left
      ((measure_mono sdiff_subset).trans_lt
        (by rw [← hμE U hU]; exact hE U hU hcU)).ne hsave

/-- Inner products of polar vectors are given by the angle difference. -/
theorem cone2dCircle_inner_smul (r θ φ : ℝ) :
    inner ℝ (r • cone2dCircle θ) (cone2dCircle φ) = r * Real.cos (θ - φ) := by
  rw [real_inner_smul_left]
  congr 1
  simp only [PiLp.inner_apply, Fin.sum_univ_two, cone2dCircle_zero, cone2dCircle_one,
    RCLike.inner_apply, conj_trivial, Real.cos_sub]
  ring

/-- A unit circle point has a representative in every half-open interval of length two pi. -/
theorem cone2dCircle_surjOn_Ico (a : ℝ) :
    SurjOn cone2dCircle (Ico a (a + 2 * Real.pi)) (sphere 0 1) := by
  intro x hx
  have hr : (cone2dRotation (a + Real.pi)).symm x ∈ sphere 0 1 := by
    simpa only [mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  obtain ⟨t, ht, htx⟩ := cone2dCircle_surjOn hr
  have heq : cone2dCircle (a + Real.pi + t) = x := by
    apply (cone2dRotation (a + Real.pi)).symm.injective
    simpa only [cone2dRotation_symm_circle, add_sub_cancel_left] using htx
  by_cases htp : t = Real.pi
  · refine ⟨a, ⟨le_rfl, by linarith [Real.pi_pos]⟩, ?_⟩
    have hturn : a + Real.pi + t = a + 2 * Real.pi := by rw [htp]; ring
    simpa only [hturn, cone2dCircle_add_two_pi] using heq
  · exact ⟨a + Real.pi + t, ⟨by linarith [ht.1],
      by have := lt_of_le_of_ne ht.2 htp; linarith⟩, heq⟩

/-- Every nonzero vector has polar coordinates with angle in a specified one-turn interval. -/
theorem cone2d_exists_polar_Ico {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) (a : ℝ) :
    ∃ θ ∈ Ico a (a + 2 * Real.pi), x = ‖x‖ • cone2dCircle θ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖x‖⁻¹ • x ∈ sphere 0 1 := by
    simp [norm_smul, hn.ne']
  obtain ⟨θ, hθ, heq⟩ := cone2dCircle_surjOn_Ico a hu
  refine ⟨θ, hθ, ?_⟩
  rw [heq, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

/-- The explicit truncation parameter gives a strict chord saving. -/
theorem cone2d_chord_saving {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    0 < (1 - s) / 4 ∧ (1 - s) / 4 < 1 ∧
      2 * s * (1 + (1 - s) / 4) < 2 * (1 - (1 - s) / 4) := by
  constructor
  · positivity
  constructor
  · linarith
  · nlinarith [sq_nonneg (1 - s)]

/-- Segments in Euclidean space are compact. -/
theorem cone2d_isCompact_segment {k : ℕ} (p q : EuclideanSpace ℝ (Fin k)) :
    IsCompact (segment ℝ p q) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image (by fun_prop)

/-- On a line segment, local halfspace agreement gives exactly the segment's length. -/
theorem measure_segment_eq_of_ae_eq_halfspace
    {E : Set (EuclideanSpace ℝ (Fin 2))} {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμ : ∀ O, IsOpen O → perimeterIn E O = μ O)
    {p q ν : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q) (hν : ‖ν‖ = 1) (c : ℝ)
    (hline : segment ℝ p q ⊆ {z | inner ℝ z ν = c})
    {δ : ℝ} (hδ : 0 < δ)
    (hE : E =ᵐ[volume.restrict (thickening δ (segment ℝ p q))]
      {z | inner ℝ z ν < c}) :
    μ (segment ℝ p q) = ENNReal.ofReal (dist p q) := by
  rw [measure_eq_of_ae_eq_halfspace hμ (cone2d_isCompact_segment p q) hν c hδ hE,
    inter_eq_left.mpr hline, euclideanHausdorffMeasure_one_segment hpq]

/-- At a chord, the other two bounding lines contribute only endpoints and hence no length. -/
theorem measure_segment_le_of_ae_eq_three_halfspaces
    {G : Set (EuclideanSpace ℝ (Fin 2))} {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμ : ∀ O, IsOpen O → perimeterIn G O = μ O)
    {p q ν₁ ν₂ ν₃ : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q)
    (h₁ : ‖ν₁‖ = 1) (h₂ : ‖ν₂‖ = 1) (h₃ : ‖ν₃‖ = 1) (c₁ c₂ c₃ : ℝ)
    (hside₁ : segment ℝ p q ∩ {z | inner ℝ z ν₁ = c₁} ⊆ {p})
    (hside₂ : segment ℝ p q ∩ {z | inner ℝ z ν₂ = c₂} ⊆ {q})
    (hline : segment ℝ p q ⊆ {z | inner ℝ z ν₃ = c₃})
    {δ : ℝ} (hδ : 0 < δ)
    (hG : G =ᵐ[volume.restrict (thickening δ (segment ℝ p q))]
      ({z | inner ℝ z ν₁ < c₁} ∩ {z | inner ℝ z ν₂ < c₂} ∩
        {z | inner ℝ z ν₃ < c₃} : Set (EuclideanSpace ℝ (Fin 2)))) :
    μ (segment ℝ p q) ≤ ENNReal.ofReal (dist p q) := by
  have h := measure_le_of_ae_eq_three_halfspaces hμ (cone2d_isCompact_segment p q)
    h₁ h₂ h₃ c₁ c₂ c₃ hδ hG
  have hz₁ := measure_mono_null hside₁ (euclideanHausdorffMeasure_one_singleton p)
  have hz₂ := measure_mono_null hside₂ (euclideanHausdorffMeasure_one_singleton q)
  simpa only [hz₁, hz₂, zero_add, inter_eq_left.mpr hline,
    euclideanHausdorffMeasure_one_segment hpq] using h

/-- A cover by a zero-cost open region and two chords bounds the compact modification cost. -/
theorem measure_le_two_chords
    {G Q O : Set (EuclideanSpace ℝ (Fin 2))} {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμ : ∀ V, IsOpen V → perimeterIn G V = μ V)
    (hO : IsOpen O) (hG : G =ᵐ[volume.restrict O] (∅ : Set (EuclideanSpace ℝ (Fin 2))))
    {p₁ p₂ q₁ q₂ : EuclideanSpace ℝ (Fin 2)}
    (hcover : Q ⊆ O ∪ segment ℝ p₁ p₂ ∪ segment ℝ q₁ q₂)
    (hp : μ (segment ℝ p₁ p₂) ≤ ENNReal.ofReal (dist p₁ p₂))
    (hq : μ (segment ℝ q₁ q₂) ≤ ENNReal.ofReal (dist q₁ q₂)) :
    μ Q ≤ ENNReal.ofReal (dist p₁ p₂) + ENNReal.ofReal (dist q₁ q₂) := by
  have hzero : μ O = 0 := by
    rw [← hμ O hO, perimeterIn_congr_ae O hG]
    exact perimeterIn_eq_zero_of_disjoint hO.measurableSet (empty_disjoint O)
  calc μ Q ≤ μ (O ∪ segment ℝ p₁ p₂ ∪ segment ℝ q₁ q₂) := measure_mono hcover
    _ ≤ μ (O ∪ segment ℝ p₁ p₂) + μ (segment ℝ q₁ q₂) := measure_union_le _ _
    _ ≤ (μ O + μ (segment ℝ p₁ p₂)) + μ (segment ℝ q₁ q₂) :=
      add_le_add (measure_union_le _ _) le_rfl
    _ ≤ _ := by simpa only [hzero, zero_add] using add_le_add hp hq

/-- Two disjoint radial segments give the required lower bound on the old perimeter. -/
theorem two_segments_le_measure
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {Q : Set (EuclideanSpace ℝ (Fin 2))}
    {p₁ p₂ q₁ q₂ : EuclideanSpace ℝ (Fin 2)}
    (hsub₁ : segment ℝ q₁ p₁ ⊆ Q) (hsub₂ : segment ℝ q₂ p₂ ⊆ Q)
    (hdisj : Disjoint (segment ℝ q₁ p₁) (segment ℝ q₂ p₂))
    (h₁ : μ (segment ℝ q₁ p₁) = ENNReal.ofReal (dist q₁ p₁))
    (h₂ : μ (segment ℝ q₂ p₂) = ENNReal.ofReal (dist q₂ p₂)) :
    ENNReal.ofReal (dist q₁ p₁) + ENNReal.ofReal (dist q₂ p₂) ≤ μ Q := by
  rw [← h₁, ← h₂, ← measure_union hdisj (cone2d_isCompact_segment q₂ p₂).measurableSet]
  exact measure_mono (union_subset hsub₁ hsub₂)

/-- Abstract truncated-chord comparison, with the geometric costs stated explicitly.
The preceding three lemmas obtain these costs from the local halfspace descriptions. -/
theorem perimeterIn_sdiff_lt_of_two_chords
    {E Q U : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : HasLocallyFinitePerimeter E) (hQ : IsCompact Q)
    (hU : IsOpen U) (hcU : IsCompact (closure U)) (hQU : Q ⊆ U)
    {μE μG : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμE : ∀ O, IsOpen O → perimeterIn E O = μE O)
    (hμG : ∀ O, IsOpen O → perimeterIn (E \ Q) O = μG O)
    {p₁ p₂ q₁ q₂ : EuclideanSpace ℝ (Fin 2)}
    (hsub₁ : segment ℝ q₁ p₁ ⊆ Q) (hsub₂ : segment ℝ q₂ p₂ ⊆ Q)
    (hdisj : Disjoint (segment ℝ q₁ p₁) (segment ℝ q₂ p₂))
    (h₁ : μE (segment ℝ q₁ p₁) = ENNReal.ofReal (dist q₁ p₁))
    (h₂ : μE (segment ℝ q₂ p₂) = ENNReal.ofReal (dist q₂ p₂))
    (hcost : μG Q ≤ ENNReal.ofReal (dist p₁ p₂) + ENNReal.ofReal (dist q₁ q₂))
    (hsave : dist p₁ p₂ + dist q₁ q₂ < dist q₁ p₁ + dist q₂ p₂) :
    HasLocallyFinitePerimeter (E \ Q) ∧ perimeterIn (E \ Q) U < perimeterIn E U := by
  apply perimeterIn_lt_of_compact_modification hE hQ hU hcU hQU hμE hμG
  · filter_upwards [ae_restrict_mem hQ.measurableSet.compl] with x hx
    simp only [mem_compl_iff] at hx
    change (x ∈ E \ Q) = (x ∈ E)
    simp only [Set.mem_sdiff, hx, not_false_eq_true, and_true]
  · apply hcost.trans_lt
    apply lt_of_lt_of_le _ (two_segments_le_measure hsub₁ hsub₂ hdisj h₁ h₂)
    rw [← ENNReal.ofReal_add (dist_nonneg : 0 ≤ dist p₁ p₂) dist_nonneg,
      ← ENNReal.ofReal_add (dist_nonneg : 0 ≤ dist q₁ p₁) dist_nonneg]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hsave

/-- Minimality rules out a compact removal improvement of any a.e. representative. -/
theorem cone2d_no_sdiff_improvement
    {C E Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C) (hEC : E =ᵐ[volume] C)
    (hQ : IsCompact Q) (hQball : Q ⊆ ball 0 2)
    (hG : HasLocallyFinitePerimeter (E \ Q)) :
    perimeterIn E (ball 0 2) ≤ perimeterIn (E \ Q) (ball 0 2) := by
  have hcut : E \ Q =ᵐ[volume] C \ Q := by
    filter_upwards [hEC] with x hx
    change (x ∈ E ∧ x ∉ Q) = (x ∈ C ∧ x ∉ Q)
    rw [show (x ∈ E) = (x ∈ C) from hx]
  have hp : HasLocallyFinitePerimeter (C \ Q) := by
    intro U hU hcU
    calc perimeterIn (C \ Q) U = perimeterIn (E \ Q) U :=
        perimeterIn_congr_ae U (ae_restrict_of_ae hcut.symm)
      _ < ⊤ := hG U hU hcU
  have hs : (C \ Q) ∆ C ⊆ Q := by
    intro x hx
    simp only [mem_symmDiff, Set.mem_sdiff] at hx
    tauto
  have hc : closure ((C \ Q) ∆ C) ⊆ Q := closure_minimal hs hQ.isClosed
  have hm := (hmin 2 (by norm_num)).nullMeasurable
  have h := (hmin 2 (by norm_num)).comparison 0 2 (by norm_num) le_rfl (C \ Q)
    (hm.diff hQ.measurableSet.nullMeasurableSet) hp
    (hQ.of_isClosed_subset isClosed_closure hc) (hc.trans hQball)
  simp only [ENNReal.ofReal_zero, zero_mul, add_zero] at h
  calc perimeterIn E (ball 0 2) = perimeterIn C (ball 0 2) :=
      perimeterIn_congr_ae _ (ae_restrict_of_ae hEC)
    _ ≤ perimeterIn (C \ Q) (ball 0 2) := h
    _ = perimeterIn (E \ Q) (ball 0 2) :=
      perimeterIn_congr_ae _ (ae_restrict_of_ae hcut.symm)

/-- The reverse phase is handled by minimality of the complement. -/
theorem cone2d_no_compl_sdiff_improvement
    {C E Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C) (hEC : E =ᵐ[volume] Cᶜ)
    (hQ : IsCompact Q) (hQball : Q ⊆ ball 0 2)
    (hG : HasLocallyFinitePerimeter (E \ Q)) :
    perimeterIn E (ball 0 2) ≤ perimeterIn (E \ Q) (ball 0 2) := by
  exact cone2d_no_sdiff_improvement (fun R hR => (hmin R hR).compl) hEC hQ hQball hG

/-- A short gap has positive midpoint height and half-chord length strictly below one. -/
theorem cone2d_short_gap_trig {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    (hπ : θ₂ < θ₁ + Real.pi) :
    0 < Real.cos ((θ₂ - θ₁) / 2) ∧
    0 < Real.sin ((θ₂ - θ₁) / 2) ∧ Real.sin ((θ₂ - θ₁) / 2) < 1 := by
  have hc : 0 < Real.cos ((θ₂ - θ₁) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs : 0 < Real.sin ((θ₂ - θ₁) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  refine ⟨hc, hs, ?_⟩
  nlinarith [Real.sin_sq_add_cos_sq ((θ₂ - θ₁) / 2)]

/-- The length of a radial segment in the unit disk. -/
theorem cone2d_dist_radial (θ : ℝ) {ε : ℝ} (hε : ε ≤ 1) :
    dist (ε • cone2dCircle θ) (cone2dCircle θ) = 1 - ε := by
  rw [dist_eq_norm, show ε • cone2dCircle θ - cone2dCircle θ =
    (ε - 1) • cone2dCircle θ by rw [sub_smul, one_smul], norm_smul]
  simp only [cone2dCircle_norm, mul_one, Real.norm_eq_abs]
  rw [abs_of_nonpos (by linarith)]
  ring

/-- The chord of a short angular gap has length twice the sine of its half-angle. -/
theorem cone2d_dist_chord {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    (hπ : θ₂ < θ₁ + Real.pi) :
    dist (cone2dCircle θ₁) (cone2dCircle θ₂) = 2 * Real.sin ((θ₂ - θ₁) / 2) := by
  have ht := cone2d_short_gap_trig hθ hπ
  have hc : inner ℝ (cone2dCircle θ₁) (cone2dCircle θ₂) = Real.cos (θ₁ - θ₂) := by
    simpa using cone2dCircle_inner_smul 1 θ₁ θ₂
  have hcos : Real.cos (θ₁ - θ₂) = 1 - 2 * Real.sin ((θ₂ - θ₁) / 2) ^ 2 := by
    rw [show θ₁ - θ₂ = -(2 * ((θ₂ - θ₁) / 2)) by ring, Real.cos_neg, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq ((θ₂ - θ₁) / 2)]
  have hd := norm_sub_sq_real (cone2dCircle θ₁) (cone2dCircle θ₂)
  rw [← dist_eq_norm, cone2dCircle_norm, cone2dCircle_norm, hc, hcos] at hd
  nlinarith [dist_nonneg (x := cone2dCircle θ₁) (y := cone2dCircle θ₂)]

/-- Open-neighborhood form of the compact halfspace equality. -/
theorem measure_eq_of_ae_eq_halfspace_on_open {k : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    {μ : Measure (EuclideanSpace ℝ (Fin (k + 1)))}
    (hμ : ∀ O, IsOpen O → perimeterIn E O = μ O)
    {K V : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {ν : EuclideanSpace ℝ (Fin (k + 1))} (hν : ‖ν‖ = 1) (c : ℝ)
    (hE : E =ᵐ[volume.restrict V] {z | inner ℝ z ν < c}) :
    μ K = Measure.euclideanHausdorffMeasure k (K ∩ {z | inner ℝ z ν = c}) := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hV hKV
  exact measure_eq_of_ae_eq_halfspace hμ hK hν c hδ
    (ae_restrict_of_ae_restrict_of_subset hsub hE)

/-- Open-neighborhood form of the chord upper bound. -/
theorem measure_segment_le_of_ae_eq_three_halfspaces_on_open
    {G : Set (EuclideanSpace ℝ (Fin 2))} {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμ : ∀ O, IsOpen O → perimeterIn G O = μ O)
    {p q ν₁ ν₂ ν₃ : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q)
    (h₁ : ‖ν₁‖ = 1) (h₂ : ‖ν₂‖ = 1) (h₃ : ‖ν₃‖ = 1) (c₁ c₂ c₃ : ℝ)
    (hside₁ : segment ℝ p q ∩ {z | inner ℝ z ν₁ = c₁} ⊆ {p})
    (hside₂ : segment ℝ p q ∩ {z | inner ℝ z ν₂ = c₂} ⊆ {q})
    (hline : segment ℝ p q ⊆ {z | inner ℝ z ν₃ = c₃})
    {V : Set (EuclideanSpace ℝ (Fin 2))} (hV : IsOpen V) (hKV : segment ℝ p q ⊆ V)
    (hG : G =ᵐ[volume.restrict V]
      ({z | inner ℝ z ν₁ < c₁} ∩ {z | inner ℝ z ν₂ < c₂} ∩
        {z | inner ℝ z ν₃ < c₃} : Set (EuclideanSpace ℝ (Fin 2)))) :
    μ (segment ℝ p q) ≤ ENNReal.ofReal (dist p q) := by
  obtain ⟨δ, hδ, hsub⟩ := (cone2d_isCompact_segment p q).exists_thickening_subset_open hV hKV
  exact measure_segment_le_of_ae_eq_three_halfspaces hμ hpq h₁ h₂ h₃ c₁ c₂ c₃
    hside₁ hside₂ hline hδ (ae_restrict_of_ae_restrict_of_subset hsub hG)

/-- The closed trapezoid obtained by cutting a closed wedge between two parallel lines. -/
def cone2dTrapezoid (ν₁ ν₂ m : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | inner ℝ x ν₁ ≤ 0 ∧ inner ℝ x ν₂ ≤ 0 ∧ a ≤ inner ℝ x m ∧ inner ℝ x m ≤ b}

/-- Removing the trapezoid leaves the upper three-halfspace intersection above its lower cut. -/
theorem cone2d_sdiff_trapezoid_ae_upper
    {E W : Set (EuclideanSpace ℝ (Fin 2))} {ν₁ ν₂ m : EuclideanSpace ℝ (Fin 2)}
    {a b : ℝ} (hW : MeasurableSet W)
    (hE : E =ᵐ[volume.restrict W]
      ({x | inner ℝ x ν₁ < 0} ∩ {x | inner ℝ x ν₂ < 0} : Set (EuclideanSpace ℝ (Fin 2)))) :
    E \ cone2dTrapezoid ν₁ ν₂ m a b =ᵐ[volume.restrict (W ∩ {x | a < inner ℝ x m})]
      ({x | inner ℝ x ν₁ < 0} ∩ {x | inner ℝ x ν₂ < 0} ∩
        {x | inner ℝ x (-m) < -b} : Set (EuclideanSpace ℝ (Fin 2))) := by
  have hm : MeasurableSet (W ∩ {x | a < inner ℝ x m}) :=
    hW.inter (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hE,
    ae_restrict_mem hm] with x hx hmem
  change (x ∈ E) = (inner ℝ x ν₁ < 0 ∧ inner ℝ x ν₂ < 0) at hx
  change ((x ∈ E) ∧ ¬ (inner ℝ x ν₁ ≤ 0 ∧ inner ℝ x ν₂ ≤ 0 ∧
    a ≤ inner ℝ x m ∧ inner ℝ x m ≤ b)) =
    ((inner ℝ x ν₁ < 0 ∧ inner ℝ x ν₂ < 0) ∧ inner ℝ x (-m) < -b)
  rw [hx, inner_neg_right]
  apply propext
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hnot⟩
    refine ⟨⟨h₁, h₂⟩, ?_⟩
    have : b < inner ℝ x m := by
      by_contra h
      exact hnot ⟨h₁.le, h₂.le, hmem.2.le, le_of_not_gt h⟩
    linarith
  · rintro ⟨⟨h₁, h₂⟩, htop⟩
    exact ⟨⟨h₁, h₂⟩, fun h => by linarith [h.2.2.2]⟩

/-- Below the upper cut, the remainder is the lower three-halfspace intersection. -/
theorem cone2d_sdiff_trapezoid_ae_lower
    {E W : Set (EuclideanSpace ℝ (Fin 2))} {ν₁ ν₂ m : EuclideanSpace ℝ (Fin 2)}
    {a b : ℝ} (hW : MeasurableSet W)
    (hE : E =ᵐ[volume.restrict W]
      ({x | inner ℝ x ν₁ < 0} ∩ {x | inner ℝ x ν₂ < 0} : Set (EuclideanSpace ℝ (Fin 2)))) :
    E \ cone2dTrapezoid ν₁ ν₂ m a b =ᵐ[volume.restrict (W ∩ {x | inner ℝ x m < b})]
      ({x | inner ℝ x ν₁ < 0} ∩ {x | inner ℝ x ν₂ < 0} ∩
        {x | inner ℝ x m < a} : Set (EuclideanSpace ℝ (Fin 2))) := by
  have hm : MeasurableSet (W ∩ {x | inner ℝ x m < b}) :=
    hW.inter (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hE,
    ae_restrict_mem hm] with x hx hmem
  change (x ∈ E) = (inner ℝ x ν₁ < 0 ∧ inner ℝ x ν₂ < 0) at hx
  change ((x ∈ E) ∧ ¬ (inner ℝ x ν₁ ≤ 0 ∧ inner ℝ x ν₂ ≤ 0 ∧
    a ≤ inner ℝ x m ∧ inner ℝ x m ≤ b)) =
    ((inner ℝ x ν₁ < 0 ∧ inner ℝ x ν₂ < 0) ∧ inner ℝ x m < a)
  rw [hx]
  apply propext
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hnot⟩
    refine ⟨⟨h₁, h₂⟩, ?_⟩
    by_contra h
    exact hnot ⟨h₁.le, h₂.le, le_of_not_gt h, hmem.2.le⟩
  · rintro ⟨⟨h₁, h₂⟩, hbot⟩
    exact ⟨⟨h₁, h₂⟩, fun h => by linarith [h.2.2.1]⟩

/-- Between the cuts the removed wedge has zero remaining volume. -/
theorem cone2d_sdiff_trapezoid_ae_empty
    {E W : Set (EuclideanSpace ℝ (Fin 2))} {ν₁ ν₂ m : EuclideanSpace ℝ (Fin 2)}
    {a b : ℝ} (hW : MeasurableSet W)
    (hE : E =ᵐ[volume.restrict W]
      ({x | inner ℝ x ν₁ < 0} ∩ {x | inner ℝ x ν₂ < 0} : Set (EuclideanSpace ℝ (Fin 2)))) :
    E \ cone2dTrapezoid ν₁ ν₂ m a b =ᵐ[volume.restrict
      (W ∩ {x | a < inner ℝ x m ∧ inner ℝ x m < b})]
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
  have hm : MeasurableSet (W ∩ {x | a < inner ℝ x m ∧ inner ℝ x m < b}) := by
    apply hW.inter
    have ho : IsOpen {x : EuclideanSpace ℝ (Fin 2) | a < inner ℝ x m ∧ inner ℝ x m < b} := by
      change IsOpen ({x : EuclideanSpace ℝ (Fin 2) | a < inner ℝ x m} ∩
        {x | inner ℝ x m < b})
      exact (isOpen_lt continuous_const (continuous_id.inner continuous_const)).inter
        (isOpen_lt (continuous_id.inner continuous_const) continuous_const)
    exact ho.measurableSet
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hE,
    ae_restrict_mem hm] with x hx hmem
  change (x ∈ E) = (inner ℝ x ν₁ < 0 ∧ inner ℝ x ν₂ < 0) at hx
  change (x ∈ E ∧ x ∉ cone2dTrapezoid ν₁ ν₂ m a b) = False
  rw [hx]
  apply propext
  simp only [iff_false]
  rintro ⟨⟨h₁, h₂⟩, hn⟩
  exact hn ⟨h₁.le, h₂.le, hmem.2.1.le, hmem.2.2.le⟩

/-- The left outward normal evaluates to minus the sine of the angular displacement. -/
theorem cone2dCircle_inner_left_normal (r θ a : ℝ) :
    inner ℝ (r • cone2dCircle θ) (cone2dCircle (a - Real.pi / 2)) =
      -r * Real.sin (θ - a) := by
  rw [cone2dCircle_inner_smul, show θ - (a - Real.pi / 2) =
    (θ - a) + Real.pi / 2 by ring, Real.cos_add_pi_div_two]
  ring

/-- The right outward normal evaluates to the sine of the angular displacement. -/
theorem cone2dCircle_inner_right_normal (r θ b : ℝ) :
    inner ℝ (r • cone2dCircle θ) (cone2dCircle (b + Real.pi / 2)) =
      r * Real.sin (θ - b) := by
  rw [cone2dCircle_inner_smul, show θ - (b + Real.pi / 2) =
    (θ - b) - Real.pi / 2 by ring, Real.cos_sub_pi_div_two]

/-- On one turn, a short open wedge is exactly its open angular interval. -/
theorem cone2d_wedge_iff_angle {a b θ r : ℝ}
    (hab : a < b) (hπ : b < a + Real.pi) (hr : 0 < r)
    (hθ : θ ∈ Ico a (a + 2 * Real.pi)) :
    (inner ℝ (r • cone2dCircle θ) (cone2dCircle (a - Real.pi / 2)) < 0 ∧
      inner ℝ (r • cone2dCircle θ) (cone2dCircle (b + Real.pi / 2)) < 0) ↔
        θ ∈ Ioo a b := by
  rw [cone2dCircle_inner_left_normal, cone2dCircle_inner_right_normal]
  constructor
  · rintro ⟨hl, hu⟩
    have hs : 0 < Real.sin (θ - a) := by nlinarith
    have hθa : a < θ := by
      by_contra h
      have he : θ = a := le_antisymm (le_of_not_gt h) hθ.1
      simp [he] at hs
    have hθπ : θ < a + Real.pi := by
      by_contra h
      have hn : 0 ≤ Real.sin (θ - a - Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2])
      rw [Real.sin_sub_pi] at hn
      linarith
    refine ⟨hθa, ?_⟩
    by_contra h
    have hn := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ θ - b by linarith) (show θ - b ≤ Real.pi by linarith)
    nlinarith
  · intro h
    have hl := Real.sin_pos_of_pos_of_lt_pi
      (show 0 < θ - a by linarith [h.1]) (show θ - a < Real.pi by linarith [h.2])
    have hu := Real.sin_neg_of_neg_of_neg_pi_lt
      (show θ - b < 0 by linarith [h.2]) (show -Real.pi < θ - b by linarith [h.1])
    constructor <;> nlinarith

/-- The short open wedge consists of positive dilations of its circle arc. -/
theorem cone2d_wedge_eq_polar {a b : ℝ} (hab : a < b) (hπ : b < a + Real.pi) :
    ({x | inner ℝ x (cone2dCircle (a - Real.pi / 2)) < 0} ∩
      {x | inner ℝ x (cone2dCircle (b + Real.pi / 2)) < 0} : Set (EuclideanSpace ℝ (Fin 2))) =
      {x | ∃ θ ∈ Ioo a b, ∃ r : ℝ, 0 < r ∧ x = r • cone2dCircle θ} := by
  ext x
  constructor
  · intro hx
    have hx0 : x ≠ 0 := by rintro rfl; simpa using hx.1
    obtain ⟨θ, hθ, heq⟩ := cone2d_exists_polar_Ico hx0 a
    refine ⟨θ, ?_, ‖x‖, norm_pos_iff.mpr hx0, heq⟩
    apply (cone2d_wedge_iff_angle hab hπ (norm_pos_iff.mpr hx0) hθ).mp
    rw [← heq]
    exact hx
  · rintro ⟨θ, hθ, r, hr, rfl⟩
    exact (cone2d_wedge_iff_angle hab hπ hr
      ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩).mpr hθ

/-- The angular phase hypotheses give a.e. agreement with the wedge on an explicitly
widened open wedge. The two endpoint lines are the only exceptional sets. -/
theorem cone2d_gap_ae_wedge
    {E : Set (EuclideanSpace ℝ (Fin 2))} {a b η : ℝ}
    (hab : a < b) (hπ : b < a + Real.pi) (hη : 0 < η)
    (hin : ∀ θ ∈ Ioo a b, ∀ r : ℝ, 0 < r → r • cone2dCircle θ ∈ E)
    (hleft : ∀ θ ∈ Ioo (a - η) a, ∀ r : ℝ, 0 < r → r • cone2dCircle θ ∉ E)
    (hright : ∀ θ ∈ Ioo b (b + η), ∀ r : ℝ, 0 < r → r • cone2dCircle θ ∉ E) :
    ∃ δ > 0, δ ≤ min η (b - a) ∧ b + δ < (a - δ) + Real.pi ∧
      E =ᵐ[volume.restrict
        ({x | inner ℝ x (cone2dCircle (a - δ - Real.pi / 2)) < 0} ∩
          {x | inner ℝ x (cone2dCircle (b + δ + Real.pi / 2)) < 0})]
        ({x | inner ℝ x (cone2dCircle (a - Real.pi / 2)) < 0} ∩
          {x | inner ℝ x (cone2dCircle (b + Real.pi / 2)) < 0} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
  let δ := min (min (η / 2) ((b - a) / 2)) ((a + Real.pi - b) / 4)
  have hδ : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hδη : δ ≤ η := (min_le_left _ _).trans ((min_le_left _ _).trans (by linarith))
  have hδα : δ ≤ b - a := (min_le_left _ _).trans ((min_le_right _ _).trans (by linarith))
  have hδπ : b + δ < (a - δ) + Real.pi := by
    have := min_le_right (min (η / 2) ((b - a) / 2)) ((a + Real.pi - b) / 4)
    dsimp [δ] at *
    linarith
  refine ⟨δ, hδ, le_min hδη hδα, hδπ, ?_⟩
  let W : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | inner ℝ x (cone2dCircle (a - δ - Real.pi / 2)) < 0} ∩
      {x | inner ℝ x (cone2dCircle (b + δ + Real.pi / 2)) < 0}
  have hW : IsOpen W :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).inter
      (isOpen_lt (continuous_id.inner continuous_const) continuous_const)
  have hn (t : ℝ) : ∀ᵐ x ∂volume, inner ℝ x (cone2dCircle t) ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not, real_inner_comm] using
      (volume_hyperplane (ν := cone2dCircle t) (by
        intro he; have hh := cone2dCircle_norm t; rw [he, norm_zero] at hh; norm_num at hh))
  change E =ᵐ[volume.restrict W] _
  filter_upwards [ae_restrict_mem hW.measurableSet,
    ae_restrict_of_ae (hn (a - Real.pi / 2)),
    ae_restrict_of_ae (hn (b + Real.pi / 2))] with x hx hna hnb
  obtain ⟨θ, hθ, r, hr, rfl⟩ :=
    (Set.ext_iff.mp (cone2d_wedge_eq_polar (show a - δ < b + δ by linarith) hδπ) x).mp hx
  have hθa : θ ≠ a := by
    intro he
    apply hna
    rw [cone2dCircle_inner_left_normal, he, sub_self, Real.sin_zero, mul_zero]
  have hθb : θ ≠ b := by
    intro he
    apply hnb
    rw [cone2dCircle_inner_right_normal, he, sub_self, Real.sin_zero, mul_zero]
  change (r • cone2dCircle θ ∈ E) =
    (inner ℝ (r • cone2dCircle θ) (cone2dCircle (a - Real.pi / 2)) < 0 ∧
      inner ℝ (r • cone2dCircle θ) (cone2dCircle (b + Real.pi / 2)) < 0)
  apply propext
  by_cases hla : θ < a
  · have hnot := hleft θ ⟨by linarith [hθ.1], hla⟩ r hr
    have hs := Real.sin_neg_of_neg_of_neg_pi_lt (show θ - a < 0 by linarith)
      (show -Real.pi < θ - a by linarith [hθ.1])
    rw [cone2dCircle_inner_left_normal]
    have hf : ¬ (-r * Real.sin (θ - a) < 0) := by nlinarith
    simp only [hnot, hf, false_and]
  · by_cases hgb : b < θ
    · have hnot := hright θ ⟨hgb, by linarith [hθ.2]⟩ r hr
      have hs := Real.sin_pos_of_pos_of_lt_pi (show 0 < θ - b by linarith)
        (show θ - b < Real.pi by linarith [hθ.2])
      rw [cone2dCircle_inner_right_normal]
      have hf : ¬ (r * Real.sin (θ - b) < 0) := by nlinarith
      simp only [hnot, hf, and_false]
    · have hgap : θ ∈ Ioo a b := ⟨lt_of_le_of_ne (le_of_not_gt hla) hθa.symm,
        lt_of_le_of_ne (le_of_not_gt hgb) hθb⟩
      have hwedge := (cone2d_wedge_iff_angle hab hπ hr
        ⟨hgap.1.le, by linarith [hgap.2, Real.pi_pos]⟩).mpr hgap
      exact iff_of_true (hin θ hgap r hr) hwedge

/-- A segment lies in a hyperplane if both endpoints do. -/
theorem cone2d_segment_hyperplane {p q ν : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (hp : inner ℝ p ν = c) (hq : inner ℝ q ν = c) :
    segment ℝ p q ⊆ {x | inner ℝ x ν = c} := by
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  change inner ℝ (u • p + v • q) ν = c
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hp, hq,
    ← add_mul, huv, one_mul]

/-- Strict halfspaces are convex, in the segment form used below. -/
theorem cone2d_segment_halfspace {p q ν : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (hp : inner ℝ p ν < c) (hq : inner ℝ q ν < c) :
    segment ℝ p q ⊆ {x | inner ℝ x ν < c} := by
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  change inner ℝ (u • p + v • q) ν < c
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hsum : u * c + v * c = c := by rw [← add_mul, huv, one_mul]
  have h₁ := mul_nonneg hu (sub_nonneg.mpr hp.le)
  have h₂ := mul_nonneg hv (sub_nonneg.mpr hq.le)
  rcases lt_or_eq_of_le hu with hu | rfl
  · nlinarith [mul_pos hu (sub_pos.mpr hp)]
  · nlinarith

/-- A transverse segment meets the first endpoint's hyperplane only at that endpoint. -/
theorem cone2d_segment_inter_hyperplane_left {p q ν : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (hp : inner ℝ p ν = c) (hq : inner ℝ q ν < c) :
    segment ℝ p q ∩ {x | inner ℝ x ν = c} ⊆ {p} := by
  rintro x ⟨⟨u, v, hu, hv, huv, rfl⟩, hx⟩
  change inner ℝ (u • p + v • q) ν = c at hx
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hp] at hx
  have hsum : u * c + v * c = c := by rw [← add_mul, huv, one_mul]
  have hv0 : v = 0 := by nlinarith
  have hu1 : u = 1 := by linarith
  simp [hv0, hu1]

/-- A transverse segment meets the second endpoint's hyperplane only there. -/
theorem cone2d_segment_inter_hyperplane_right {p q ν : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (hp : inner ℝ p ν < c) (hq : inner ℝ q ν = c) :
    segment ℝ p q ∩ {x | inner ℝ x ν = c} ⊆ {q} := by
  rw [segment_symm]
  exact cone2d_segment_inter_hyperplane_left hq hp

/-- The two chords bound the new perimeter on a trapezoid. The set only needs to agree
with the wedge on an open neighborhood of that trapezoid. -/
theorem cone2d_trapezoid_cost
    {E W : Set (EuclideanSpace ℝ (Fin 2))}
    {ν₁ ν₂ m : EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (hab : a < b)
    (h₁ : ‖ν₁‖ = 1) (h₂ : ‖ν₂‖ = 1) (hm : ‖m‖ = 1)
    (hW : IsOpen W) (hQW : cone2dTrapezoid ν₁ ν₂ m a b ⊆ W)
    (hE : E =ᵐ[volume.restrict W]
      ({x | inner ℝ x ν₁ < 0} ∩ {x | inner ℝ x ν₂ < 0} : Set (EuclideanSpace ℝ (Fin 2))))
    {p₁ p₂ q₁ q₂ : EuclideanSpace ℝ (Fin 2)} (hp : p₁ ≠ p₂) (hq : q₁ ≠ q₂)
    (htop : cone2dTrapezoid ν₁ ν₂ m a b ∩ {x | inner ℝ x m = b} = segment ℝ p₁ p₂)
    (hbot : cone2dTrapezoid ν₁ ν₂ m a b ∩ {x | inner ℝ x m = a} = segment ℝ q₁ q₂)
    (hp₁ : inner ℝ p₁ ν₁ = 0) (hp₂ : inner ℝ p₂ ν₁ < 0)
    (hp₃ : inner ℝ p₁ ν₂ < 0) (hp₄ : inner ℝ p₂ ν₂ = 0)
    (hq₁ : inner ℝ q₁ ν₁ = 0) (hq₂ : inner ℝ q₂ ν₁ < 0)
    (hq₃ : inner ℝ q₁ ν₂ < 0) (hq₄ : inner ℝ q₂ ν₂ = 0)
    {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμ : ∀ O, IsOpen O → perimeterIn (E \ cone2dTrapezoid ν₁ ν₂ m a b) O = μ O) :
    μ (cone2dTrapezoid ν₁ ν₂ m a b) ≤
      ENNReal.ofReal (dist p₁ p₂) + ENNReal.ofReal (dist q₁ q₂) := by
  have ht (x) (hx : x ∈ segment ℝ p₁ p₂) :
      x ∈ cone2dTrapezoid ν₁ ν₂ m a b ∧ inner ℝ x m = b := by
    rw [← htop] at hx
    exact hx
  have hb (x) (hx : x ∈ segment ℝ q₁ q₂) :
      x ∈ cone2dTrapezoid ν₁ ν₂ m a b ∧ inner ℝ x m = a := by
    rw [← hbot] at hx
    exact hx
  have htopcost : μ (segment ℝ p₁ p₂) ≤ ENNReal.ofReal (dist p₁ p₂) := by
    apply measure_segment_le_of_ae_eq_three_halfspaces_on_open
      (V := W ∩ {x | a < inner ℝ x m}) hμ hp h₁ h₂
      (show ‖-m‖ = 1 by simpa using hm) 0 0 (-b)
      (cone2d_segment_inter_hyperplane_left hp₁ hp₂)
      (cone2d_segment_inter_hyperplane_right hp₃ hp₄)
    · intro x hx
      change inner ℝ x (-m) = -b
      rw [inner_neg_right, (ht x hx).2]
    · exact hW.inter (isOpen_lt continuous_const (continuous_id.inner continuous_const))
    · intro x hx
      exact ⟨hQW (ht x hx).1, by change a < inner ℝ x m; rw [(ht x hx).2]; exact hab⟩
    · exact cone2d_sdiff_trapezoid_ae_upper hW.measurableSet hE
  have hbotcost : μ (segment ℝ q₁ q₂) ≤ ENNReal.ofReal (dist q₁ q₂) := by
    apply measure_segment_le_of_ae_eq_three_halfspaces_on_open
      (V := W ∩ {x | inner ℝ x m < b}) hμ hq h₁ h₂ hm 0 0 a
      (cone2d_segment_inter_hyperplane_left hq₁ hq₂)
      (cone2d_segment_inter_hyperplane_right hq₃ hq₄)
    · exact fun x hx => (hb x hx).2
    · exact hW.inter (isOpen_lt (continuous_id.inner continuous_const) continuous_const)
    · intro x hx
      exact ⟨hQW (hb x hx).1, by change inner ℝ x m < b; rw [(hb x hx).2]; exact hab⟩
    · exact cone2d_sdiff_trapezoid_ae_lower hW.measurableSet hE
  let O : Set (EuclideanSpace ℝ (Fin 2)) := W ∩ {x | a < inner ℝ x m ∧ inner ℝ x m < b}
  have hO : IsOpen O := by
    change IsOpen (W ∩ ({x | a < inner ℝ x m} ∩ {x | inner ℝ x m < b}))
    exact hW.inter ((isOpen_lt continuous_const (continuous_id.inner continuous_const)).inter
      (isOpen_lt (continuous_id.inner continuous_const) continuous_const))
  apply measure_le_two_chords hμ hO (cone2d_sdiff_trapezoid_ae_empty hW.measurableSet hE)
    _ htopcost hbotcost
  intro x hx
  by_cases ht' : inner ℝ x m = b
  · exact Or.inl (Or.inr (htop ▸ ⟨hx, ht'⟩))
  by_cases hb' : inner ℝ x m = a
  · exact Or.inr (hbot ▸ ⟨hx, hb'⟩)
  · exact Or.inl (Or.inl ⟨hQW hx, lt_of_le_of_ne hx.2.2.1 (Ne.symm hb'),
      lt_of_le_of_ne hx.2.2.2 ht'⟩)

/-- Near a compact radial segment, the other side of the wedge is inactive, so the old
perimeter is exactly its length. -/
theorem cone2d_radial_cost
    {E W : Set (EuclideanSpace ℝ (Fin 2))}
    {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμ : ∀ O, IsOpen O → perimeterIn E O = μ O)
    {p q ν₁ ν₂ : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q) (h₁ : ‖ν₁‖ = 1)
    (hW : IsOpen W) (hKW : segment ℝ p q ⊆ W)
    (hline : segment ℝ p q ⊆ {x | inner ℝ x ν₁ = 0})
    (hside : segment ℝ p q ⊆ {x | inner ℝ x ν₂ < 0})
    (hE : E =ᵐ[volume.restrict W]
      ({x | inner ℝ x ν₁ < 0} ∩ {x | inner ℝ x ν₂ < 0} : Set (EuclideanSpace ℝ (Fin 2)))) :
    μ (segment ℝ p q) = ENNReal.ofReal (dist p q) := by
  have hV : IsOpen (W ∩ {x | inner ℝ x ν₂ < 0}) :=
    hW.inter (isOpen_lt (continuous_id.inner continuous_const) continuous_const)
  have heq : E =ᵐ[volume.restrict (W ∩ {x | inner ℝ x ν₂ < 0})] {x | inner ℝ x ν₁ < 0} := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hE,
      ae_restrict_mem hV.measurableSet] with x hx hmem
    change (x ∈ E) = (inner ℝ x ν₁ < 0) at ⊢
    change (x ∈ E) = (inner ℝ x ν₁ < 0 ∧ inner ℝ x ν₂ < 0) at hx
    have hxside : inner ℝ x ν₂ < 0 := hmem.2
    simpa only [hxside, and_true] using hx
  rw [measure_eq_of_ae_eq_halfspace_on_open hμ (cone2d_isCompact_segment p q) hV
    (fun x hx => ⟨hKW hx, hside hx⟩) h₁ 0 heq,
    inter_eq_left.mpr hline, euclideanHausdorffMeasure_one_segment hpq]

/-- The two short-gap directions give explicit linear coordinates in the plane. -/
theorem cone2d_gap_decomposition {a b : ℝ} (hab : a < b) (hπ : b < a + Real.pi)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x = (-inner ℝ x (cone2dCircle (b + Real.pi / 2)) / Real.sin (b - a)) • cone2dCircle a +
      (-inner ℝ x (cone2dCircle (a - Real.pi / 2)) / Real.sin (b - a)) • cone2dCircle b := by
  have hd : Real.sin (b - a) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  ext i
  fin_cases i <;>
    simp [PiLp.inner_apply, Fin.sum_univ_two, Real.cos_add_pi_div_two,
      Real.sin_add_pi_div_two, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two] <;>
    field_simp <;> rw [Real.sin_sub] <;> ring

/-- The midpoint normal has the same positive height at the two endpoints. -/
theorem cone2d_gap_midpoint_inner (a b : ℝ) :
    inner ℝ (cone2dCircle a) (cone2dCircle ((a + b) / 2)) = Real.cos ((b - a) / 2) ∧
    inner ℝ (cone2dCircle b) (cone2dCircle ((a + b) / 2)) = Real.cos ((b - a) / 2) := by
  have h₁ := cone2dCircle_inner_smul 1 a ((a + b) / 2)
  have h₂ := cone2dCircle_inner_smul 1 b ((a + b) / 2)
  simp only [one_smul, one_mul] at h₁ h₂
  rw [show a - (a + b) / 2 = -((b - a) / 2) by ring, Real.cos_neg] at h₁
  rw [show b - (a + b) / 2 = (b - a) / 2 by ring] at h₂
  exact ⟨h₁, h₂⟩

/-- The four endpoint evaluations of the side normals. -/
theorem cone2d_gap_side_inner (a b : ℝ) :
    inner ℝ (cone2dCircle a) (cone2dCircle (a - Real.pi / 2)) = 0 ∧
    inner ℝ (cone2dCircle b) (cone2dCircle (a - Real.pi / 2)) = -Real.sin (b - a) ∧
    inner ℝ (cone2dCircle a) (cone2dCircle (b + Real.pi / 2)) = -Real.sin (b - a) ∧
    inner ℝ (cone2dCircle b) (cone2dCircle (b + Real.pi / 2)) = 0 := by
  have h₁ := cone2dCircle_inner_left_normal 1 a a
  have h₂ := cone2dCircle_inner_left_normal 1 b a
  have h₃ := cone2dCircle_inner_right_normal 1 a b
  have h₄ := cone2dCircle_inner_right_normal 1 b b
  simp only [one_smul, one_mul, neg_mul, sub_self, Real.sin_zero, neg_zero] at h₁ h₂ h₃ h₄
  rw [show a - b = -(b - a) by ring, Real.sin_neg] at h₃
  exact ⟨h₁, h₂, h₃, h₄⟩

/-- A short-gap trapezoid is precisely the set of positive endpoint combinations whose
coefficient sum lies between the truncation parameter and one. -/
theorem cone2d_mem_trapezoid_iff {a b ε : ℝ}
    (hab : a < b) (hπ : b < a + Real.pi) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ cone2dTrapezoid (cone2dCircle (a - Real.pi / 2))
        (cone2dCircle (b + Real.pi / 2)) (cone2dCircle ((a + b) / 2))
        (ε * Real.cos ((b - a) / 2)) (Real.cos ((b - a) / 2)) ↔
      ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ ε ≤ u + v ∧ u + v ≤ 1 ∧
        x = u • cone2dCircle a + v • cone2dCircle b := by
  have hd : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hh := (cone2d_short_gap_trig hab hπ).1
  obtain ⟨hm₁, hm₂⟩ := cone2d_gap_midpoint_inner a b
  obtain ⟨hn₁, hn₂, hn₃, hn₄⟩ := cone2d_gap_side_inner a b
  constructor
  · intro hx
    let u := -inner ℝ x (cone2dCircle (b + Real.pi / 2)) / Real.sin (b - a)
    let v := -inner ℝ x (cone2dCircle (a - Real.pi / 2)) / Real.sin (b - a)
    have heq : x = u • cone2dCircle a + v • cone2dCircle b := cone2d_gap_decomposition hab hπ x
    have hm : inner ℝ x (cone2dCircle ((a + b) / 2)) = (u + v) * Real.cos ((b - a) / 2) := by
      rw [heq, inner_add_left, real_inner_smul_left, real_inner_smul_left, hm₁, hm₂]
      ring
    refine ⟨u, v, div_nonneg (neg_nonneg.mpr hx.2.1) hd.le,
      div_nonneg (neg_nonneg.mpr hx.1) hd.le, ?_, ?_, heq⟩
    · have := hx.2.2.1
      rw [hm] at this
      nlinarith
    · have := hx.2.2.2
      rw [hm] at this
      nlinarith
  · rintro ⟨u, v, hu, hv, hlo, hhi, rfl⟩
    change _ ≤ 0 ∧ _ ≤ 0 ∧ _ ≤ _ ∧ _ ≤ _
    simp only [inner_add_left, real_inner_smul_left, hn₁, hn₂, hn₃, hn₄,
      hm₁, hm₂, mul_zero, zero_add, add_zero]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith

/-- The halfspace definition makes the trapezoid closed. -/
theorem cone2dTrapezoid_isClosed (ν₁ ν₂ m : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    IsClosed (cone2dTrapezoid ν₁ ν₂ m a b) := by
  change IsClosed ({x | inner ℝ x ν₁ ≤ 0} ∩ ({x | inner ℝ x ν₂ ≤ 0} ∩
    ({x | a ≤ inner ℝ x m} ∩ {x | inner ℝ x m ≤ b})))
  exact (isClosed_le (continuous_id.inner continuous_const) continuous_const).inter
    ((isClosed_le (continuous_id.inner continuous_const) continuous_const).inter
      ((isClosed_le continuous_const (continuous_id.inner continuous_const)).inter
        (isClosed_le (continuous_id.inner continuous_const) continuous_const)))

/-- The short-gap trapezoid lies in the closed unit ball. -/
theorem cone2d_trapezoid_subset_closedBall {a b ε : ℝ}
    (hab : a < b) (hπ : b < a + Real.pi) :
    cone2dTrapezoid (cone2dCircle (a - Real.pi / 2))
      (cone2dCircle (b + Real.pi / 2)) (cone2dCircle ((a + b) / 2))
      (ε * Real.cos ((b - a) / 2)) (Real.cos ((b - a) / 2)) ⊆ closedBall 0 1 := by
  intro x hx
  obtain ⟨u, v, hu, hv, hlo, hhi, rfl⟩ := (cone2d_mem_trapezoid_iff hab hπ x).mp hx
  rw [mem_closedBall, dist_zero_right]
  calc ‖u • cone2dCircle a + v • cone2dCircle b‖ ≤
      ‖u • cone2dCircle a‖ + ‖v • cone2dCircle b‖ := norm_add_le _ _
    _ = u + v := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu, abs_of_nonneg hv]
    _ ≤ 1 := hhi

/-- Compactness of the truncated short-gap wedge. -/
theorem cone2d_trapezoid_isCompact {a b ε : ℝ}
    (hab : a < b) (hπ : b < a + Real.pi) :
    IsCompact (cone2dTrapezoid (cone2dCircle (a - Real.pi / 2))
      (cone2dCircle (b + Real.pi / 2)) (cone2dCircle ((a + b) / 2))
      (ε * Real.cos ((b - a) / 2)) (Real.cos ((b - a) / 2))) :=
  (isCompact_closedBall 0 1).of_isClosed_subset (cone2dTrapezoid_isClosed _ _ _ _ _)
    (cone2d_trapezoid_subset_closedBall hab hπ)

/-- A nonzero nonnegative combination of two strictly negative values is strictly negative. -/
theorem cone2d_combination_neg {u v A B : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : 0 < u + v) (hA : A < 0) (hB : B < 0) : u * A + v * B < 0 := by
  have h₁ := mul_nonpos_of_nonneg_of_nonpos hu hA.le
  have h₂ := mul_nonpos_of_nonneg_of_nonpos hv hB.le
  rcases lt_or_eq_of_le hu with hu | rfl
  · have := mul_neg_of_pos_of_neg hu hA
    linarith
  · have hv' : 0 < v := by linarith
    have := mul_neg_of_pos_of_neg hv' hB
    linarith

/-- Positive truncation puts the entire trapezoid inside every slightly enlarged short wedge. -/
theorem cone2d_trapezoid_subset_widened_wedge {a b ε δ : ℝ}
    (hab : a < b) (hπ : b < a + Real.pi) (hε : 0 < ε) (hδ : 0 < δ)
    (hδπ : b + δ < (a - δ) + Real.pi) :
    cone2dTrapezoid (cone2dCircle (a - Real.pi / 2))
      (cone2dCircle (b + Real.pi / 2)) (cone2dCircle ((a + b) / 2))
      (ε * Real.cos ((b - a) / 2)) (Real.cos ((b - a) / 2)) ⊆
      {x | inner ℝ x (cone2dCircle (a - δ - Real.pi / 2)) < 0} ∩
        {x | inner ℝ x (cone2dCircle (b + δ + Real.pi / 2)) < 0} := by
  have hp (θ : ℝ) (hθ : θ ∈ Ioo (a - δ) (b + δ)) :
      cone2dCircle θ ∈
        ({x | inner ℝ x (cone2dCircle (a - δ - Real.pi / 2)) < 0} ∩
          {x | inner ℝ x (cone2dCircle (b + δ + Real.pi / 2)) < 0} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [cone2d_wedge_eq_polar (show a - δ < b + δ by linarith) hδπ]
    exact ⟨θ, hθ, 1, one_pos, by simp⟩
  have hpa := hp a ⟨by linarith, by linarith⟩
  have hpb := hp b ⟨by linarith, by linarith⟩
  intro x hx
  obtain ⟨u, v, hu, hv, hlo, hhi, rfl⟩ := (cone2d_mem_trapezoid_iff hab hπ x).mp hx
  change (inner ℝ (u • cone2dCircle a + v • cone2dCircle b)
      (cone2dCircle (a - δ - Real.pi / 2)) < 0) ∧
    (inner ℝ (u • cone2dCircle a + v • cone2dCircle b)
      (cone2dCircle (b + δ + Real.pi / 2)) < 0)
  simp only [inner_add_left, real_inner_smul_left]
  exact ⟨cone2d_combination_neg hu hv (hε.trans_le hlo) hpa.1 hpb.1,
    cone2d_combination_neg hu hv (hε.trans_le hlo) hpa.2 hpb.2⟩

/-- The outer cut of the short-gap trapezoid is its unit-radius chord. -/
theorem cone2d_trapezoid_top {a b ε : ℝ}
    (hab : a < b) (hπ : b < a + Real.pi) (hε : ε ≤ 1) :
    cone2dTrapezoid (cone2dCircle (a - Real.pi / 2))
      (cone2dCircle (b + Real.pi / 2)) (cone2dCircle ((a + b) / 2))
      (ε * Real.cos ((b - a) / 2)) (Real.cos ((b - a) / 2)) ∩
      {x | inner ℝ x (cone2dCircle ((a + b) / 2)) = Real.cos ((b - a) / 2)} =
        segment ℝ (cone2dCircle a) (cone2dCircle b) := by
  have hh := (cone2d_short_gap_trig hab hπ).1
  obtain ⟨hm₁, hm₂⟩ := cone2d_gap_midpoint_inner a b
  ext x
  constructor
  · rintro ⟨hx, hline⟩
    obtain ⟨u, v, hu, hv, hlo, hhi, heq⟩ := (cone2d_mem_trapezoid_iff hab hπ x).mp hx
    change inner ℝ x (cone2dCircle ((a + b) / 2)) = _ at hline
    rw [heq, inner_add_left, real_inner_smul_left, real_inner_smul_left, hm₁, hm₂] at hline
    exact ⟨u, v, hu, hv, by nlinarith, heq.symm⟩
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    constructor
    · exact (cone2d_mem_trapezoid_iff hab hπ _).mpr ⟨u, v, hu, hv, by linarith, huv.le, rfl⟩
    · change inner ℝ (u • cone2dCircle a + v • cone2dCircle b) _ = _
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hm₁, hm₂,
        ← add_mul, huv, one_mul]

/-- The inner cut is the chord between the two truncated ray endpoints. -/
theorem cone2d_trapezoid_bottom {a b ε : ℝ}
    (hab : a < b) (hπ : b < a + Real.pi) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    cone2dTrapezoid (cone2dCircle (a - Real.pi / 2))
      (cone2dCircle (b + Real.pi / 2)) (cone2dCircle ((a + b) / 2))
      (ε * Real.cos ((b - a) / 2)) (Real.cos ((b - a) / 2)) ∩
      {x | inner ℝ x (cone2dCircle ((a + b) / 2)) = ε * Real.cos ((b - a) / 2)} =
        segment ℝ (ε • cone2dCircle a) (ε • cone2dCircle b) := by
  have hh := (cone2d_short_gap_trig hab hπ).1
  obtain ⟨hm₁, hm₂⟩ := cone2d_gap_midpoint_inner a b
  ext x
  constructor
  · rintro ⟨hx, hline⟩
    obtain ⟨u, v, hu, hv, hlo, hhi, heq⟩ := (cone2d_mem_trapezoid_iff hab hπ x).mp hx
    change inner ℝ x (cone2dCircle ((a + b) / 2)) = _ at hline
    rw [heq, inner_add_left, real_inner_smul_left, real_inner_smul_left, hm₁, hm₂] at hline
    have huv : u + v = ε := by nlinarith
    refine ⟨u / ε, v / ε, div_nonneg hu hε.le, div_nonneg hv hε.le, ?_, ?_⟩
    · rw [← add_div, huv, div_self hε.ne']
    · rw [smul_smul, smul_smul, div_mul_cancel₀ _ hε.ne', div_mul_cancel₀ _ hε.ne']
      exact heq.symm
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    have hsum : u * ε + v * ε = ε := by rw [← add_mul, huv, one_mul]
    constructor
    · apply (cone2d_mem_trapezoid_iff hab hπ _).mpr
      exact ⟨u * ε, v * ε, mul_nonneg hu hε.le, mul_nonneg hv hε.le,
        hsum.ge, hsum.le.trans hε1, by rw [smul_smul, smul_smul]⟩
    · change inner ℝ (u • ε • cone2dCircle a + v • ε • cone2dCircle b) _ = _
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_left, hm₁, hm₂]
      nlinarith [congrArg (fun t => t * (ε * Real.cos ((b - a) / 2))) huv]

/-- Both radial sides belong to the trapezoid. -/
theorem cone2d_trapezoid_radial_subset {a b ε : ℝ}
    (hab : a < b) (hπ : b < a + Real.pi) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    segment ℝ (ε • cone2dCircle a) (cone2dCircle a) ⊆
      cone2dTrapezoid (cone2dCircle (a - Real.pi / 2))
        (cone2dCircle (b + Real.pi / 2)) (cone2dCircle ((a + b) / 2))
        (ε * Real.cos ((b - a) / 2)) (Real.cos ((b - a) / 2)) ∧
    segment ℝ (ε • cone2dCircle b) (cone2dCircle b) ⊆
      cone2dTrapezoid (cone2dCircle (a - Real.pi / 2))
        (cone2dCircle (b + Real.pi / 2)) (cone2dCircle ((a + b) / 2))
        (ε * Real.cos ((b - a) / 2)) (Real.cos ((b - a) / 2)) := by
  have hbds (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
      0 ≤ u * ε + v ∧ ε ≤ u * ε + v ∧ u * ε + v ≤ 1 := by
    have hu1 : u ≤ 1 := by linarith
    have hv1 : v ≤ 1 := by linarith
    constructor
    · positivity
    constructor <;> nlinarith
  constructor
  · rintro x ⟨u, v, hu, hv, huv, rfl⟩
    obtain ⟨h0, hlo, hhi⟩ := hbds u v hu hv huv
    apply (cone2d_mem_trapezoid_iff hab hπ _).mpr
    refine ⟨u * ε + v, 0, h0, le_rfl, by simpa using hlo, by simpa using hhi, ?_⟩
    rw [smul_smul, add_smul, zero_smul, add_zero]
  · rintro x ⟨u, v, hu, hv, huv, rfl⟩
    obtain ⟨h0, hlo, hhi⟩ := hbds u v hu hv huv
    apply (cone2d_mem_trapezoid_iff hab hπ _).mpr
    refine ⟨0, u * ε + v, le_rfl, h0, by simpa using hlo, by simpa using hhi, ?_⟩
    rw [smul_smul, add_smul, zero_smul, zero_add]

/-- A single short angular gap admits a compact truncated-chord removal with strictly smaller
perimeter. This statement is independent of which original phase occupies the gap. -/
theorem cone2d_gap_competitor
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hmE : NullMeasurableSet E volume)
    (hpE : HasLocallyFinitePerimeter E) {a b η : ℝ}
    (hab : a < b) (hπ : b < a + Real.pi) (hη : 0 < η)
    (hin : ∀ θ ∈ Ioo a b, ∀ r : ℝ, 0 < r → r • cone2dCircle θ ∈ E)
    (hleft : ∀ θ ∈ Ioo (a - η) a, ∀ r : ℝ, 0 < r → r • cone2dCircle θ ∉ E)
    (hright : ∀ θ ∈ Ioo b (b + η), ∀ r : ℝ, 0 < r → r • cone2dCircle θ ∉ E) :
    ∃ Q : Set (EuclideanSpace ℝ (Fin 2)), IsCompact Q ∧ Q ⊆ ball 0 2 ∧
      HasLocallyFinitePerimeter (E \ Q) ∧
        perimeterIn (E \ Q) (ball 0 2) < perimeterIn E (ball 0 2) := by
  let s := Real.sin ((b - a) / 2)
  let h := Real.cos ((b - a) / 2)
  let ε := (1 - s) / 4
  have htrig := cone2d_short_gap_trig hab hπ
  obtain ⟨hε, hε1, hsave⟩ := cone2d_chord_saving htrig.2.1.le htrig.2.2
  change 0 < ε at hε
  change ε < 1 at hε1
  change 2 * s * (1 + ε) < 2 * (1 - ε) at hsave
  let p₁ := cone2dCircle a
  let p₂ := cone2dCircle b
  let ν₁ := cone2dCircle (a - Real.pi / 2)
  let ν₂ := cone2dCircle (b + Real.pi / 2)
  let m := cone2dCircle ((a + b) / 2)
  let Q := cone2dTrapezoid ν₁ ν₂ m (ε * h) h
  obtain ⟨δ, hδ, hδη, hδπ, hEW⟩ := cone2d_gap_ae_wedge hab hπ hη hin hleft hright
  let W : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | inner ℝ x (cone2dCircle (a - δ - Real.pi / 2)) < 0} ∩
      {x | inner ℝ x (cone2dCircle (b + δ + Real.pi / 2)) < 0}
  have hW : IsOpen W :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).inter
      (isOpen_lt (continuous_id.inner continuous_const) continuous_const)
  have hQ : IsCompact Q := cone2d_trapezoid_isCompact hab hπ
  have hQball : Q ⊆ ball 0 2 := (cone2d_trapezoid_subset_closedBall hab hπ).trans
    (closedBall_subset_ball (by norm_num))
  have hQW : Q ⊆ W := cone2d_trapezoid_subset_widened_wedge hab hπ hε hδ hδπ
  have hn₁ : ‖ν₁‖ = 1 := cone2dCircle_norm _
  have hn₂ : ‖ν₂‖ = 1 := cone2dCircle_norm _
  have hnm : ‖m‖ = 1 := cone2dCircle_norm _
  obtain ⟨hp₁, hp₂, hp₃, hp₄⟩ := cone2d_gap_side_inner a b
  have hd : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith)
  have hp₂' : inner ℝ p₂ ν₁ < 0 := by rw [hp₂]; linarith
  have hp₃' : inner ℝ p₁ ν₂ < 0 := by rw [hp₃]; linarith
  have hq₁ : inner ℝ (ε • p₁) ν₁ = 0 := by rw [real_inner_smul_left, hp₁, mul_zero]
  have hq₂ : inner ℝ (ε • p₂) ν₁ < 0 := by
    rw [real_inner_smul_left]; exact mul_neg_of_pos_of_neg hε hp₂'
  have hq₃ : inner ℝ (ε • p₁) ν₂ < 0 := by
    rw [real_inner_smul_left]; exact mul_neg_of_pos_of_neg hε hp₃'
  have hq₄ : inner ℝ (ε • p₂) ν₂ = 0 := by rw [real_inner_smul_left, hp₄, mul_zero]
  have hpne : p₁ ≠ p₂ := by
    intro he
    have hzero : inner ℝ p₂ ν₁ = 0 := by rw [← he]; exact hp₁
    linarith
  have hqne : ε • p₁ ≠ ε • p₂ := fun he => hpne ((smul_right_injective _ hε.ne') he)
  have hrad₁ : ε • p₁ ≠ p₁ := by
    apply dist_pos.mp
    change 0 < dist (ε • cone2dCircle a) (cone2dCircle a)
    rw [cone2d_dist_radial a hε1.le]
    linarith
  have hrad₂ : ε • p₂ ≠ p₂ := by
    apply dist_pos.mp
    change 0 < dist (ε • cone2dCircle b) (cone2dCircle b)
    rw [cone2d_dist_radial b hε1.le]
    linarith
  obtain ⟨hs₁, hs₂⟩ := cone2d_trapezoid_radial_subset hab hπ hε.le hε1.le
  have hl₁ : segment ℝ (ε • p₁) p₁ ⊆ {x | inner ℝ x ν₁ = 0} :=
    cone2d_segment_hyperplane hq₁ hp₁
  have hl₂ : segment ℝ (ε • p₂) p₂ ⊆ {x | inner ℝ x ν₂ = 0} :=
    cone2d_segment_hyperplane hq₄ hp₄
  have hi₁ : segment ℝ (ε • p₁) p₁ ⊆ {x | inner ℝ x ν₂ < 0} :=
    cone2d_segment_halfspace hq₃ hp₃'
  have hi₂ : segment ℝ (ε • p₂) p₂ ⊆ {x | inner ℝ x ν₁ < 0} :=
    cone2d_segment_halfspace hq₂ hp₂'
  have hdisj : Disjoint (segment ℝ (ε • p₁) p₁) (segment ℝ (ε • p₂) p₂) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hzero : inner ℝ x ν₁ = 0 := hl₁ hx
    have hneg : inner ℝ x ν₁ < 0 := hi₂ hy
    linarith
  obtain ⟨μE, hμE⟩ := exists_perimeter_measure hmE
  obtain ⟨μG, hμG⟩ := exists_perimeter_measure (hmE.diff hQ.measurableSet.nullMeasurableSet)
  have hc₁ := cone2d_radial_cost hμE hrad₁ hn₁ hW (hs₁.trans hQW) hl₁ hi₁ hEW
  have hEW' : E =ᵐ[volume.restrict W]
      ({x | inner ℝ x ν₂ < 0} ∩ {x | inner ℝ x ν₁ < 0} : Set (EuclideanSpace ℝ (Fin 2))) := by
    filter_upwards [hEW] with x hx
    change (x ∈ E) = (inner ℝ x ν₁ < 0 ∧ inner ℝ x ν₂ < 0) at hx
    change (x ∈ E) = (inner ℝ x ν₂ < 0 ∧ inner ℝ x ν₁ < 0)
    exact hx.trans (propext and_comm)
  have hc₂ := cone2d_radial_cost hμE hrad₂ hn₂ hW (hs₂.trans hQW) hl₂ hi₂ hEW'
  have hcost : μG Q ≤ ENNReal.ofReal (dist p₁ p₂) + ENNReal.ofReal (dist (ε • p₁) (ε • p₂)) :=
    cone2d_trapezoid_cost (by nlinarith [htrig.1]) hn₁ hn₂ hnm hW hQW hEW
      hpne hqne (cone2d_trapezoid_top hab hπ hε1.le)
      (cone2d_trapezoid_bottom hab hπ hε hε1.le)
      hp₁ hp₂' hp₃' hp₄ hq₁ hq₂ hq₃ hq₄ hμG
  have hlength : dist p₁ p₂ + dist (ε • p₁) (ε • p₂) <
      dist (ε • p₁) p₁ + dist (ε • p₂) p₂ := by
    change dist (cone2dCircle a) (cone2dCircle b) +
      dist (ε • cone2dCircle a) (ε • cone2dCircle b) <
      dist (ε • cone2dCircle a) (cone2dCircle a) + dist (ε • cone2dCircle b) (cone2dCircle b)
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hε, cone2d_dist_chord hab hπ,
      cone2d_dist_radial a hε1.le, cone2d_dist_radial b hε1.le]
    change 2 * s + ε * (2 * s) < (1 - ε) + (1 - ε)
    nlinarith
  refine ⟨Q, hQ, hQball, ?_⟩
  exact perimeterIn_sdiff_lt_of_two_chords hpE hQ isOpen_ball
    (isCompact_closedBall 0 2 |>.of_isClosed_subset isClosed_closure closure_ball_subset_closedBall)
    hQball hμE hμG hs₁ hs₂ hdisj hc₁ hc₂ hcost hlength

/-- Blueprint `lem:cone-2d`. -/
theorem cone2d_halfplane {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : MeasurableSet C) (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (hnt : 0 < volume C ∧ 0 < volume Cᶜ) :
    ∃ μ : EuclideanSpace ℝ (Fin 2), ‖μ‖ = 1 ∧ densityOne C = {x | 0 < inner ℝ μ x} := by
  by_cases hlink : ∃ u : EuclideanSpace ℝ (Fin 2),
      frontier (densityOne C) ∩ sphere 0 1 ⊆ {u, -u}
  · obtain ⟨u, hu⟩ := hlink
    exact cone2d_halfplane_of_link_subset_antipodal hm hcone hnt u hu
  · obtain ⟨a, b, hab, hπ, ha, hb, hgap⟩ := cone2d_exists_short_gap
      (cone2d_link_finite hmin hcone) inter_subset_right hlink
    have hgap' : ∀ θ ∈ Ioo a b, cone2dCircle θ ∉ frontier (densityOne C) := by
      intro θ hθ hf
      exact hgap θ hθ ⟨hf, cone2dCircle_mem_sphere θ⟩
    obtain ⟨η, hη, hphase⟩ := cone2d_gap_phases_smul hmin hcone hab ha.1 hb.1 hgap'
    have hmD : NullMeasurableSet (densityOne C) volume :=
      (measurableSet_densityOne hm.nullMeasurableSet).nullMeasurableSet
    have hpD := cone2d_densityOne_locallyFinite hm.nullMeasurableSet
      (hmin 2 (by norm_num)).locallyFinite
    have hDC := densityOne_ae_eq (by norm_num : 0 < 2) hm.nullMeasurableSet
    rcases hphase with ⟨hin, hl, hr⟩ | ⟨hin, hl, hr⟩
    · obtain ⟨Q, hQ, hQball, hG, hsave⟩ := cone2d_gap_competitor hmD hpD hab hπ hη
        (fun θ hθ r hr => interior_subset (hin θ hθ r hr))
        (fun θ hθ r hr => interior_subset (hl θ hθ r hr))
        (fun θ hθ r hpos => interior_subset (hr θ hθ r hpos))
      exact (not_lt_of_ge (cone2d_no_sdiff_improvement hmin hDC hQ hQball hG) hsave).elim
    · have hpDc : HasLocallyFinitePerimeter (densityOne C)ᶜ := by
        intro U hU hcU
        rw [perimeterIn_compl hmD hU]
        exact hpD U hU hcU
      have hDCc : (densityOne C)ᶜ =ᵐ[volume] Cᶜ := by
        filter_upwards [hDC] with x hx
        change (x ∈ densityOne C) = (x ∈ C) at hx
        change (x ∉ densityOne C) = (x ∉ C)
        rw [hx]
      obtain ⟨Q, hQ, hQball, hG, hsave⟩ := cone2d_gap_competitor hmD.compl hpDc hab hπ hη
        (fun θ hθ r hr => interior_subset (hin θ hθ r hr))
        (fun θ hθ r hr hnot => hnot (interior_subset (hl θ hθ r hr)))
        (fun θ hθ r hpos hnot => hnot (interior_subset (hr θ hθ r hpos)))
      exact (not_lt_of_ge (cone2d_no_compl_sdiff_improvement hmin hDCc hQ hQball hG) hsave).elim

end LiquidDrop
