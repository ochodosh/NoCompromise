module

public import NoCompromise.Cones.TwoDim
public import NoCompromise.BV.Density

@[expose] public section

/-!
# BV profiles for planar cones

Partial progress toward blueprint `lem:cone-2d-link`. The canonical representative
has locally finite perimeter and admits binary BV profiles in every orthogonal
frame. Constant profile intervals generate sectors contained in the corresponding
interior phase. Frontier points on a positive-offset profile line must be jumps,
so good lines have finitely many frontier points on compact profile intervals.
Finiteness of the full unit-circle link and its even cardinality remain separate.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace LiquidDrop

/-- Passing to the density-one representative preserves local perimeter finiteness. -/
theorem cone2d_densityOne_locallyFinite
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : NullMeasurableSet C volume) (hp : HasLocallyFinitePerimeter C) :
    HasLocallyFinitePerimeter (densityOne C) := by
  intro U hU hcU
  rw [perimeterIn_congr_ae U (ae_restrict_of_ae (densityOne_ae_eq (by norm_num) hm))]
  exact hp U hU hcU

/-- A point on an affine line in a prescribed orthogonal frame. -/
def cone2dSlicePoint
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  e (graphAppendN (euclideanOneReal.symm a) t)

/-- The affine-line coordinates commute with simultaneous dilation of both coordinates. -/
theorem cone2dSlicePoint_smul
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (r a t : ℝ) :
    cone2dSlicePoint e (r * a) (r * t) = r • cone2dSlicePoint e a t := by
  have ha : euclideanOneReal.symm (r * a) = r • euclideanOneReal.symm a := by
    simpa only [smul_eq_mul] using euclideanOneReal.symm.map_smul r a
  simp only [cone2dSlicePoint, graphAppendN, ha, map_add, map_smul, smul_add, smul_smul]

/-- Exact conical symmetry gives exact equality of membership on rescaled lines. -/
theorem cone2dSlicePoint_mem_smul_iff
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r) (a t : ℝ) :
    cone2dSlicePoint e (r * a) (r * t) ∈ densityOne C ↔
      cone2dSlicePoint e a t ∈ densityOne C := by
  rw [cone2dSlicePoint_smul]
  exact IsDilationInvariant.smul_mem_iff hcone hr

/-- Almost every affine line in any prescribed orthogonal frame has binary BV
profiles for the density-one representative, with finite jumps on compact intervals. -/
theorem cone2d_ae_binary_profile
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : NullMeasurableSet C volume) (hp : HasLocallyFinitePerimeter C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) :
    ∀ᵐ c : ℝ, ∀ a b : ℝ, ∃ g : ℝ → ℝ,
      BoundedVariationOn g univ ∧
      (∀ t, ContinuousWithinAt g (Iic t) t) ∧
      (fun t => (densityOne C).indicator (fun _ => (1 : ℝ)) (cone2dSlicePoint e c t))
        =ᵐ[volume.restrict (Ioo a b)] g ∧
      (∀ t ∈ Ioo a b, g t ∈ ({0, 1} : Set ℝ)) ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b →
        {t ∈ K | oneDimensionalJump g t ≠ 0}.Finite := by
  classical
  have hD := cone2d_densityOne_locallyFinite hm hp
  have hmD : NullMeasurableSet (densityOne C) volume :=
    (measurableSet_densityOne hm).nullMeasurableSet
  have hs := (hD.isLocallyBVOn_indicator hmD univ).ae_lineSlice_frame e
  have hs' := euclideanOneReal.symm.measurePreserving.quasiMeasurePreserving.ae hs
  filter_upwards [hs'] with c hc
  intro a b
  let f : EuclideanSpace ℝ (Fin 1) → ℝ := fun t =>
    (densityOne C).indicator (fun _ => (1 : ℝ)) (cone2dSlicePoint e c (t 0))
  have hf : IsLocallyBVOn f univ := by
    simpa only [f, cone2dSlicePoint, graphAppendN, map_add, map_smul] using hc
  have hb : ∀ᵐ t : ℝ, f (euclideanOneReal.symm t) ∈ ({0, 1} : Set ℝ) :=
    ae_of_all _ fun t => by
      dsimp [f]
      by_cases h : cone2dSlicePoint e c t ∈ densityOne C <;>
        simp [h]
  obtain ⟨g, hg, hgc, heq, hgb, _⟩ := hf.exists_binary_representative_Ioo hb a b
  refine ⟨g, hg, hgc, ?_, hgb, fun K hK hKU => ?_⟩
  · simpa only [Function.comp_def, f, euclideanOneReal_symm_apply] using heq
  · exact finite_oneDimensionalJump_of_binary_ae hg hgc
      (ae_restrict_of_forall_mem measurableSet_Ioo hgb) hK hKU


/-- A good profile line can be chosen in any nonempty open interval of offsets.
In particular one can choose it on either side of the origin. -/
theorem cone2d_exists_binary_profile
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : NullMeasurableSet C volume) (hp : HasLocallyFinitePerimeter C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {u v : ℝ} (huv : u < v) (a b : ℝ) :
    ∃ c ∈ Ioo u v, ∃ g : ℝ → ℝ,
      BoundedVariationOn g univ ∧
      (∀ t, ContinuousWithinAt g (Iic t) t) ∧
      (fun t => (densityOne C).indicator (fun _ => (1 : ℝ)) (cone2dSlicePoint e c t))
        =ᵐ[volume.restrict (Ioo a b)] g ∧
      (∀ t ∈ Ioo a b, g t ∈ ({0, 1} : Set ℝ)) ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b →
        {t ∈ K | oneDimensionalJump g t ≠ 0}.Finite := by
  have hvol : volume (Ioo u v) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv))
  obtain ⟨c, hc, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
    (ae_restrict_of_ae (cone2d_ae_binary_profile hm hp e))
  exact ⟨c, hc, hgood a b⟩

/-- For a conical representative, the exceptional null set of profile parameters
can be chosen independently of the positive radial coordinate. -/
theorem cone2d_profile_ae_all_radii
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c a b : ℝ} {g : ℝ → ℝ}
    (heq : (fun t => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c t)) =ᵐ[volume.restrict (Ioo a b)] g) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ r : ℝ, 0 < r →
      (densityOne C).indicator (fun _ => (1 : ℝ))
        (cone2dSlicePoint e (r * c) (r * t)) = g t := by
  classical
  filter_upwards [heq] with t ht
  intro r hr
  rw [← ht]
  have hmem := cone2dSlicePoint_mem_smul_iff hcone e hr c t
  by_cases h : cone2dSlicePoint e c t ∈ densityOne C
  · simp only [indicator_of_mem h, indicator_of_mem (hmem.mpr h)]
  · simp only [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.mp h'))]

/-- At every nonjump point of a binary left-continuous BV profile, the profile is
constant on a neighborhood. This is the local input for identifying open sectors. -/
theorem cone2d_profile_locally_constant
    {g : ℝ → ℝ} {a b t : ℝ}
    (hg : BoundedVariationOn g univ)
    (hc : ∀ s, ContinuousWithinAt g (Iic s) s)
    (hb : ∀ s ∈ Ioo a b, g s ∈ ({0, 1} : Set ℝ))
    (ht : t ∈ Ioo a b) (hj : oneDimensionalJump g t = 0) :
    ∃ δ > 0, ball t δ ⊆ Ioo a b ∧ ∀ s ∈ ball t δ, g s = g t := by
  have hcont : ContinuousAt g t := (oneDimensionalJump_eq_zero_iff hg (hc t)).mp hj
  have hbinary : ∀ᶠ s in 𝓝 t, g s ∈ ({0, 1} : Set ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hb s hs
  have hconst := eventually_eq_of_tendsto_binary hbinary hcont
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (isOpen_Ioo.mem_nhds ht) hconst)
  exact ⟨δ, hδ, fun s hs => (hball hs).1, fun s hs => (hball hs).2⟩


/-- A nonjump parameter gives a sector on which the cone indicator is constant
for almost every angular parameter, simultaneously at every positive radius. -/
theorem cone2d_profile_sector_constancy
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c a b t : ℝ} {g : ℝ → ℝ}
    (hg : BoundedVariationOn g univ)
    (hc : ∀ s, ContinuousWithinAt g (Iic s) s)
    (hb : ∀ s ∈ Ioo a b, g s ∈ ({0, 1} : Set ℝ))
    (heq : (fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo a b)] g)
    (ht : t ∈ Ioo a b) (hj : oneDimensionalJump g t = 0) :
    ∃ δ > 0, ball t δ ⊆ Ioo a b ∧
      ∀ᵐ s ∂volume.restrict (ball t δ), ∀ r : ℝ, 0 < r →
        (densityOne C).indicator (fun _ => (1 : ℝ))
          (cone2dSlicePoint e (r * c) (r * s)) = g t := by
  obtain ⟨δ, hδ, hsub, hconst⟩ := cone2d_profile_locally_constant hg hc hb ht hj
  refine ⟨δ, hδ, hsub, ?_⟩
  have he := ae_restrict_of_ae_restrict_of_subset hsub
    (cone2d_profile_ae_all_radii hcone e heq)
  filter_upwards [he, ae_restrict_mem measurableSet_ball] with s hs hball
  intro r hr
  exact (hs r hr).trans (hconst s hball)

/-- Rescaling the profile parameter transports an almost-everywhere profile to
any positive dilation of its base line. The interval endpoints scale as well. -/
theorem cone2d_profile_transport
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c a b r : ℝ} (hr : 0 < r) {g : ℝ → ℝ}
    (heq : (fun t => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c t)) =ᵐ[volume.restrict (Ioo a b)] g) :
    (fun t => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e (c / r) t))
        =ᵐ[volume.restrict (Ioo (a / r) (b / r))] (fun t => g (r * t)) := by
  classical
  have hmaps : MapsTo (fun t : ℝ => r • t) (Ioo (a / r) (b / r)) (Ioo a b) := by
    intro t ht
    simp only [mem_Ioo, smul_eq_mul] at *
    constructor
    · nlinarith [(div_lt_iff₀ hr).mp ht.1]
    · nlinarith [(lt_div_iff₀ hr).mp ht.2]
  have heq' := ((Measure.quasiMeasurePreserving_smul volume hr.ne').restrict hmaps).ae heq
  filter_upwards [heq'] with t ht
  simp only [smul_eq_mul] at ht
  rw [← ht]
  have hmem := cone2dSlicePoint_mem_smul_iff hcone e hr (c / r) t
  have hrc : r * (c / r) = c := by field_simp
  rw [hrc] at hmem
  by_cases h : cone2dSlicePoint e (c / r) t ∈ densityOne C
  · simp only [indicator_of_mem h, indicator_of_mem (hmem.mpr h)]
  · simp only [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.mp h'))]

/-- The BV part of the planar cone argument: on each compact profile interval
there are finitely many exceptional parameters; elsewhere the binary profile is
locally constant. Its agreement with the canonical cone holds almost everywhere
with an exceptional set independent of the radial coordinate.

This statement does not yet identify the exceptional parameters with the
intersection of the topological frontier and the unit circle. -/
theorem cone2d_exists_finite_sector_profile
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {u v : ℝ} (huv : u < v) (a b : ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hKab : K ⊆ Ioo a b) :
    ∃ c ∈ Ioo u v, ∃ g : ℝ → ℝ, ∃ J : Set ℝ,
      J.Finite ∧ J ⊆ K ∧
      (∀ t ∈ Ioo a b, g t ∈ ({0, 1} : Set ℝ)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), ∀ r : ℝ, 0 < r →
        (densityOne C).indicator (fun _ => (1 : ℝ))
          (cone2dSlicePoint e (r * c) (r * t)) = g t) ∧
      ∀ t ∈ K \ J, ∃ δ > 0,
        ball t δ ⊆ Ioo a b ∧ ∀ s ∈ ball t δ, g s = g t := by
  have h1 := hmin 1 (by norm_num)
  obtain ⟨c, hc, g, hg, hgc, heq, hgb, hfin⟩ :=
    cone2d_exists_binary_profile h1.nullMeasurable h1.locallyFinite e huv a b
  refine ⟨c, hc, g, {t ∈ K | oneDimensionalJump g t ≠ 0},
    hfin K hK hKab, fun _ ht => ht.1, hgb,
    cone2d_profile_ae_all_radii hcone e heq, ?_⟩
  intro t ht
  have hj : oneDimensionalJump g t = 0 := by
    by_contra hj
    exact ht.2 ⟨ht.1, hj⟩
  exact cone2d_profile_locally_constant hg hgc hgb (hKab ht.1) hj

/-- The open sector described by a positive affine offset and an interval of slopes. -/
def cone2dOpenSector
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (c a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | 0 < e.symm x 0 ∧ a * e.symm x 0 < c * e.symm x 1 ∧
    c * e.symm x 1 < b * e.symm x 0}

theorem cone2dOpenSector_isOpen
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (c a b : ℝ) : IsOpen (cone2dOpenSector e c a b) := by
  have h0 : Continuous (fun x => e.symm x 0) :=
    (EuclideanSpace.proj (0 : Fin 2)).continuous.comp e.symm.continuous
  have h1 : Continuous (fun x => e.symm x 1) :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous.comp e.symm.continuous
  exact (isOpen_lt continuous_const h0).inter
    ((isOpen_lt (continuous_const.mul h0) (continuous_const.mul h1)).inter
      (isOpen_lt (continuous_const.mul h1) (continuous_const.mul h0)))

/-- Every positive dilation of the specified open profile interval lies in the sector. -/
theorem cone2d_smul_mem_openSector
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c a b r t : ℝ} (hc : 0 < c) (hr : 0 < r) (ht : t ∈ Ioo a b) :
    r • cone2dSlicePoint e c t ∈ cone2dOpenSector e c a b := by
  rw [← cone2dSlicePoint_smul]
  change 0 < e.symm (cone2dSlicePoint e (r * c) (r * t)) 0 ∧ _
  simp only [cone2dSlicePoint, LinearIsometryEquiv.symm_apply_apply]
  change 0 < graphAppendN (euclideanOneReal.symm (r * c)) (r * t) (0 : Fin 1).castSucc ∧
    a * graphAppendN (euclideanOneReal.symm (r * c)) (r * t) (0 : Fin 1).castSucc <
      c * graphAppendN (euclideanOneReal.symm (r * c)) (r * t) (Fin.last 1) ∧
    c * graphAppendN (euclideanOneReal.symm (r * c)) (r * t) (Fin.last 1) <
      b * graphAppendN (euclideanOneReal.symm (r * c)) (r * t) (0 : Fin 1).castSucc
  simp only [graphAppendN_castSucc, graphAppendN_last, euclideanOneReal_symm_apply]
  refine ⟨mul_pos hr hc, ?_, ?_⟩
  · nlinarith [mul_lt_mul_of_pos_left ht.1 (mul_pos hr hc)]
  · nlinarith [mul_lt_mul_of_pos_left ht.2 (mul_pos hr hc)]

/-- Fubini upgrades constancy on a single profile interval to ambient almost-everywhere
constancy on its open sector. No perimeter or minimality assumption is needed. -/
theorem cone2d_ae_constant_on_openSector
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : NullMeasurableSet C volume)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c a b k : ℝ} (hc : 0 < c)
    (heq : (fun t => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c t)) =ᵐ[volume.restrict (Ioo a b)] (fun _ => k)) :
    ∀ᵐ x ∂volume, x ∈ cone2dOpenSector e c a b →
      (densityOne C).indicator (fun _ => (1 : ℝ)) x = k := by
  classical
  have hcoords (d t : ℝ) :
      cone2dSlicePoint e d t ∈ cone2dOpenSector e c a b ↔
        0 < d ∧ a * d < c * t ∧ c * t < b * d := by
    simp [cone2dOpenSector, cone2dSlicePoint, graphAppendN, graphBaseN]
  have hline (d : ℝ) : ∀ᵐ t ∂volume,
      cone2dSlicePoint e d t ∈ cone2dOpenSector e c a b →
        (densityOne C).indicator (fun _ => (1 : ℝ)) (cone2dSlicePoint e d t) = k := by
    by_cases hd : 0 < d
    · have hr : 0 < c / d := div_pos hc hd
      have hcd : c / (c / d) = d := by field_simp
      have ht := cone2d_profile_transport hcone e hr heq
      rw [hcd] at ht
      have ht' := (ae_restrict_iff' measurableSet_Ioo).mp ht
      filter_upwards [ht'] with t hgood hmem
      obtain ⟨_, ha, hb⟩ := (hcoords d t).mp hmem
      apply hgood
      constructor
      · apply (div_lt_iff₀ hr).mpr
        rw [← mul_div_assoc]
        exact (lt_div_iff₀ hd).mpr (by nlinarith)
      · apply (lt_div_iff₀ hr).mpr
        rw [← mul_div_assoc]
        exact (div_lt_iff₀ hd).mpr (by nlinarith)
    · exact ae_of_all _ fun t ht => (hd ((hcoords d t).mp ht).1).elim
  have hmap : MeasurePreserving (fun p : ℝ × ℝ => cone2dSlicePoint e p.1 p.2)
      (volume.prod volume) volume := by
    simpa only [Function.comp_def, Prod.map_apply', lineCoordinateEquiv_symm_apply,
      euclideanOneReal_symm_apply, cone2dSlicePoint] using
      e.measurePreserving.comp
        (((lineCoordinateEquiv_measurePreserving 1).symm (lineCoordinateEquiv 1)).comp
          (euclideanOneReal.symm.measurePreserving.prod euclideanOneReal.symm.measurePreserving))
  have hmi : Measurable ((densityOne C).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (measurableSet_densityOne hm)
  have hP : MeasurableSet {x | x ∈ cone2dOpenSector e c a b →
      (densityOne C).indicator (fun _ => (1 : ℝ)) x = k} :=
    (cone2dOpenSector_isOpen e c a b).measurableSet.imp
      (measurableSet_eq_fun hmi measurable_const)
  have hp := (Measure.ae_prod_iff_ae_ae (hP.preimage hmap.measurable)).mpr
    (ae_of_all volume hline)
  have h := (ae_map_iff hmap.aemeasurable hP).mpr hp
  rwa [hmap.map_eq] at h

/-- An open region occupied almost everywhere by one phase is contained in the
interior of the corresponding canonical phase. -/
theorem cone2d_open_ae_phase_interior
    {C U : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : NullMeasurableSet C volume) (hU : IsOpen U) {k : ℝ}
    (heq : ∀ᵐ x ∂volume, x ∈ U →
      (densityOne C).indicator (fun _ => (1 : ℝ)) x = k) :
    (k = 1 → U ⊆ interior (densityOne C)) ∧
      (k = 0 → U ⊆ interior ((densityOne C)ᶜ)) := by
  classical
  have hDC := densityOne_ae_eq (by norm_num : 0 < 2) hm
  constructor
  · rintro rfl
    apply interior_maximal ?_ hU
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
    change Tendsto (densityRatio C x) (𝓝[>] (0 : ℝ)) (𝓝 1)
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds hδ)] with r hr hrd
    have hsub : ball x r ⊆ U := (ball_subset_ball hrd.le).trans hball
    have hset : (C ∩ ball x r : Set (EuclideanSpace ℝ (Fin 2))) =ᵐ[volume] ball x r := by
      filter_upwards [heq, hDC] with y hy hCy
      apply propext
      constructor
      · exact And.right
      · intro hyb
        refine ⟨?_, hyb⟩
        have hyD : y ∈ densityOne C := by
          by_contra hno
          have h := hy (hsub hyb)
          simp [hno] at h
        exact (Iff.of_eq hCy).mp hyD
    simp only [densityRatio, measure_congr hset]
    exact (div_self ((ENNReal.toReal_pos (measure_ball_pos volume x hr).ne'
      measure_ball_lt_top.ne).ne')).symm
  · rintro rfl
    apply interior_maximal ?_ hU
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
    have hz : x ∈ densityZero C := by
      change Tendsto (densityRatio C x) (𝓝[>] (0 : ℝ)) (𝓝 0)
      apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hδ)] with r hrd
      have hsub : ball x r ⊆ U := (ball_subset_ball hrd.le).trans hball
      have hset : (C ∩ ball x r : Set (EuclideanSpace ℝ (Fin 2))) =ᵐ[volume]
          (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        filter_upwards [heq, hDC] with y hy hCy
        apply propext
        change (y ∈ C ∧ y ∈ ball x r) ↔ False
        refine ⟨?_, False.elim⟩
        rintro ⟨hyC, hyb⟩
        have hyD : y ∈ densityOne C := (Iff.of_eq hCy).mpr hyC
        have h := hy (hsub hyb)
        simp [hyD] at h
      simp only [densityRatio, measure_congr hset, measure_empty,
        ENNReal.toReal_zero, zero_div]
    exact fun hxD => disjoint_left.mp (disjoint_densityZero_densityOne C) hz hxD

/-- The sector lemma: an almost-everywhere constant line interval determines
the interior phase at every positive dilation of every point of that interval. -/
theorem cone2d_sector_interior
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : NullMeasurableSet C volume)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c a b k : ℝ} (hc : 0 < c)
    (heq : (fun t => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c t)) =ᵐ[volume.restrict (Ioo a b)] (fun _ => k)) :
    (k = 1 → ∀ r : ℝ, 0 < r → ∀ t ∈ Ioo a b,
      r • cone2dSlicePoint e c t ∈ interior (densityOne C)) ∧
    (k = 0 → ∀ r : ℝ, 0 < r → ∀ t ∈ Ioo a b,
      r • cone2dSlicePoint e c t ∈ interior ((densityOne C)ᶜ)) := by
  have h := cone2d_open_ae_phase_interior hm (cone2dOpenSector_isOpen e c a b)
    (cone2d_ae_constant_on_openSector hm hcone e hc heq)
  exact ⟨fun hk r hr t ht => h.1 hk (cone2d_smul_mem_openSector e hc hr ht),
    fun hk r hr t ht => h.2 hk (cone2d_smul_mem_openSector e hc hr ht)⟩

/-- No point of a sector with an almost-everywhere constant profile lies on the
frontier. The constant is automatically binary when the interval is nonempty. -/
theorem cone2d_sector_not_mem_frontier
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : NullMeasurableSet C volume)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c a b k r t : ℝ} (hc : 0 < c)
    (heq : (fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo a b)] (fun _ => k))
    (hr : 0 < r) (ht : t ∈ Ioo a b) :
    r • cone2dSlicePoint e c t ∉ frontier (densityOne C) := by
  classical
  have hvol : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (ht.1.trans ht.2)))
  obtain ⟨s, _, hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol heq
  have hphase := cone2d_sector_interior hm hcone e hc heq
  by_cases hmem : cone2dSlicePoint e c s ∈ densityOne C
  · have hk : k = 1 := by simpa [hmem] using hs.symm
    exact fun hf => disjoint_left.mp disjoint_interior_frontier
      (hphase.1 hk r hr t ht) hf
  · have hk : k = 0 := by simpa [hmem] using hs.symm
    have hn : r • cone2dSlicePoint e c t ∉ frontier ((densityOne C)ᶜ) :=
      fun hf => disjoint_left.mp disjoint_interior_frontier (hphase.2 hk r hr t ht) hf
    simpa only [frontier_compl] using hn

/-- Every frontier point on a positive-offset profile line is a jump of its
left-continuous binary BV representative. -/
theorem cone2d_frontier_profile_jump
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : NullMeasurableSet C volume)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c a b t : ℝ} {g : ℝ → ℝ} (hc : 0 < c)
    (hg : BoundedVariationOn g univ)
    (hgc : ∀ s, ContinuousWithinAt g (Iic s) s)
    (hgb : ∀ s ∈ Ioo a b, g s ∈ ({0, 1} : Set ℝ))
    (heq : (fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo a b)] g)
    (ht : t ∈ Ioo a b) (hf : cone2dSlicePoint e c t ∈ frontier (densityOne C)) :
    oneDimensionalJump g t ≠ 0 := by
  intro hj
  obtain ⟨δ, hδ, hsub, hconst⟩ := cone2d_profile_locally_constant hg hgc hgb ht hj
  have heq' : (fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (ball t δ)] (fun _ => g t) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub heq,
      ae_restrict_mem measurableSet_ball] with s hs hsb
    exact hs.trans (hconst s hsb)
  rw [Real.ball_eq_Ioo] at heq'
  have ht' : t ∈ Ioo (t - δ) (t + δ) := by constructor <;> linarith
  have hn := cone2d_sector_not_mem_frontier hm hcone e hc heq'
    (r := 1) (by norm_num) ht'
  exact hn (by simpa only [one_smul] using hf)

/-- A positive-offset line with finitely many actual frontier points on any
specified compact profile interval can be chosen in every orthogonal frame. -/
theorem cone2d_exists_finite_frontier_profile
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (K : Set ℝ) (hK : IsCompact K) (hKab : K ⊆ Ioo a b) :
    ∃ c ∈ Ioo (1 : ℝ) 2,
      {t ∈ K | cone2dSlicePoint e c t ∈ frontier (densityOne C)}.Finite := by
  have h1 := hmin 1 (by norm_num)
  obtain ⟨c, hc, g, hg, hgc, heq, hgb, hfin⟩ :=
    cone2d_exists_binary_profile h1.nullMeasurable h1.locallyFinite e
      (by norm_num : (1 : ℝ) < 2) a b
  refine ⟨c, hc, (hfin K hK hKab).subset ?_⟩
  intro t ht
  exact ⟨ht.1, cone2d_frontier_profile_jump h1.nullMeasurable hcone e
    (lt_trans zero_lt_one hc.1) hg hgc hgb heq (hKab ht.1) ht.2⟩

end LiquidDrop

namespace LiquidDrop

/-- Central projection of a point to a nonzero-offset profile line. -/
theorem cone2dSlicePoint_project
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (c : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (hu : e.symm u 0 ≠ 0) :
    cone2dSlicePoint e c (c * e.symm u 1 / e.symm u 0) =
      (c / e.symm u 0) • u := by
  apply e.symm.injective
  simp only [cone2dSlicePoint, LinearIsometryEquiv.symm_apply_apply, map_smul]
  ext i
  fin_cases i
  · change graphAppendN (euclideanOneReal.symm c) _ (0 : Fin 1).castSucc = _
    rw [graphAppendN_castSucc, euclideanOneReal_symm_apply]
    change c = (c / e.symm u 0) * e.symm u 0
    field_simp
  · change graphAppendN (euclideanOneReal.symm c) _ (Fin.last 1) = _
    rw [graphAppendN_last]
    change c * e.symm u 1 / e.symm u 0 = (c / e.symm u 0) * e.symm u 1
    ring

/-- The part of the unit-circle link facing any fixed orthogonal frame is finite. -/
theorem cone2d_link_arc_finite {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) :
    {u ∈ frontier (densityOne C) ∩ Metric.sphere 0 1 |
      |e.symm u 1| ≤ e.symm u 0}.Finite := by
  obtain ⟨c, hc, hfin⟩ := cone2d_exists_finite_frontier_profile hmin hcone e
    (-3) 3 (Icc (-2) 2) isCompact_Icc (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hc0 : 0 < c := by linarith [hc.1]
  apply (hfin.image (fun t => ‖cone2dSlicePoint e c t‖⁻¹ • cone2dSlicePoint e c t)).subset
  intro u hu
  have hn : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hu.1.2
  have he : (e.symm u 0)^2 + (e.symm u 1)^2 = 1 := by
    have hh := EuclideanSpace.real_norm_sq_eq (e.symm u)
    simpa [Fin.sum_univ_two, hn] using hh.symm
  have hpos : 0 < e.symm u 0 := by
    have hab := abs_nonneg (e.symm u 1)
    have hb := abs_le.mp (hu.2.trans (le_refl _))
    by_contra hh
    have hz : e.symm u 0 = 0 := by linarith [hu.2]
    have hz' : e.symm u 1 = 0 := by linarith [hb.1, hb.2]
    rw [hz, hz'] at he
    norm_num at he
  have ht : c * e.symm u 1 / e.symm u 0 ∈ Icc (-2 : ℝ) 2 := by
    have hb := abs_le.mp hu.2
    constructor
    · apply (le_div_iff₀ hpos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hb.1 hc0.le,
        mul_le_mul_of_nonneg_right hc.2.le hpos.le]
    · apply (div_le_iff₀ hpos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hb.2 hc0.le,
        mul_le_mul_of_nonneg_right hc.2.le hpos.le]
  have hp := cone2dSlicePoint_project e c u hpos.ne'
  refine ⟨c * e.symm u 1 / e.symm u 0, ⟨ht, ?_⟩, ?_⟩
  · rw [hp]
    exact (IsDilationInvariant.frontier hcone).smul_mem (div_pos hc0 hpos) hu.1.1
  · dsimp only
    rw [hp, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hc0 hpos), hn,
      mul_one, smul_smul, inv_mul_cancel₀ (div_pos hc0 hpos).ne', one_smul]

end LiquidDrop

namespace LiquidDrop

/-- The canonical frontier of a locally perimeter-minimizing planar cone has a
finite intersection with the unit circle. -/
theorem cone2d_link_finite {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C) :
    (frontier (densityOne C) ∩ Metric.sphere 0 1).Finite := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)
  have h0 : {u ∈ frontier (densityOne C) ∩ Metric.sphere 0 1 |
      |u 1| ≤ u 0}.Finite := by
    exact cone2d_link_arc_finite hmin hcone (LinearIsometryEquiv.refl ℝ _)
  have h1 : {u ∈ frontier (densityOne C) ∩ Metric.sphere 0 1 |
      |u 1| ≤ -u 0}.Finite := by
    simpa using cone2d_link_arc_finite hmin hcone (LinearIsometryEquiv.neg ℝ)
  have h2 : {u ∈ frontier (densityOne C) ∩ Metric.sphere 0 1 |
      |u 0| ≤ u 1}.Finite := by
    simpa [e, Equiv.piCongrLeft'] using cone2d_link_arc_finite hmin hcone e
  have h3 : {u ∈ frontier (densityOne C) ∩ Metric.sphere 0 1 |
      |u 0| ≤ -u 1}.Finite := by
    simpa [e, Equiv.piCongrLeft'] using
      cone2d_link_arc_finite hmin hcone (e.trans (LinearIsometryEquiv.neg ℝ))
  apply ((h0.union h1).union (h2.union h3)).subset
  intro u hu
  rcases le_total |u 1| |u 0| with hh | hh
  · by_cases hx : 0 ≤ u 0
    · exact Or.inl (Or.inl ⟨hu, by simpa [abs_of_nonneg hx] using hh⟩)
    · exact Or.inl (Or.inr ⟨hu, by simpa [abs_of_neg (lt_of_not_ge hx)] using hh⟩)
  · by_cases hy : 0 ≤ u 1
    · exact Or.inr (Or.inl ⟨hu, by simpa [abs_of_nonneg hy] using hh⟩)
    · exact Or.inr (Or.inr ⟨hu, by simpa [abs_of_neg (lt_of_not_ge hy)] using hh⟩)

end LiquidDrop

namespace LiquidDrop

/-- Adjacent constant profile intervals at a frontier ray have different phases.
The intervals are open, so no assumption is made about the value on the ray itself.
Positive dilations of these intervals are the adjacent open sectors. -/
theorem cone2d_adjacent_profile_phases_ne
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : NullMeasurableSet C volume)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c a t b kₗ kᵣ : ℝ} (hc : 0 < c) (hat : a < t) (htb : t < b)
    (hl : (fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo a t)] (fun _ => kₗ))
    (hr : (fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo t b)] (fun _ => kᵣ))
    (hf : cone2dSlicePoint e c t ∈ frontier (densityOne C)) :
    kₗ ≠ kᵣ := by
  intro hk
  have hl' := (ae_restrict_iff' measurableSet_Ioo).mp hl
  have hr' := (ae_restrict_iff' measurableSet_Ioo).mp hr
  have heq : (fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo a b)] (fun _ => kₗ) := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hl', hr', ((volume : Measure ℝ).ae_ne t)]
      with s hsl hsr hst hs
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · exact hsl ⟨hs.1, hlt⟩
    · exact (hsr ⟨hgt, hs.2⟩).trans hk.symm
  have hn := cone2d_sector_not_mem_frontier hm hcone e hc heq
    (r := 1) (by norm_num) ⟨hat, htb⟩
  exact hn (by simpa only [one_smul] using hf)

end LiquidDrop

namespace LiquidDrop

/-- A frontier point of a good binary BV profile has constant, different binary
phases on its two adjacent open intervals. Via `cone2d_sector_interior`, these
intervals generate open sectors in the respective canonical interior phases. -/
theorem cone2d_frontier_adjacent_profile_phases
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : NullMeasurableSet C volume)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c a b t : ℝ} {g : ℝ → ℝ} (hc : 0 < c)
    (hg : BoundedVariationOn g univ)
    (hgc : ∀ s, ContinuousWithinAt g (Iic s) s)
    (hgb : ∀ s ∈ Ioo a b, g s ∈ ({0, 1} : Set ℝ))
    (heq : (fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo a b)] g)
    (ht : t ∈ Ioo a b) (hf : cone2dSlicePoint e c t ∈ frontier (densityOne C)) :
    ∃ δ > 0, ∃ kₗ ∈ ({0, 1} : Set ℝ), ∃ kᵣ ∈ ({0, 1} : Set ℝ),
      kₗ ≠ kᵣ ∧
      ((fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
        (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo (t - δ) t)] (fun _ => kₗ)) ∧
      ((fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
        (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo t (t + δ))] (fun _ => kᵣ)) := by
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo a b := isOpen_Ioo.mem_nhds ht
  have hleft : ∀ᶠ s in 𝓝[<] t, s ∈ Ioo a b ∧ g s = g t := by
    have hn := hnear.filter_mono (nhdsWithin_le_nhds : 𝓝[<] t ≤ 𝓝 t)
    exact hn.and (eventually_eq_of_tendsto_binary (hn.mono fun s hs => hgb s hs)
      ((hgc t).mono Iio_subset_Iic_self))
  have hright : ∀ᶠ s in 𝓝[>] t, s ∈ Ioo a b ∧ g s = Function.rightLim g t := by
    have hn := hnear.filter_mono (nhdsWithin_le_nhds : 𝓝[>] t ≤ 𝓝 t)
    exact hn.and (eventually_eq_of_tendsto_binary (hn.mono fun s hs => hgb s hs)
      (hg.tendsto_rightLim t))
  obtain ⟨δl, hδl, hl⟩ := Metric.mem_nhdsWithin_iff.mp hleft
  obtain ⟨δr, hδr, hr⟩ := Metric.mem_nhdsWithin_iff.mp hright
  let δ := min δl δr
  have hδ : 0 < δ := lt_min hδl hδr
  have hl' (s : ℝ) (hs : s ∈ Ioo (t - δ) t) : s ∈ Ioo a b ∧ g s = g t := by
    apply hl
    refine ⟨?_, hs.2⟩
    rw [mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hs.2)]
    have hd : δ ≤ δl := min_le_left _ _
    linarith [hs.1]
  have hr' (s : ℝ) (hs : s ∈ Ioo t (t + δ)) :
      s ∈ Ioo a b ∧ g s = Function.rightLim g t := by
    apply hr
    refine ⟨?_, hs.1⟩
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hs.1)]
    have hd : δ ≤ δr := min_le_right _ _
    linarith [hs.2]
  have heql : (fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo (t - δ) t)] (fun _ => g t) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (fun s hs => (hl' s hs).1) heq, ae_restrict_mem measurableSet_Ioo] with s hs hsm
    exact hs.trans (hl' s hsm).2
  have heqr : (fun s => (densityOne C).indicator (fun _ => (1 : ℝ))
      (cone2dSlicePoint e c s)) =ᵐ[volume.restrict (Ioo t (t + δ))]
        (fun _ => Function.rightLim g t) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (fun s hs => (hr' s hs).1) heq, ae_restrict_mem measurableSet_Ioo] with s hs hsm
    exact hs.trans (hr' s hsm).2
  have hmid : t + δ / 2 ∈ Ioo t (t + δ) := by constructor <;> linarith
  have hbin : Function.rightLim g t ∈ ({0, 1} : Set ℝ) := by
    rw [← (hr' _ hmid).2]
    exact hgb _ (hr' _ hmid).1
  refine ⟨δ, hδ, g t, hgb t ht, Function.rightLim g t, hbin, ?_, heql, heqr⟩
  exact cone2d_adjacent_profile_phases_ne hm hcone e hc (by linarith) (by linarith)
    heql heqr hf

end LiquidDrop

namespace LiquidDrop

/-- At any frontier ray facing an orthogonal frame, the two sufficiently small
adjacent open sectors lie in opposite canonical interior phases. This is the
local phase change statement for the planar link; the unit-norm assumption on
the frontier point is unnecessary. -/
theorem cone2d_frontier_adjacent_sectors
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {u : EuclideanSpace ℝ (Fin 2)} (hu : 0 < e.symm u 0)
    (hf : u ∈ frontier (densityOne C)) :
    ∃ c ∈ Ioo (1 : ℝ) 2, ∃ δ > 0,
      let t := c * (e.symm u 1 / e.symm u 0)
      (cone2dOpenSector e c (t - δ) t ⊆ interior (densityOne C) ∧
        cone2dOpenSector e c t (t + δ) ⊆ interior ((densityOne C)ᶜ)) ∨
      (cone2dOpenSector e c (t - δ) t ⊆ interior ((densityOne C)ᶜ) ∧
        cone2dOpenSector e c t (t + δ) ⊆ interior (densityOne C)) := by
  let s := e.symm u 1 / e.symm u 0
  have h1 := hmin 1 (by norm_num)
  obtain ⟨c, hc, g, hg, hgc, heq, hgb, _⟩ :=
    cone2d_exists_binary_profile h1.nullMeasurable h1.locallyFinite e
      (by norm_num : (1 : ℝ) < 2) (-(2 * |s| + 1)) (2 * |s| + 1)
  have hc0 : 0 < c := by linarith [hc.1]
  have ht : c * s ∈ Ioo (-(2 * |s| + 1)) (2 * |s| + 1) := by
    have hab : |c * s| ≤ 2 * |s| := by
      rw [abs_mul, abs_of_pos hc0]
      exact mul_le_mul_of_nonneg_right hc.2.le (abs_nonneg s)
    obtain ⟨hl, hr⟩ := abs_le.mp hab
    constructor <;> linarith
  have hproj : cone2dSlicePoint e c (c * s) = (c / e.symm u 0) • u := by
    simpa only [s, mul_div_assoc] using cone2dSlicePoint_project e c u hu.ne'
  have hf' : cone2dSlicePoint e c (c * s) ∈ frontier (densityOne C) := by
    rw [hproj]
    exact (IsDilationInvariant.frontier hcone).smul_mem (div_pos hc0 hu) hf
  obtain ⟨δ, hδ, kₗ, hkₗ, kᵣ, hkᵣ, hne, hl, hr⟩ :=
    cone2d_frontier_adjacent_profile_phases h1.nullMeasurable hcone e hc0
      hg hgc hgb heq ht hf'
  have hleft := cone2d_open_ae_phase_interior h1.nullMeasurable
    (cone2dOpenSector_isOpen e c (c * s - δ) (c * s))
    (cone2d_ae_constant_on_openSector h1.nullMeasurable hcone e hc0 hl)
  have hright := cone2d_open_ae_phase_interior h1.nullMeasurable
    (cone2dOpenSector_isOpen e c (c * s) (c * s + δ))
    (cone2d_ae_constant_on_openSector h1.nullMeasurable hcone e hc0 hr)
  refine ⟨c, hc, δ, hδ, ?_⟩
  change (_ ∧ _) ∨ (_ ∧ _)
  simp only [mem_insert_iff, mem_singleton_iff] at hkₗ hkᵣ
  rcases hkₗ with rfl | rfl <;> rcases hkᵣ with rfl | rfl
  · exact (hne rfl).elim
  · exact Or.inr ⟨hleft.2 rfl, hright.1 rfl⟩
  · exact Or.inl ⟨hleft.1 rfl, hright.2 rfl⟩
  · exact (hne rfl).elim

end LiquidDrop
