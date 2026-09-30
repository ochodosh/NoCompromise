module

public import NoCompromise.BV.CompactnessIndicators
public import NoCompromise.Energy.Scaling
public import NoCompromise.Energy.Coulomb
public import NoCompromise.Sobolev.RelativeCubes
public import NoCompromise.Elliptic.ClassicalCubeGeometry
public import NoCompromise.BV.Basic
public import NoCompromise.BV.PlanarCuts

@[expose] public section

/-!
# Lower semicontinuity of Coulomb energy under local L¹ convergence
-/

noncomputable section

open Filter MeasureTheory Metric
open scoped ENNReal
open scoped Topology

namespace LiquidDrop

private def truncation (n : ℕ) : Set AmbientSpace := closedBall 0 n

private lemma truncation_compact (n : ℕ) : IsCompact (truncation n) :=
  isCompact_closedBall _ _

private lemma truncation_mono : Monotone truncation := by
  intro i j hij
  exact closedBall_subset_closedBall (by exact_mod_cast hij)

private lemma truncation_cover : (⋃ n, truncation n) = Set.univ := by
  exact Metric.iUnion_closedBall_nat 0

private lemma truncation_energy_sup (F : Set AmbientSpace) :
    coulombEnergy F = ⨆ n, coulombEnergy (F ∩ truncation n) := by
  have hunion : (⋃ n, (F ∩ truncation n) ×ˢ (F ∩ truncation n)) = F ×ˢ F := by
    ext p
    constructor
    · intro hp
      obtain ⟨n, hp⟩ := Set.mem_iUnion.mp hp
      exact ⟨hp.1.1, hp.2.1⟩
    · intro hp
      have hi' : p.1 ∈ ⋃ n, truncation n := by rw [truncation_cover]; trivial
      have hj' : p.2 ∈ ⋃ n, truncation n := by rw [truncation_cover]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hi'
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hj'
      apply Set.mem_iUnion.mpr
      refine ⟨max i j, ⟨hp.1, ?_⟩, ⟨hp.2, ?_⟩⟩
      · exact truncation_mono (le_max_left i j) hi
      · exact truncation_mono (le_max_right i j) hj
  have hdir : Directed (· ⊆ ·) (fun n => (F ∩ truncation n) ×ˢ (F ∩ truncation n)) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact Set.prod_mono (Set.inter_subset_inter_right F (truncation_mono (le_max_left i j)))
        (Set.inter_subset_inter_right F (truncation_mono (le_max_left i j)))
    · exact Set.prod_mono (Set.inter_subset_inter_right F (truncation_mono (le_max_right i j)))
        (Set.inter_subset_inter_right F (truncation_mono (le_max_right i j)))
  unfold coulombEnergy
  rw [← hunion, setLIntegral_iUnion_of_directed _ hdir, ENNReal.mul_iSup]

/-- Coulomb energy is lower semicontinuous under local L¹ convergence of indicators.
No finite-volume or finite-energy assumption is needed. -/
theorem coulombEnergy_le_liminf_of_l1_loc (E : ℕ → Set AmbientSpace) (F : Set AmbientSpace)
    (hE : ∀ n, NullMeasurableSet (E n) volume) (hF : NullMeasurableSet F volume)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun n => ∫ x in K,
        |(E n).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
        atTop (𝓝 0)) :
    coulombEnergy F ≤ Filter.liminf (fun n => coulombEnergy (E n)) Filter.atTop := by
  rw [truncation_energy_sup]
  refine iSup_le fun k => ?_
  let K := truncation k
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hKfin : volume K < ∞ := (truncation_compact k).measure_lt_top
  have hEm : ∀ n, NullMeasurableSet (E n ∩ K) volume :=
    fun n => (hE n).inter hKm.nullMeasurableSet
  have hFm : NullMeasurableSet (F ∩ K) volume := hF.inter hKm.nullMeasurableSet
  have hboundE : ∀ n, volume (E n ∩ K) ≤ ENNReal.ofReal (volume K).toReal := by
    intro n
    simpa only [ENNReal.ofReal_toReal hKfin.ne] using measure_mono (Set.inter_subset_right)
  have hboundF : volume (F ∩ K) ≤ ENNReal.ofReal (volume K).toReal := by
    simpa only [ENNReal.ofReal_toReal hKfin.ne] using measure_mono (Set.inter_subset_right)
  have hconvK : Tendsto (fun n => ∫ x,
      |(E n ∩ K).indicator (fun _ => (1 : ℝ)) x -
        (F ∩ K).indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0) := by
    convert hconv K (truncation_compact k) using 1
    ext n
    rw [← integral_indicator hKm]
    congr 1
    funext x
    by_cases hx : x ∈ K
    · by_cases hxE : x ∈ E n <;> by_cases hxF : x ∈ F <;>
        simp [Set.indicator, hx, hxE, hxF]
    · simp [Set.indicator, hx]
  have ht := tendsto_coulombEnergy_of_l1 hEm hFm ENNReal.toReal_nonneg
    hboundE hboundF hconvK
  have ht' : Tendsto (fun n => coulombEnergy (E n ∩ K)) atTop
      (𝓝 (coulombEnergy (F ∩ K))) := by
    have h := ENNReal.tendsto_ofReal ht
    have hEq : (fun n => ENNReal.ofReal (coulombEnergy (E n ∩ K)).toReal) =
        (fun n => coulombEnergy (E n ∩ K)) := by
      funext n
      exact ENNReal.ofReal_toReal (coulombEnergy_lt_top _
        ((hboundE n).trans_lt ENNReal.ofReal_lt_top)).ne
    rw [hEq, ENNReal.ofReal_toReal (coulombEnergy_lt_top _
      (hboundF.trans_lt ENNReal.ofReal_lt_top)).ne] at h
    exact h
  have hle : ∀ n, coulombEnergy (E n ∩ K) ≤ coulombEnergy (E n) := by
    intro n
    unfold coulombEnergy
    exact mul_le_mul_of_nonneg_left (lintegral_mono_set
      (Set.prod_mono Set.inter_subset_left Set.inter_subset_left)) (by positivity)
  exact ht'.liminf_eq ▸ Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)

end LiquidDrop

open Set

namespace LiquidDrop

set_option linter.style.haveILetI false

/-- The integer lattice point associated with a cube index. -/
def gridPoint (k : Fin 3 → ℤ) : AmbientSpace :=
  WithLp.toLp 2 (fun j => (k j : ℝ))

/-- An open unit cube in the grid translated by `v`. -/
def gridCube (v : AmbientSpace) (k : Fin 3 → ℤ) : Set AmbientSpace :=
  (fun y => y + (v + gridPoint k)) '' coordinateCube 3 (1 / 2)

private lemma gridCube_mem_iff (v x : AmbientSpace) (k : Fin 3 → ℤ) :
    x ∈ gridCube v k ↔ ∀ j : Fin 3, |x j - (v j + (k j : ℝ))| < 1 / 2 := by
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    simpa only [PiLp.add_apply, gridPoint, PiLp.toLp_apply, add_sub_cancel_right] using hy j
  · intro hx
    refine ⟨x - (v + gridPoint k), ?_, by simp⟩
    intro j
    simpa only [PiLp.sub_apply, PiLp.add_apply, gridPoint, PiLp.toLp_apply] using hx j

private lemma gridCube_isOpen (v : AmbientSpace) (k : Fin 3 → ℤ) :
    IsOpen (gridCube v k) := by
  exact (Homeomorph.addRight (v + gridPoint k)).isOpenMap _
    (isOpen_coordinateCube 3 (1 / 2))

private lemma gridCube_volume (v : AmbientSpace) (k : Fin 3 → ℤ) :
    volume (gridCube v k) = 1 := by
  have hc : volume (coordinateCube 3 (1 / 2)) = 1 := by
    have heq : coordinateCube 3 (1 / 2) = WithLp.ofLp ⁻¹'
        (univ.pi fun _ : Fin 3 => Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
      ext x
      simp only [coordinateCube, mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ,
        true_implies, mem_Ioo, abs_lt]
    rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
      ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)).nullMeasurableSet),
      volume_pi_pi]
    norm_num [Real.volume_Ioo]
  rw [gridCube]
  have hf : (fun y : AmbientSpace => y + (v + gridPoint k)) =
      (fun y => (v + gridPoint k) + y) := by
    funext y
    exact add_comm y _
  rw [hf, volume_image_add_left, hc]

private lemma gridCube_closure_mem (v x : AmbientSpace) (k : Fin 3 → ℤ)
    (hx : x ∈ closure (gridCube v k)) (j : Fin 3) :
    |x j - (v j + (k j : ℝ))| ≤ 1 / 2 := by
  let S : Set AmbientSpace := {y | |y j - (v j + (k j : ℝ))| ≤ 1 / 2}
  have hclosed : IsClosed S :=
    isClosed_le (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.sub
      continuous_const).abs) continuous_const
  have hsub : gridCube v k ⊆ S := fun y hy => (gridCube_mem_iff v y k).mp hy j |>.le
  exact closure_minimal hsub hclosed hx

private lemma gridCube_closure_eq (v : AmbientSpace) (k : Fin 3 → ℤ) :
    closure (gridCube v k) =
      (fun y => y + (v + gridPoint k)) '' closedCoordinateCube 3 (1 / 2) := by
  have h := (Homeomorph.addRight (v + gridPoint k)).image_closure
    (coordinateCube 3 (1 / 2))
  rw [closure_coordinateCube (by norm_num : (0 : ℝ) < 1 / 2)] at h
  exact h.symm

private lemma gridCube_mem_closure_iff (v x : AmbientSpace) (k : Fin 3 → ℤ) :
    x ∈ closure (gridCube v k) ↔
      ∀ j : Fin 3, |x j - (v j + (k j : ℝ))| ≤ 1 / 2 := by
  rw [gridCube_closure_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    simpa only [PiLp.add_apply, gridPoint, PiLp.toLp_apply, add_sub_cancel_right] using hy j
  · intro hx
    refine ⟨x - (v + gridPoint k), ?_, by simp⟩
    intro j
    simpa only [PiLp.sub_apply, PiLp.add_apply, gridPoint, PiLp.toLp_apply] using hx j

private lemma gridCube_closure_cover (v : AmbientSpace) :
    (⋃ k : Fin 3 → ℤ, closure (gridCube v k)) = Set.univ := by
  apply eq_univ_of_forall
  intro x
  let k : Fin 3 → ℤ := fun j => ⌊x j - v j + 1 / 2⌋
  apply mem_iUnion.mpr
  refine ⟨k, (gridCube_mem_closure_iff v x k).mpr ?_⟩
  intro j
  have hle : (k j : ℝ) ≤ x j - v j + 1 / 2 := Int.floor_le _
  have hlt : x j - v j + 1 / 2 < (k j : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> dsimp [k] at * <;> linarith

private lemma gridCube_pairwise_disjoint (v : AmbientSpace) :
    Pairwise (fun k l => Disjoint (gridCube v k) (gridCube v l)) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro x hxk hxl
  have hj : ∃ j : Fin 3, k j ≠ l j := by
    by_contra h
    push Not at h
    exact hkl (funext h)
  obtain ⟨j, hj⟩ := hj
  have hk := abs_lt.mp ((gridCube_mem_iff v x k).mp hxk j)
  have hl := abs_lt.mp ((gridCube_mem_iff v x l).mp hxl j)
  have hkl' : k j < l j + 1 := by
    have hr : (k j : ℝ) < (l j : ℝ) + 1 := by linarith
    exact_mod_cast hr
  have hlk' : l j < k j + 1 := by
    have hr : (l j : ℝ) < (k j : ℝ) + 1 := by linarith
    exact_mod_cast hr
  omega

private lemma gridCube_boundary_subset_planes (v : AmbientSpace) (k : Fin 3 → ℤ) :
    closure (gridCube v k) \ gridCube v k ⊆
      ⋃ (j : Fin 3) (z : ℤ), {x : AmbientSpace | x j = v j + (z : ℝ) + 1 / 2} := by
  intro x hx
  have hnot := (gridCube_mem_iff v x k).not.mp hx.2
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  have hle := gridCube_closure_mem v x k hx.1 j
  have habs : |x j - (v j + (k j : ℝ))| = 1 / 2 := le_antisymm hle hj
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp habs with hp | hn
  · refine mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨k j, ?_⟩⟩
    change x j = v j + (k j : ℝ) + 1 / 2
    linarith
  · refine mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨k j - 1, ?_⟩⟩
    change x j = v j + ((k j - 1 : ℤ) : ℝ) + 1 / 2
    push_cast
    linarith

private lemma gridCube_faces_volume_null (v : AmbientSpace) :
    volume (⋃ k : Fin 3 → ℤ, closure (gridCube v k) \ gridCube v k) = 0 := by
  have hplanes : volume (⋃ (j : Fin 3) (z : ℤ),
      {x : AmbientSpace | x j = v j + (z : ℝ) + 1 / 2}) = 0 := by
    apply measure_iUnion_null
    intro j
    apply measure_iUnion_null
    intro z
    have hnorm : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
    simpa [EuclideanSpace.inner_single_left] using
      volume_plane_eq_zero hnorm (v j + (z : ℝ) + 1 / 2)
  apply nonpos_iff_eq_zero.mp
  exact (measure_mono (iUnion_subset fun k => gridCube_boundary_subset_planes v k)).trans_eq
    hplanes

private lemma gridCube_volume_eq_tsum (v : AmbientSpace) (E : Set AmbientSpace)
    (hmE : NullMeasurableSet E volume) :
    volume E = ∑' k : Fin 3 → ℤ, volume (E ∩ gridCube v k) := by
  have hcover : (⋃ k : Fin 3 → ℤ, gridCube v k) ∪
      (⋃ k : Fin 3 → ℤ, closure (gridCube v k) \ gridCube v k) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ k : Fin 3 → ℤ, closure (gridCube v k) := by
      rw [gridCube_closure_cover]
      trivial
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    by_cases hq : x ∈ gridCube v k
    · exact Or.inl (mem_iUnion.mpr ⟨k, hq⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨k, ⟨hk, hq⟩⟩)
  have hEae : E =ᵐ[volume]
      (Set.inter E (⋃ k : Fin 3 → ℤ, gridCube v k) : Set AmbientSpace) := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (gridCube_faces_volume_null v)]
      with x hx
    apply propext
    constructor
    · intro hxe
      refine ⟨hxe, ?_⟩
      have hu : x ∈ (⋃ k : Fin 3 → ℤ, gridCube v k) ∪
          (⋃ k : Fin 3 → ℤ, closure (gridCube v k) \ gridCube v k) := by
        rw [hcover]
        trivial
      exact hu.resolve_right hx
    · exact And.left
  calc
    volume E = volume (E ∩ ⋃ k : Fin 3 → ℤ, gridCube v k) := measure_congr hEae
    _ = volume (⋃ k : Fin 3 → ℤ, E ∩ gridCube v k) := by rw [inter_iUnion]
    _ = ∑' k : Fin 3 → ℤ, volume (E ∩ gridCube v k) := by
      apply measure_iUnion₀
      · intro k l hkl
        exact ((gridCube_pairwise_disjoint v hkl).mono
          inter_subset_right inter_subset_right).aedisjoint
      · intro k
        exact hmE.inter (gridCube_isOpen v k).measurableSet.nullMeasurableSet

private lemma gridCube_measure_eq_tsum (v : AmbientSpace) (ρ : Measure AmbientSpace)
    (hfaces : ρ (⋃ k : Fin 3 → ℤ,
      closure (gridCube v k) \ gridCube v k) = 0) :
    ρ univ = ∑' k : Fin 3 → ℤ, ρ (gridCube v k) := by
  have hcover : (⋃ k : Fin 3 → ℤ, gridCube v k) ∪
      (⋃ k : Fin 3 → ℤ, closure (gridCube v k) \ gridCube v k) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ k : Fin 3 → ℤ, closure (gridCube v k) := by
      rw [gridCube_closure_cover]
      trivial
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    by_cases hq : x ∈ gridCube v k
    · exact Or.inl (mem_iUnion.mpr ⟨k, hq⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨k, ⟨hk, hq⟩⟩)
  have hae : (univ : Set AmbientSpace) =ᵐ[ρ]
      (⋃ k : Fin 3 → ℤ, gridCube v k) := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hfaces] with x hx
    apply propext
    constructor
    · intro _
      have hu : x ∈ (⋃ k : Fin 3 → ℤ, gridCube v k) ∪
          (⋃ k : Fin 3 → ℤ, closure (gridCube v k) \ gridCube v k) := by
        rw [hcover]
        trivial
      exact hu.resolve_right hx
    · intro _
      trivial
  calc
    ρ univ = ρ (⋃ k : Fin 3 → ℤ, gridCube v k) := measure_congr hae
    _ = ∑' k : Fin 3 → ℤ, ρ (gridCube v k) := by
      apply measure_iUnion (gridCube_pairwise_disjoint v)
      intro k
      exact (gridCube_isOpen v k).measurableSet

private lemma gridCube_perimeter_eq_tsum (E : Set AmbientSpace)
    (hmE : NullMeasurableSet E volume) (v : AmbientSpace)
    (hfaces : variationMeasure (E.indicator (fun _ => (1 : ℝ)))
      (locallyIntegrable_indicator_one hmE)
      (⋃ k : Fin 3 → ℤ, closure (gridCube v k) \ gridCube v k) = 0) :
    perimeterN E = ∑' k : Fin 3 → ℤ, perimeterIn E (gridCube v k) := by
  have h := gridCube_measure_eq_tsum v
    (variationMeasure (E.indicator (fun _ => (1 : ℝ)))
      (locallyIntegrable_indicator_one hmE)) hfaces
  simpa only [perimeterN, perimeterIn,
    variationMeasure_open (locallyIntegrable_indicator_one hmE) isOpen_univ,
    variationMeasure_open (locallyIntegrable_indicator_one hmE)
      (gridCube_isOpen v _)] using h

private lemma perimeterMeasure_locallyFinite {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    IsLocallyFiniteMeasure (variationMeasure (E.indicator (fun _ => (1 : ℝ)))
      (locallyIntegrable_indicator_one hmE)) := by
  let μ := variationMeasure (E.indicator (fun _ => (1 : ℝ)))
    (locallyIntegrable_indicator_one hmE)
  refine ⟨fun x => ⟨ball x 1, isOpen_ball.mem_nhds (mem_ball_self (by norm_num)), ?_⟩⟩
  change μ (ball x 1) < ∞
  rw [variationMeasure_open _ isOpen_ball]
  exact hE (ball x 1) isOpen_ball isBounded_ball.isCompact_closure

/-- A common grid shift whose faces are null for volume and for every perimeter measure. -/
theorem gridCube_faces_null_exists (E : ℕ → Set AmbientSpace)
    (hE : ∀ n, HasLocallyFinitePerimeter (E n))
    (hmE : ∀ n, NullMeasurableSet (E n) volume) :
    ∃ v : AmbientSpace,
      volume (⋃ k : Fin 3 → ℤ, closure (gridCube v k) \ gridCube v k) = 0 ∧
      ∀ n, variationMeasure ((E n).indicator (fun _ => (1 : ℝ)))
        (locallyIntegrable_indicator_one (hmE n))
        (⋃ k : Fin 3 → ℤ, closure (gridCube v k) \ gridCube v k) = 0 := by
  let μ (n : ℕ) := variationMeasure ((E n).indicator (fun _ => (1 : ℝ)))
    (locallyIntegrable_indicator_one (hmE n))
  let bad (n : ℕ) (j : Fin 3) (z : ℤ) : Set ℝ :=
    {t | 0 < μ n {x : AmbientSpace | x j = t + (z : ℝ) + 1 / 2}}
  have hbad (n : ℕ) (j : Fin 3) (z : ℤ) : (bad n j z).Countable := by
    haveI : IsLocallyFiniteMeasure (μ n) := perimeterMeasure_locallyFinite (hE n) (hmE n)
    have hc : {s : ℝ | 0 < μ n {x : AmbientSpace | x j = s}}.Countable :=
      Measure.countable_meas_level_set_pos
        ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable)
    have hs : bad n j z ⊆
        (fun s : ℝ => s - (z : ℝ) - 1 / 2) ''
          {s : ℝ | 0 < μ n {x : AmbientSpace | x j = s}} := by
      intro t ht
      refine ⟨t + (z : ℝ) + 1 / 2, ht, ?_⟩
      dsimp
      ring
    exact (hc.image _).mono hs
  let B : Set ℝ := ⋃ n : ℕ, ⋃ j : Fin 3, ⋃ z : ℤ, bad n j z
  have hB : B.Countable :=
    Set.countable_iUnion fun n => Set.countable_iUnion fun j =>
      Set.countable_iUnion fun z => hbad n j z
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ B := by
    by_contra h
    push Not at h
    exact Set.not_countable_univ (show (Set.univ : Set ℝ).Countable from
      (Set.eq_univ_of_forall h) ▸ hB)
  let v : AmbientSpace := WithLp.toLp 2 (fun _ => t)
  have hv (j : Fin 3) : v j = t := rfl
  have hplane (n : ℕ) (j : Fin 3) (z : ℤ) :
      μ n {x : AmbientSpace | x j = v j + (z : ℝ) + 1 / 2} = 0 := by
    rw [hv]
    have hn : t ∉ bad n j z := by
      intro hmem
      exact ht (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨j,
        mem_iUnion.mpr ⟨z, hmem⟩⟩⟩)
    exact nonpos_iff_eq_zero.mp (le_of_not_gt hn)
  have hvolplane (j : Fin 3) (z : ℤ) :
      volume {x : AmbientSpace | x j = v j + (z : ℝ) + 1 / 2} = 0 := by
    have hnorm : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
    simpa [EuclideanSpace.inner_single_left] using
      volume_plane_eq_zero hnorm (v j + (z : ℝ) + 1 / 2)
  have hsub : (⋃ k : Fin 3 → ℤ, closure (gridCube v k) \ gridCube v k) ⊆
      ⋃ (j : Fin 3) (z : ℤ), {x : AmbientSpace | x j = v j + (z : ℝ) + 1 / 2} := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact gridCube_boundary_subset_planes v k hk
  have hnull (ρ : Measure AmbientSpace)
      (hp : ∀ (j : Fin 3) (z : ℤ),
        ρ {x : AmbientSpace | x j = v j + (z : ℝ) + 1 / 2} = 0) :
      ρ (⋃ k : Fin 3 → ℤ, closure (gridCube v k) \ gridCube v k) = 0 := by
    apply nonpos_iff_eq_zero.mp
    exact (measure_mono hsub).trans_eq
      (measure_iUnion_null fun j => measure_iUnion_null fun z => hp j z)
  exact ⟨v, hnull volume hvolplane, fun n => hnull (μ n) (hplane n)⟩

/-- The relative-isoperimetric constant yields a uniform positive cube mass. -/
theorem cube_nonvanishing {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (E : Set AmbientSpace), NullMeasurableSet E volume →
      HasFinitePerimeter E → ENNReal.ofReal c ≤ volume E →
      volume E ≤ ENNReal.ofReal C → perimeterN E ≤ ENNReal.ofReal C →
      ∀ v : AmbientSpace,
        perimeterN E = (∑' k : Fin 3 → ℤ, perimeterIn E (gridCube v k)) →
        ∃ k : Fin 3 → ℤ, ENNReal.ofReal c₀ ≤ volume (E ∩ gridCube v k) := by
  obtain ⟨A, hA, hiso⟩ := relative_isoperimetric_cube_three
  let b : ℝ := c / (2 * A * C)
  let d : ℝ := min (1 / 2) (b ^ 3)
  have hb : 0 < b := by dsimp [b]; positivity
  have hd : 0 < d := lt_min (by norm_num) (pow_pos hb _)
  have hdhalf : d ≤ 1 / 2 := min_le_left _ _
  have hdroot : d ^ (1 / 3 : ℝ) ≤ b := by
    calc
      _ ≤ (b ^ 3) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hd.le (min_le_right _ _) (by norm_num)
      _ = b := by
        convert Real.pow_rpow_inv_natCast hb.le (by decide : (3 : ℕ) ≠ 0) using 1
        norm_num
  have hdprod : d ^ (1 / 3 : ℝ) * A * C ≤ c / 2 := by
    calc
      _ ≤ b * A * C := by gcongr
      _ = c / 2 := by
        dsimp [b]
        field_simp
  have hdc : (ENNReal.ofReal d) ^ (1 / 3 : ℝ) * ENNReal.ofReal A *
      ENNReal.ofReal C ≤ ENNReal.ofReal (c / 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hd.le (by norm_num),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hd.le _) hA.le)]
    exact ENNReal.ofReal_le_ofReal hdprod
  refine ⟨d, hd, ?_⟩
  intro E hmE _hfin hvol _hvolupper hper v hpergrid
  by_contra h
  push Not at h
  have hmass (k : Fin 3 → ℤ) :
      volume (E ∩ gridCube v k) < ENNReal.ofReal d := h k
  have hlocal (k : Fin 3 → ℤ) :
      volume (E ∩ gridCube v k) ≤
        (ENNReal.ofReal d) ^ (1 / 3 : ℝ) *
          (ENNReal.ofReal A * perimeterIn E (gridCube v k)) := by
    let m := volume (E ∩ gridCube v k)
    let q := volume (gridCube v k \ E)
    have hmhalf : m ≤ (1 / 2 : ℝ≥0∞) := by
      calc
        m ≤ ENNReal.ofReal d := (hmass k).le
        _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal hdhalf
        _ = (1 / 2 : ℝ≥0∞) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
          norm_num
    have hmfin : m ≠ ∞ := ne_top_of_le_ne_top (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞) hmhalf
    have hsum : m + q = 1 := by
      simpa only [m, q, inter_comm, gridCube_volume v k] using
        measure_inter_add_sdiff₀ (gridCube v k) hmE
    have hmq : m ≤ q := by
      apply (ENNReal.add_le_add_iff_left hmfin).mp
      calc
        m + m ≤ (1 / 2 : ℝ≥0∞) + 1 / 2 := add_le_add hmhalf hmhalf
        _ = 1 := by simpa only [one_div] using ENNReal.inv_two_add_inv_two
        _ = m + q := hsum.symm
    have hcube : m ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal A * perimeterIn E (gridCube v k) := by
      let a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace :=
        AffineIsometryEquiv.vaddConst ℝ (v + gridPoint k)
      have ha : a '' coordinateCube 3 (1 / 2) = gridCube v k := rfl
      have hi := hiso a 1 (by norm_num) E hmE
      simpa only [ha, m, q, min_eq_left hmq] using hi
    have hroot : m ^ (1 / 3 : ℝ) ≤ (ENNReal.ofReal d) ^ (1 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow (hmass k).le (by norm_num)
    calc
      m = m ^ (1 / 3 : ℝ) * m ^ (2 / 3 : ℝ) := by
        have hexp : (1 / 3 : ℝ) + 2 / 3 = 1 := by norm_num
        rw [← ENNReal.rpow_add_of_nonneg (1 / 3) (2 / 3)
          (by norm_num) (by norm_num), hexp, ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal d) ^ (1 / 3 : ℝ) *
          (ENNReal.ofReal A * perimeterIn E (gridCube v k)) := by
        exact mul_le_mul hroot hcube (by positivity) (by positivity)
  have hsum := ENNReal.tsum_le_tsum hlocal
  rw [← gridCube_volume_eq_tsum v E hmE, ENNReal.tsum_mul_left,
    ENNReal.tsum_mul_left,
    ← hpergrid] at hsum
  have hbound : volume E ≤ ENNReal.ofReal (c / 2) := by
    calc
      volume E ≤ (ENNReal.ofReal d) ^ (1 / 3 : ℝ) *
          ENNReal.ofReal A * perimeterN E := by
        simpa only [mul_assoc] using hsum
      _ ≤ (ENNReal.ofReal d) ^ (1 / 3 : ℝ) *
          ENNReal.ofReal A * ENNReal.ofReal C := by gcongr
      _ ≤ ENNReal.ofReal (c / 2) := hdc
  have hstrict : ENNReal.ofReal (c / 2) < ENNReal.ofReal c :=
    (ENNReal.ofReal_lt_ofReal_iff hc).mpr (by linarith)
  exact (not_le_of_gt hstrict) (hvol.trans hbound)

/-- Uniform nonvanishing for a sequence of finite-perimeter sets on one translated grid. -/
theorem cube_nonvanishing_seq {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (E : ℕ → Set AmbientSpace) (hmE : ∀ n, NullMeasurableSet (E n) volume)
    (hfin : ∀ n, HasFinitePerimeter (E n))
    (hvol_lower : ∀ n, ENNReal.ofReal c ≤ volume (E n))
    (hvol_upper : ∀ n, volume (E n) ≤ ENNReal.ofReal C)
    (hper : ∀ n, perimeterN (E n) ≤ ENNReal.ofReal C) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ v : AmbientSpace,
      ∀ n, ∃ k : Fin 3 → ℤ,
        ENNReal.ofReal c₀ ≤ volume (E n ∩ gridCube v k) := by
  obtain ⟨c₀, hc₀, hsingle⟩ := cube_nonvanishing hc hC
  have hloc : ∀ n, HasLocallyFinitePerimeter (E n) := by
    intro n A _ _
    exact (variation_mono MeasurableSet.univ (subset_univ _)).trans_lt (hfin n)
  obtain ⟨v, _, hfaces⟩ := gridCube_faces_null_exists E hloc hmE
  refine ⟨c₀, hc₀, v, fun n => ?_⟩
  exact hsingle (E n) (hmE n) (hfin n) (hvol_lower n) (hvol_upper n)
    (hper n) v (gridCube_perimeter_eq_tsum (E n) (hmE n) v (hfaces n))


private lemma compactness_nullMeasurable_translate {A : Set AmbientSpace}
    (hA : NullMeasurableSet A volume) (a : AmbientSpace) :
    NullMeasurableSet ((fun y => a + y) '' A) volume :=
  nullMeasurableSet_image_of_differentiable (by fun_prop)
    (fun _ _ h => add_left_cancel h) hA

private lemma compactness_cube_subset_ball :
    coordinateCube 3 (1 / 2) ⊆ ball (0 : AmbientSpace) 1 := by
  intro x hx
  rw [mem_ball_zero_iff, EuclideanSpace.norm_eq]
  apply (Real.sqrt_lt (by positivity) (by norm_num)).mpr
  have hb (j : Fin 3) : ‖x j‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hx j).le _
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
  norm_num at hs ⊢
  linarith

private lemma compactness_integral_indicator {A K : Set AmbientSpace}
    (hA : NullMeasurableSet A volume) (_hK : MeasurableSet K) :
    (∫ x in K, A.indicator (fun _ => (1 : ℝ)) x) = (volume (A ∩ K)).toReal := by
  have hA' : NullMeasurableSet A (volume.restrict K) :=
    hA.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  rw [integral_indicator₀ hA', setIntegral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply₀ hA', measureReal_def]

private lemma compactness_volume_tendsto {A : ℕ → Set AmbientSpace}
    {F K : Set AmbientSpace} (hA : ∀ j, NullMeasurableSet (A j) volume)
    (hF : NullMeasurableSet F volume) (hK : IsCompact K)
    (ht : Tendsto (fun j => ∫ x in K,
      |(A j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
      atTop (𝓝 0)) :
    Tendsto (fun j => (volume (A j ∩ K)).toReal) atTop
      (𝓝 (volume (F ∩ K)).toReal) := by
  have h := tendsto_integral_mul_of_l1_on_compact hK
    (fun j => (locallyIntegrable_indicator_one (hA j)).integrableOn_isCompact hK)
    ((locallyIntegrable_indicator_one hF).integrableOn_isCompact hK)
    (ψ := fun _ => (1 : ℝ)) continuousOn_const ht
  simpa only [mul_one, compactness_integral_indicator (hA _) hK.measurableSet,
    compactness_integral_indicator hF hK.measurableSet] using h

/-- Blueprint `thm:compactness`. -/
theorem compactness_of_volume_perimeter_bounds {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (E : ℕ → Set AmbientSpace) (hmE : ∀ n, NullMeasurableSet (E n) volume)
    (hfin : ∀ n, HasFinitePerimeter (E n))
    (hvol_lower : ∀ n, ENNReal.ofReal c ≤ volume (E n))
    (hvol_upper : ∀ n, volume (E n) ≤ ENNReal.ofReal C)
    (hper : ∀ n, perimeter (E n) ≤ ENNReal.ofReal C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ (w : ℕ → AmbientSpace) (F : Set AmbientSpace),
        MeasurableSet F ∧ HasLocallyFinitePerimeter F ∧ HasFinitePerimeter F ∧
        0 < volume F ∧ volume F ≤ ENNReal.ofReal C ∧
        (∀ K : Set AmbientSpace, IsCompact K →
          Tendsto (fun j => ∫ x in K,
            |((fun y => w j + y) '' E (σ j)).indicator (fun _ => (1 : ℝ)) x
              - F.indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0)) ∧
        perimeter F ≤ liminf (fun j => perimeter (E (σ j))) atTop ∧
        coulombEnergy F ≤ liminf (fun j => coulombEnergy (E (σ j))) atTop := by
  classical
  have hperN (n : ℕ) : perimeterN (E n) ≤ ENNReal.ofReal C := by
    rw [perimeterN_eq_perimeter _ (hmE n)]
    exact hper n
  obtain ⟨c₀, hc₀, v, hk⟩ :=
    cube_nonvanishing_seq hc hC E hmE hfin hvol_lower hvol_upper hperN
  choose k hk using hk
  let w (n : ℕ) := -(v + gridPoint (k n))
  let A (n : ℕ) := (fun y => w n + y) '' E n
  have hmA (n : ℕ) : NullMeasurableSet (A n) volume :=
    compactness_nullMeasurable_translate (hmE n) (w n)
  have hvA (n : ℕ) : volume (A n) ≤ ENNReal.ofReal C := by
    dsimp [A]
    rw [volume_image_translate]
    exact hvol_upper n
  have hpA (n : ℕ) : perimeterN (A n) ≤ ENNReal.ofReal C := by
    dsimp [A]
    rw [perimeterN_translate]
    exact hperN n
  have hlA (n : ℕ) : HasLocallyFinitePerimeter (A n) := by
    intro B _ _
    exact ((variation_mono MeasurableSet.univ (subset_univ _)).trans (hpA n)).trans_lt
      ENNReal.ofReal_lt_top
  have hmass (n : ℕ) : ENNReal.ofReal c₀ ≤ volume (A n ∩ closedBall 0 1) := by
    have hs : (fun y => w n + y) '' (E n ∩ gridCube v (k n)) ⊆
        A n ∩ closedBall 0 1 := by
      rintro _ ⟨x, ⟨hx, y, hy, rfl⟩, rfl⟩
      refine ⟨⟨y + (v + gridPoint (k n)), hx, rfl⟩, ?_⟩
      have heq : w n + (y + (v + gridPoint (k n))) = y := by
        dsimp [w]
        abel
      change w n + (y + (v + gridPoint (k n))) ∈ closedBall 0 1
      rw [heq]
      exact ball_subset_closedBall (compactness_cube_subset_ball hy)
    exact (hk n).trans ((volume_image_translate _ (w n)) ▸ measure_mono hs)
  have hbound (B : Set AmbientSpace) (hB : IsOpen B) (_ : IsCompact (closure B)) :
      ∃ C' : ℝ, ∀ n, (∫ x in B, |(A n).indicator (fun _ => (1 : ℝ)) x|) +
        (perimeterIn (A n) B).toReal ≤ C' := by
    refine ⟨2 * C, fun n => ?_⟩
    have hi : (∫ x in B, |(A n).indicator (fun _ => (1 : ℝ)) x|) ≤ C := by
      have heq : (fun x => |(A n).indicator (fun _ => (1 : ℝ)) x|) =
          (A n).indicator (fun _ => (1 : ℝ)) := by
        funext x
        by_cases hx : x ∈ A n <;> simp [hx]
      rw [heq, compactness_integral_indicator (hmA n) hB.measurableSet]
      exact ENNReal.toReal_le_of_le_ofReal hC.le
        ((measure_mono inter_subset_left).trans (hvA n))
    have hp : (perimeterIn (A n) B).toReal ≤ C :=
      ENNReal.toReal_le_of_le_ofReal hC.le
        ((variation_mono MeasurableSet.univ (subset_univ _)).trans (hpA n))
    linarith
  obtain ⟨F, hmF, hlF, σ, hσ, ht⟩ :=
    bv_compactness_indicators_univ' A hlA hmA hbound
  have hvolconv (K : Set AmbientSpace) (hK : IsCompact K) :=
    compactness_volume_tendsto (fun j => hmA (σ j)) hmF.nullMeasurableSet hK (ht K hK)
  have hvFbound (K : Set AmbientSpace) (hK : IsCompact K) :
      volume (F ∩ K) ≤ ENNReal.ofReal C := by
    have hreal : (volume (F ∩ K)).toReal ≤ C :=
      le_of_tendsto (hvolconv K hK) (Eventually.of_forall fun j =>
        ENNReal.toReal_le_of_le_ofReal hC.le
          ((measure_mono inter_subset_left).trans (hvA (σ j))))
    have hfinite : volume (F ∩ K) ≠ ∞ :=
      ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono inter_subset_right)
    exact (ENNReal.ofReal_toReal hfinite) ▸ ENNReal.ofReal_le_ofReal hreal
  have hvF : volume F ≤ ENNReal.ofReal C := by
    have hmono : Monotone (fun n => F ∩ truncation n) :=
      fun _ _ hij => inter_subset_inter_right F (truncation_mono hij)
    have hcover : (⋃ n, F ∩ truncation n) = F := by
      rw [← inter_iUnion, truncation_cover, inter_univ]
    have hlim := tendsto_measure_iUnion_atTop (μ := volume) hmono
    rw [hcover] at hlim
    exact le_of_tendsto hlim
      (Eventually.of_forall fun n => hvFbound (truncation n) (truncation_compact n))
  have hvFpos : 0 < volume F := by
    have hfinite (j : ℕ) : volume (A (σ j) ∩ closedBall 0 1) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((measure_mono inter_subset_left).trans (hvA (σ j)))
    have hreal : c₀ ≤ (volume (F ∩ closedBall 0 1)).toReal := by
      apply ge_of_tendsto (hvolconv _ (isCompact_closedBall 0 1))
      apply Eventually.of_forall
      intro j
      have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hfinite j)).mpr
        (hmass (σ j))
      simpa only [ENNReal.toReal_ofReal hc₀.le] using h
    have hpos : 0 < volume (F ∩ closedBall 0 1) :=
      ENNReal.toReal_pos_iff.mp (hc₀.trans_le hreal) |>.1
    exact hpos.trans_le (measure_mono inter_subset_left)
  have hplsc : perimeterN F ≤ liminf (fun j => perimeter (E (σ j))) atTop := by
    have h := perimeterIn_le_liminf_of_locally_l1 isOpen_univ
      (fun j => hmA (σ j)) hmF.nullMeasurableSet (fun K hK _ => ht K hK)
    change perimeterN F ≤ liminf (fun j => perimeterN (A (σ j))) atTop at h
    simpa only [A, perimeterN_translate, perimeterN_eq_perimeter _ (hmE _)] using h
  have hlimbound : liminf (fun j => perimeter (E (σ j))) atTop ≤ ENNReal.ofReal C := by
    exact liminf_le_of_frequently_le' (Frequently.of_forall fun j => hper (σ j))
  have hfF : HasFinitePerimeter F := (hplsc.trans hlimbound).trans_lt ENNReal.ofReal_lt_top
  refine ⟨σ, hσ, (fun j => w (σ j)), F, hmF, hlF, hfF, hvFpos, hvF, ht, ?_, ?_⟩
  · rwa [← perimeterN_eq_perimeter F hmF.nullMeasurableSet]
  · have h := coulombEnergy_le_liminf_of_l1_loc (fun j => A (σ j)) F
      (fun j => hmA (σ j)) hmF.nullMeasurableSet ht
    simpa only [A, coulombEnergy_translate] using h

end LiquidDrop
