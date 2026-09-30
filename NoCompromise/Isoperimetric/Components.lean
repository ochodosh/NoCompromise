module

public import NoCompromise.Isoperimetric.Sharp
public import NoCompromise.Isoperimetric.ABP
public import NoCompromise.BV.SmoothApproxBoundary
public import NoCompromise.Sobolev.C1Domain
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Topology.Connected.LocallyConnected

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

/-- The connected components of a set, as a set of sets. -/
def openComponents (S : Set AmbientSpace) : Set (Set AmbientSpace) :=
  {G | ∃ x ∈ S, connectedComponentIn S x = G}

lemma pairwiseDisjoint_openComponents (S : Set AmbientSpace) :
    (openComponents S).PairwiseDisjoint id := by
  rintro G ⟨x, hx, rfl⟩ H ⟨y, hy, rfl⟩ hne
  apply Set.disjoint_left.mpr
  intro z hzx hzy
  exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

theorem countable_openComponents {S : Set AmbientSpace} (hS : IsOpen S) :
    (openComponents S).Countable := by
  apply (pairwiseDisjoint_openComponents S).countable_of_isOpen
  · rintro G ⟨x, hx, rfl⟩
    exact hS.connectedComponentIn
  · rintro G ⟨x, hx, rfl⟩
    exact ⟨x, mem_connectedComponentIn hx⟩

theorem frontier_connectedComponentIn_subset {S : Set AmbientSpace} (hS : IsOpen S)
    (x : AmbientSpace) : frontier (connectedComponentIn S x) ⊆ frontier S := by
  intro p hp
  rw [hS.frontier_eq]
  refine ⟨closure_mono (connectedComponentIn_subset S x) hp.1, ?_⟩
  intro hpS
  obtain ⟨z, hzp, hzx⟩ := mem_closure_iff.mp hp.1 (connectedComponentIn S p)
    hS.connectedComponentIn (mem_connectedComponentIn hpS)
  have heq := (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzp).symm
  exact hp.2 (hS.connectedComponentIn.interior_eq.symm ▸ (heq.symm ▸
    mem_connectedComponentIn hpS))

/-- Near a boundary point, a C¹ domain is connected: the local picture of one component. -/
theorem HasC1Boundary.exists_nhds_isPreconnected_inter {S : Set AmbientSpace}
    (hSs : HasC1Boundary S) {p : AmbientSpace} (hp : p ∈ frontier S) :
    ∃ W : Set AmbientSpace, IsOpen W ∧ p ∈ W ∧ IsPreconnected (S ∩ W) := by
  obtain ⟨c, hc, hpc⟩ := hSs p hp
  obtain ⟨d, hd, hpd⟩ := hc.exists_lipschitzGraphChart hp hpc
  refine ⟨d.region, d.isOpen_region, hpd, ?_⟩
  rw [← hd]
  apply IsPreconnected.image _ _ d.homeomorph.continuous.continuousOn
  apply Convex.isPreconnected
  apply (convex_coordinateCube 3 d.radius).inter
  intro x hx y hy a b ha hb hab
  change 0 < (a • x + b • y) d.normal
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  change 0 < x d.normal at hx
  change 0 < y d.normal at hy
  rcases lt_or_eq_of_le ha with ha | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos ha hx) (mul_nonneg hb hy.le)
  · simpa [show b = 1 by linarith] using hy

/-- A connected local piece meeting a component belongs entirely to that component. -/
lemma inter_eq_component_inter {S W : Set AmbientSpace} {x p : AmbientSpace}
    (hW : IsOpen W) (hpW : p ∈ W) (hp : p ∈ closure (connectedComponentIn S x))
    (hc : IsPreconnected (S ∩ W)) :
    S ∩ W = connectedComponentIn S x ∩ W := by
  obtain ⟨z, hzW, hzG⟩ := mem_closure_iff.mp hp W hW hpW
  have hsub : S ∩ W ⊆ connectedComponentIn S x := by
    rw [connectedComponentIn_eq hzG]
    exact hc.subset_connectedComponentIn ⟨connectedComponentIn_subset S x hzG, hzW⟩
      inter_subset_left
  exact Subset.antisymm (fun z hz => ⟨hsub hz, hz.2⟩)
    (inter_subset_inter_left W (connectedComponentIn_subset S x))

theorem hasSmoothBoundary_connectedComponentIn {S : Set AmbientSpace} (hS : IsOpen S)
    (hSs : HasSmoothBoundary S) (x : AmbientSpace) :
    HasSmoothBoundary (connectedComponentIn S x) := by
  intro p hp
  have hpS := frontier_connectedComponentIn_subset hS x hp
  obtain ⟨c, hc, hpc, hcs⟩ := hSs p hpS
  obtain ⟨W, hW, hpW, hSW⟩ := hSs.hasC1Boundary.exists_nhds_isPreconnected_inter hpS
  have heq := inter_eq_component_inter hW hpW hp.1 hSW
  let d : C1BoundaryChart :=
    { c with
      region := c.region ∩ W
      isOpen_region := c.isOpen_region.inter hW
      bounded_region := c.bounded_region.subset inter_subset_left }
  refine ⟨d, ?_, ⟨hpc, hpW⟩, hcs⟩
  intro z hz
  change z ∈ connectedComponentIn S x ↔ c.placement.symm z ∈ smoothSubgraph c.height
  rw [← hc z hz.1]
  exact ⟨fun hzG => connectedComponentIn_subset S x hzG, fun hzS =>
    (show z ∈ connectedComponentIn S x ∩ W from heq ▸ ⟨hzS, hz.2⟩).1⟩

theorem pairwiseDisjoint_frontier_openComponents {S : Set AmbientSpace} (hS : IsOpen S)
    (hSs : HasC1Boundary S) : (openComponents S).PairwiseDisjoint frontier := by
  rintro G ⟨x, hx, rfl⟩ H ⟨y, hy, rfl⟩ hne
  apply Set.disjoint_left.mpr
  intro p hpx hpy
  have hpS := frontier_connectedComponentIn_subset hS x hpx
  obtain ⟨W, hW, hpW, hSW⟩ := hSs.exists_nhds_isPreconnected_inter hpS
  have hex := inter_eq_component_inter hW hpW hpx.1 hSW
  have hey := inter_eq_component_inter hW hpW hpy.1 hSW
  obtain ⟨z, hzW, hzS⟩ := mem_closure_iff.mp hpS.1 W hW hpW
  have hzx : z ∈ connectedComponentIn S x :=
    (show z ∈ connectedComponentIn S x ∩ W from hex ▸ ⟨hzS, hzW⟩).1
  have hzy : z ∈ connectedComponentIn S y :=
    (show z ∈ connectedComponentIn S y ∩ W from hey ▸ ⟨hzS, hzW⟩).1
  exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

theorem frontier_eq_biUnion_openComponents {S : Set AmbientSpace} (hS : IsOpen S)
    (hSs : HasC1Boundary S) : frontier S = ⋃ G ∈ openComponents S, frontier G := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨W, hW, hpW, hSW⟩ := hSs.exists_nhds_isPreconnected_inter hp
    obtain ⟨z, hzW, hzS⟩ := mem_closure_iff.mp hp.1 W hW hpW
    have hsub := hSW.subset_connectedComponentIn ⟨hzS, hzW⟩ inter_subset_left
    have hpcl : p ∈ closure (S ∩ W) := by
      rw [inter_comm]
      exact hW.inter_closure ⟨hpW, hp.1⟩
    apply mem_biUnion (show connectedComponentIn S z ∈ openComponents S from ⟨z, hzS, rfl⟩)
    rw [hS.connectedComponentIn.frontier_eq]
    refine ⟨closure_mono hsub hpcl, ?_⟩
    intro hpG
    exact (hS.frontier_eq ▸ hp).2 (connectedComponentIn_subset S z hpG)
  · intro p hp
    obtain ⟨G, ⟨x, hx, rfl⟩, hpG⟩ := mem_iUnion₂.mp hp
    exact frontier_connectedComponentIn_subset hS x hpG

theorem perimeter_eq_tsum_openComponents {S : Set AmbientSpace} (hS : IsOpen S)
    (hSs : HasSmoothBoundary S) :
    perimeter S = ∑' G : openComponents S, perimeter (G : Set AmbientSpace) := by
  rw [hSs.hasC1Boundary.perimeter_eq_boundaryArea hS,
    frontier_eq_biUnion_openComponents hS hSs.hasC1Boundary,
    measure_biUnion (countable_openComponents hS)
      (pairwiseDisjoint_frontier_openComponents hS hSs.hasC1Boundary)
      (fun _ _ => isClosed_frontier.measurableSet)]
  apply tsum_congr
  rintro ⟨G, x, hx, rfl⟩
  exact (HasC1Boundary.perimeter_eq_boundaryArea
    (hasSmoothBoundary_connectedComponentIn hS hSs x).hasC1Boundary
    hS.connectedComponentIn).symm

lemma eq_biUnion_openComponents (S : Set AmbientSpace) :
    S = ⋃ G ∈ openComponents S, G := by
  apply Subset.antisymm
  · intro x hx
    exact mem_biUnion ⟨x, hx, rfl⟩ (mem_connectedComponentIn hx)
  · intro x hx
    obtain ⟨G, ⟨y, hy, rfl⟩, hxG⟩ := mem_iUnion₂.mp hx
    exact connectedComponentIn_subset S y hxG

theorem volume_eq_tsum_openComponents {S : Set AmbientSpace} (hS : IsOpen S) :
    volume S = ∑' G : openComponents S, volume (G : Set AmbientSpace) := by
  calc
    volume S = volume (⋃ G ∈ openComponents S, G) :=
      congrArg volume (eq_biUnion_openComponents S)
    _ = _ := measure_biUnion (countable_openComponents hS)
      (pairwiseDisjoint_openComponents S) (by
        rintro G ⟨x, hx, rfl⟩
        exact hS.connectedComponentIn.measurableSet)

/-- Subadditivity of a positive power at most one for arbitrary nonnegative sums. -/
lemma ennreal_rpow_tsum_le {ι : Type*} (f : ι → ℝ≥0∞) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) : (∑' i, f i) ^ p ≤ ∑' i, f i ^ p := by
  classical
  have hfin (s : Finset ι) : (∑ i ∈ s, f i) ^ p ≤ ∑ i ∈ s, f i ^ p := by
    induction s using Finset.induction_on with
    | empty => simp [ENNReal.zero_rpow_of_pos hp]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (ENNReal.rpow_add_le_add_rpow _ _ hp.le hp1).trans (add_le_add le_rfl ih)
  rw [← ENNReal.le_rpow_inv_iff hp, ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  exact (ENNReal.le_rpow_inv_iff hp).mpr ((hfin s).trans (ENNReal.sum_le_tsum s))

/-- Taking cube roots of the connected smooth isoperimetric inequality. -/
lemma isoperimetric_cube_root {v p : ℝ} (hv : 0 ≤ v) (hp : 0 ≤ p)
    (h : 36 * Real.pi * v ^ 2 ≤ p ^ 3) :
    (36 * Real.pi) ^ (1 / (3 : ℝ)) * v ^ (2 / (3 : ℝ)) ≤ p := by
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 36 * Real.pi * v ^ 2)
    h (by norm_num : 0 ≤ 1 / (3 : ℝ))
  rw [Real.mul_rpow (by positivity) (sq_nonneg v),
    ← Real.rpow_natCast v 2, ← Real.rpow_mul hv,
    ← Real.rpow_natCast p 3, ← Real.rpow_mul hp] at hr
  norm_num only [show (2 : ℝ) * (1 / 3) = 2 / 3 by norm_num,
    show (3 : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at hr
  exact hr

/-- Blueprint `cor:iso-smooth-components` (both inequalities), from `prop:iso-smooth`. -/
theorem iso_smooth_components
    (hconn : ∀ G : Set AmbientSpace, IsOpen G → Bornology.IsBounded G → IsConnected G →
      HasSmoothBoundary G → 36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3)
    {S : Set AmbientSpace} (hS : IsOpen S) (hSb : Bornology.IsBounded S)
    (hSs : HasSmoothBoundary S) :
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ))) *
        ∑' G : openComponents S, volume (G : Set AmbientSpace) ^ (2 / (3 : ℝ))
          ≤ perimeter S ∧
      volume S ^ (2 / (3 : ℝ)) ≤
        ∑' G : openComponents S, volume (G : Set AmbientSpace) ^ (2 / (3 : ℝ)) := by
  constructor
  · rw [perimeter_eq_tsum_openComponents hS hSs, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    rintro ⟨G, x, hx, rfl⟩
    have ho : IsOpen (connectedComponentIn S x) := hS.connectedComponentIn
    have hb := hSb.subset (connectedComponentIn_subset S x)
    have hs := hasSmoothBoundary_connectedComponentIn hS hSs x
    have hc := isConnected_connectedComponentIn_iff.mpr hx
    have hvfin : volume (connectedComponentIn S x) ≠ ∞ := hb.measure_lt_top.ne
    have hpfin : perimeter (connectedComponentIn S x) ≠ ∞ := by
      have hf := hs.hasC1Boundary.hasFinitePerimeter ho hb
      change perimeterN (connectedComponentIn S x) < ∞ at hf
      rw [perimeterN_eq_perimeter _ ho.measurableSet.nullMeasurableSet] at hf
      exact hf.ne
    have hr := isoperimetric_cube_root ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (hconn _ ho hb hc hs)
    have he := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hvfin, ENNReal.ofReal_toReal hpfin] at he
    exact he
  · rw [volume_eq_tsum_openComponents hS]
    exact ennreal_rpow_tsum_le _ (by norm_num) (by norm_num)

/-- `SmoothIsoperimetric` (Sharp.lean) from `prop:iso-smooth`. -/
theorem smoothIsoperimetric_of_connected
    (hconn : ∀ G : Set AmbientSpace, IsOpen G → Bornology.IsBounded G → IsConnected G →
      HasSmoothBoundary G → 36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3) :
    SmoothIsoperimetric := by
  intro S hS hSb hSs
  obtain ⟨hfirst, hsecond⟩ := iso_smooth_components hconn hS hSb hSs
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal hSb.measure_lt_top.ne]
  exact (mul_le_mul_right hsecond _).trans hfirst

/-- Strict concavity for two positive finite extended nonnegative reals. -/
lemma ennreal_rpow_two_thirds_strict {a b : ℝ≥0∞} (ha : 0 < a) (hb : 0 < b)
    (ha_top : a ≠ ∞) (hb_top : b ≠ ∞) :
    (a + b) ^ (2 / (3 : ℝ)) < a ^ (2 / (3 : ℝ)) + b ^ (2 / (3 : ℝ)) := by
  have h := rpow_two_thirds_strict_superadditive
    (ENNReal.toReal_pos ha.ne' ha_top) (ENNReal.toReal_pos hb.ne' hb_top)
  have he := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (Real.rpow_nonneg (by positivity) _)).mpr h
  rw [ENNReal.ofReal_add (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by positivity) _)] at he
  rw [← ENNReal.ofReal_rpow_of_nonneg (add_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg) (by norm_num : 0 ≤ 2 / (3 : ℝ)),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : 0 ≤ 2 / (3 : ℝ)),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : 0 ≤ 2 / (3 : ℝ)),
    ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal ha_top, ENNReal.ofReal_toReal hb_top] at he
  exact he

open scoped Classical in
/-- Separate two distinct terms from an extended nonnegative sum. -/
lemma ennreal_tsum_eq_add_add_tsum_ite {ι : Type*} (f : ι → ℝ≥0∞)
    {i j : ι} (hij : i ≠ j) :
    ∑' k, f k = f i + f j + ∑' k, if k = j then 0 else if k = i then 0 else f k := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite i, ENNReal.tsum_eq_add_tsum_ite j]
  simp [hij.symm, add_assoc]

/-- Two positive terms make the two-thirds power inequality strict for a finite sum. -/
lemma ennreal_rpow_two_thirds_tsum_lt {ι : Type*} (f : ι → ℝ≥0∞)
    (hf : ∑' k, f k ≠ ∞) {i j : ι} (hij : i ≠ j) (hi : 0 < f i)
    (hj : 0 < f j) :
    (∑' k, f k) ^ (2 / (3 : ℝ)) < ∑' k, f k ^ (2 / (3 : ℝ)) := by
  classical
  let r : ι → ℝ≥0∞ := fun k => if k = j then 0 else if k = i then 0 else f k
  have hsplit : ∑' k, f k = f i + f j + ∑' k, r k :=
    ennreal_tsum_eq_add_add_tsum_ite f hij
  have hr_le : ∑' k, r k ≤ ∑' k, f k := by
    apply ENNReal.tsum_le_tsum
    intro k
    dsimp [r]
    split_ifs <;> simp
  have hr_top : (∑' k, r k) ^ (2 / (3 : ℝ)) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ne_top_of_le_ne_top hf hr_le)).ne
  have hi_top : f i ≠ ∞ := ne_top_of_le_ne_top hf (ENNReal.le_tsum i)
  have hj_top : f j ≠ ∞ := ne_top_of_le_ne_top hf (ENNReal.le_tsum j)
  have hstrict := ennreal_rpow_two_thirds_strict hi hj hi_top hj_top
  calc
    (∑' k, f k) ^ (2 / (3 : ℝ)) =
        (f i + f j + ∑' k, r k) ^ (2 / (3 : ℝ)) := by rw [hsplit]
    _ ≤ (f i + f j) ^ (2 / (3 : ℝ)) + (∑' k, r k) ^ (2 / (3 : ℝ)) :=
      ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
    _ < (f i ^ (2 / (3 : ℝ)) + f j ^ (2 / (3 : ℝ))) +
        (∑' k, r k) ^ (2 / (3 : ℝ)) := ENNReal.add_lt_add_right hr_top hstrict
    _ ≤ (f i ^ (2 / (3 : ℝ)) + f j ^ (2 / (3 : ℝ))) +
        ∑' k, r k ^ (2 / (3 : ℝ)) :=
      add_le_add le_rfl
        (ennreal_rpow_tsum_le r (p := 2 / (3 : ℝ)) (by norm_num) (by norm_num))
    _ = ∑' k, f k ^ (2 / (3 : ℝ)) := by
      rw [ennreal_tsum_eq_add_add_tsum_ite (fun k => f k ^ (2 / (3 : ℝ))) hij]
      congr 1
      apply tsum_congr
      intro k
      dsimp [r]
      split_ifs <;> simp

/-- Blueprint `cor:iso-smooth-components`, strictness: with two distinct components the
concavity inequality is strict. -/
theorem volume_rpow_lt_tsum_openComponents {S : Set AmbientSpace} (hS : IsOpen S)
    (hSb : Bornology.IsBounded S) {G H : Set AmbientSpace} (hG : G ∈ openComponents S)
    (hH : H ∈ openComponents S) (hGH : G ≠ H) :
    volume S ^ (2 / (3 : ℝ)) <
      ∑' K : openComponents S, volume (K : Set AmbientSpace) ^ (2 / (3 : ℝ)) := by
  have hpos (K : openComponents S) : 0 < volume (K : Set AmbientSpace) := by
    obtain ⟨K, x, hx, rfl⟩ := K
    exact hS.connectedComponentIn.measure_pos volume ⟨x, mem_connectedComponentIn hx⟩
  rw [volume_eq_tsum_openComponents hS]
  apply ennreal_rpow_two_thirds_tsum_lt
    (fun K : openComponents S => volume (K : Set AmbientSpace))
    (by rw [← volume_eq_tsum_openComponents hS]; exact hSb.measure_lt_top.ne)
    (i := ⟨G, hG⟩) (j := ⟨H, hH⟩)
  · exact fun h => hGH (congrArg Subtype.val h)
  · exact hpos ⟨G, hG⟩
  · exact hpos ⟨H, hH⟩

end LiquidDrop
