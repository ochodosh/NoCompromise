import NoCompromise.Cones.TwoDim
import NoCompromise.BV.Density

/-!
# Cones whose boundary lies in a hyperplane are halfspaces

The geometric endgame of blueprint `thm:cone-3d` ("`∂C` is the plane spanned by the great circle,
so `C` is one of the two halfspaces") and of `lem:cone-2d` (two antipodal rays give a halfplane),
in every dimension `n`, for the density-one representative `densityOne S`.

* `densityOne_halfspace` : an open halfspace is its own density-one representative
  (points of the bounding hyperplane have density exactly `1/2`);
* `frontier_halfspace` : the frontier of an open halfspace is the bounding hyperplane;
* `densityOne_eq_halfspace_of_frontier_subset` : if the frontier of `densityOne S` lies in a
  hyperplane and `S` is nontrivial in measure, `densityOne S` is one of the two open halfspaces;
* `densityOne_eq_halfspace_of_link` : the same conclusion for a dilation-invariant
  `densityOne S` whose link of the frontier lies in a great sphere.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace LiquidDrop

variable {n : ℕ}

/-- A ball contained in `E` has volume fraction one. -/
lemma densityRatio_eq_one_of_ball_subset {A : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (h : ball x r ⊆ A) :
    densityRatio A x r = 1 := by
  have hpos : volume (ball x r) ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hfin : volume (ball x r) ≠ ∞ := measure_ball_lt_top.ne
  rw [densityRatio, inter_eq_right.mpr h, div_self]
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos, hfin⟩

/-- A point with a ball inside the set is a density-one point. -/
lemma mem_densityOne_of_ball_subset {A : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (h : ball x r ⊆ A) :
    x ∈ densityOne A := by
  show Tendsto (densityRatio A x) (𝓝[>] 0) (𝓝 1)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT hr] with s hs
  exact (densityRatio_eq_one_of_ball_subset hs.1 ((ball_subset_ball hs.2.le).trans h)).symm

/-- A point with a ball disjoint from the set is not a density-one point. -/
lemma not_mem_densityOne_of_disjoint_ball {A : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (h : Disjoint (ball x r) A) :
    x ∉ densityOne A := by
  intro hx
  have h0 : Tendsto (densityRatio A x) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    have : A ∩ ball x s = ∅ := by
      rw [inter_comm]
      exact (h.mono_left (ball_subset_ball hs.2.le)).inter_eq
    simp [densityRatio, this]
  exact one_ne_zero (tendsto_nhds_unique hx h0)

/-- A hyperplane through the origin is Lebesgue-null. -/
lemma volume_hyperplane {ν : EuclideanSpace ℝ (Fin n)} (hν : ν ≠ 0) :
    volume {x : EuclideanSpace ℝ (Fin n) | inner ℝ ν x = 0} = 0 := by
  have heq : {x : EuclideanSpace ℝ (Fin n) | inner ℝ ν x = 0} =
      ((ℝ ∙ ν)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := by
    ext x
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.symm
  rw [heq]
  apply Measure.addHaar_submodule
  intro htop
  have hmem : ν ∈ (ℝ ∙ ν)ᗮ := by rw [htop]; exact Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  exact hν (inner_self_eq_zero.mp hmem)

lemma isOpen_halfspace (ν : EuclideanSpace ℝ (Fin n)) :
    IsOpen {x : EuclideanSpace ℝ (Fin n) | 0 < inner ℝ ν x} := by
  exact isOpen_lt continuous_const (continuous_const.inner continuous_id)

lemma isOpen_halfspace_neg (ν : EuclideanSpace ℝ (Fin n)) :
    IsOpen {x : EuclideanSpace ℝ (Fin n) | inner ℝ ν x < 0} := by
  exact isOpen_lt (continuous_const.inner continuous_id) continuous_const

/-- At a point of the bounding hyperplane an open halfspace has volume fraction exactly `1/2`
at every positive radius (point reflection through the centre swaps the two halves). -/
lemma densityRatio_halfspace_eq_half {ν x : EuclideanSpace ℝ (Fin n)} (hν : ν ≠ 0)
    (hx : inner ℝ ν x = 0) {r : ℝ} (hr : 0 < r) :
    densityRatio {y | 0 < inner ℝ ν y} x r = 1 / 2 := by
  set H : Set (EuclideanSpace ℝ (Fin n)) := {y | 0 < inner ℝ ν y} with hH
  set H' : Set (EuclideanSpace ℝ (Fin n)) := {y | inner ℝ ν y < 0} with hH'
  set B := ball x r with hB
  have hmeas : MeasurableSet (H ∩ B) := (isOpen_halfspace ν).measurableSet.inter measurableSet_ball
  have hpre : (fun y => (x + x) - y) ⁻¹' (H ∩ B) = H' ∩ B := by
    ext y
    simp only [hH, hH', hB, mem_preimage, mem_inter_iff, mem_setOf_eq, mem_ball, dist_eq_norm,
      inner_sub_right, inner_add_right, hx, zero_add, zero_sub, neg_pos]
    rw [show x + x - y - x = -(y - x) by abel, norm_neg]
  have hswap : volume (H' ∩ B) = volume (H ∩ B) := by
    rw [← hpre]
    have e : (fun y => (x + x) - y) ⁻¹' (H ∩ B) = -((fun h => (x + x) + h) ⁻¹' (H ∩ B)) := by
      ext y
      simp [sub_eq_add_neg]
    rw [e, Measure.measure_neg, measure_preimage_add]
  have hsplit : B \ {y | inner ℝ ν y = 0} = (H ∩ B) ∪ (H' ∩ B) := by
    ext y
    simp only [hH, hH', mem_diff, mem_setOf_eq, mem_union, mem_inter_iff]
    constructor
    · rintro ⟨hyB, hy0⟩
      rcases lt_or_gt_of_ne hy0 with h | h
      · exact Or.inr ⟨h, hyB⟩
      · exact Or.inl ⟨h, hyB⟩
    · rintro (⟨h, hyB⟩ | ⟨h, hyB⟩)
      · exact ⟨hyB, h.ne'⟩
      · exact ⟨hyB, h.ne⟩
  have hdisj : Disjoint (H ∩ B) (H' ∩ B) :=
    disjoint_left.mpr fun y hy hy' =>
      lt_asymm (show 0 < inner ℝ ν y from hy.1) (show inner ℝ ν y < 0 from hy'.1)
  have hH'meas : MeasurableSet (H' ∩ B) :=
    (isOpen_halfspace_neg ν).measurableSet.inter measurableSet_ball
  have hdiff : volume (B \ {y | inner ℝ ν y = 0}) = volume B :=
    measure_diff_null (volume_hyperplane hν)
  have hvolB : volume B = volume (H ∩ B) + volume (H ∩ B) := by
    rw [← hdiff, hsplit, measure_union hdisj hH'meas, hswap]
  have hfin : volume (H ∩ B) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hne : volume (H ∩ B) ≠ 0 := by
    intro h0
    have hb : 0 < volume B := measure_ball_pos volume x hr
    rw [hvolB, h0, add_zero] at hb
    exact lt_irrefl _ hb
  have ht : (volume (H ∩ B)).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨hne, hfin⟩
  have key : densityRatio H x r = (volume (H ∩ B)).toReal / (volume B).toReal := rfl
  rw [key, hvolB, ENNReal.toReal_add hfin hfin]
  rw [← two_mul, div_mul_eq_div_div_swap, div_self ht]

/-- **An open halfspace is its own density-one representative.** -/
theorem densityOne_halfspace {ν : EuclideanSpace ℝ (Fin n)} (hν : ν ≠ 0) :
    densityOne {x : EuclideanSpace ℝ (Fin n) | 0 < inner ℝ ν x} = {x | 0 < inner ℝ ν x} := by
  ext x
  constructor
  · intro hx
    by_contra hx'
    have hx'' : ¬ 0 < inner ℝ ν x := hx'
    rcases (not_lt.mp hx'').lt_or_eq with hneg | hzero
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_halfspace_neg ν) x hneg
      exact not_mem_densityOne_of_disjoint_ball hr
        (disjoint_left.mpr fun y hy hy' =>
          lt_asymm (show inner ℝ ν y < 0 from hball hy) (show 0 < inner ℝ ν y from hy')) hx
    · have h0 : Tendsto (densityRatio {y | 0 < inner ℝ ν y} x) (𝓝[>] 0) (𝓝 (1 / 2)) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs =>
          (densityRatio_halfspace_eq_half hν hzero hs).symm)
      have := tendsto_nhds_unique hx h0
      norm_num at this
  · intro hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_halfspace ν) x hx
    exact mem_densityOne_of_ball_subset hr hball

/-- A preconnected open halfspace missing the frontier of `D` lies inside `D` or misses `D`. -/
lemma halfspace_subset_or_disjoint {D : Set (EuclideanSpace ℝ (Fin n))}
    {w : EuclideanSpace ℝ (Fin n)} (hfr : ∀ y ∈ frontier D, inner ℝ w y = 0) :
    {x | 0 < inner ℝ w x} ⊆ D ∨ Disjoint {x | 0 < inner ℝ w x} D := by
  have hpc : IsPreconnected {x : EuclideanSpace ℝ (Fin n) | 0 < inner ℝ w x} := by
    exact (convex_halfSpace_gt (f := fun x => inner ℝ w x)
      ⟨fun x y => inner_add_right w x y, fun c x => real_inner_smul_right w x c⟩ 0).isPreconnected
  have hcover : {x | 0 < inner ℝ w x} ⊆ interior D ∪ (closure D)ᶜ := by
    intro x hx
    by_cases hi : x ∈ interior D
    · exact Or.inl hi
    · exact Or.inr fun hc => (show 0 < inner ℝ w x from hx).ne' (hfr x ⟨hc, hi⟩)
  have hdisj : Disjoint (interior D) (closure D)ᶜ :=
    disjoint_left.mpr fun x hx hc => hc (subset_closure (interior_subset hx))
  rcases hpc.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl hdisj hcover with h | h
  · exact Or.inl (h.trans interior_subset)
  · exact Or.inr (disjoint_left.mpr fun x hx hxD => h hx (subset_closure hxD))

/-- Normalising the normal vector does not change the open halfspace. -/
lemma halfspace_normalize {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) :
    ‖‖w‖⁻¹ • w‖ = 1 ∧
      {x : EuclideanSpace ℝ (Fin n) | 0 < inner ℝ (‖w‖⁻¹ • w) x} = {x | 0 < inner ℝ w x} := by
  have hpos : (0 : ℝ) < ‖w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw)
  refine ⟨?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
  · ext x
    simp only [mem_setOf_eq, real_inner_smul_left]
    exact mul_pos_iff_of_pos_left hpos

/-- **Frontier in a hyperplane forces a halfspace** (two-sided form).  If the frontier of the
density-one representative of a measurable set `S` lies in the hyperplane `ν^⊥` and both `S` and
its complement have positive volume, then `densityOne S` is one of the two open halfspaces
bounded by `ν^⊥`. -/
theorem densityOne_eq_halfspace_or_of_frontier_subset (hn : 0 < n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    {ν : EuclideanSpace ℝ (Fin n)} (hν : ν ≠ 0)
    (hfr : frontier (densityOne S) ⊆ {x | inner ℝ ν x = 0})
    (hnt : 0 < volume S ∧ 0 < volume Sᶜ) :
    densityOne S = {x | 0 < inner ℝ ν x} ∨ densityOne S = {x | 0 < inner ℝ (-ν) x} := by
  set D := densityOne S with hD
  have hDS : D =ᵐ[volume] S := densityOne_ae_eq hn hS.nullMeasurableSet
  have hDD : densityOne D = D := densityOne_congr_ae hDS
  have hP : volume {x : EuclideanSpace ℝ (Fin n) | inner ℝ ν x = 0} = 0 := volume_hyperplane hν
  have hneg : ∀ x : EuclideanSpace ℝ (Fin n), inner ℝ (-ν) x = -inner ℝ ν x :=
    fun x => inner_neg_left ν x
  have hA := halfspace_subset_or_disjoint (D := D) (w := ν) fun y hy => hfr hy
  have hB := halfspace_subset_or_disjoint (D := D) (w := -ν) fun y hy => by
    rw [hneg, show inner ℝ ν y = 0 from hfr hy, neg_zero]
  have htri : ∀ x : EuclideanSpace ℝ (Fin n),
      0 < inner ℝ ν x ∨ 0 < inner ℝ (-ν) x ∨ inner ℝ ν x = 0 := fun x => by
    rw [hneg]
    rcases lt_trichotomy 0 (inner ℝ ν x) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h.symm)
    · exact Or.inr (Or.inl (neg_pos.mpr h))
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · -- both halfspaces inside: the complement is null
    exfalso
    have hc : volume Dᶜ = 0 := by
      refine measure_mono_null (fun x hx => ?_) hP
      rcases htri x with h | h | h
      · exact absurd (hA h) hx
      · exact absurd (hB h) hx
      · exact h
    have : volume Sᶜ = 0 := by rw [← measure_congr hDS.compl]; exact hc
    exact hnt.2.ne' this
  · left
    have hae : D =ᵐ[volume] {x | 0 < inner ℝ ν x} := by
      rw [ae_eq_set]
      refine ⟨measure_mono_null (fun x hx => ?_) hP, ?_⟩
      · rcases htri x with h | h | h
        · exact absurd h hx.2
        · exact absurd hx.1 (disjoint_left.mp hB h)
        · exact h
      · rw [diff_eq_empty.mpr hA, measure_empty]
    calc D = densityOne D := hDD.symm
      _ = densityOne {x | 0 < inner ℝ ν x} := densityOne_congr_ae hae
      _ = {x | 0 < inner ℝ ν x} := densityOne_halfspace hν
  · right
    have hae : D =ᵐ[volume] {x | 0 < inner ℝ (-ν) x} := by
      rw [ae_eq_set]
      refine ⟨measure_mono_null (fun x hx => ?_) hP, ?_⟩
      · rcases htri x with h | h | h
        · exact absurd hx.1 (disjoint_left.mp hA h)
        · exact absurd h hx.2
        · exact h
      · rw [diff_eq_empty.mpr hB, measure_empty]
    calc D = densityOne D := hDD.symm
      _ = densityOne {x | 0 < inner ℝ (-ν) x} := densityOne_congr_ae hae
      _ = {x | 0 < inner ℝ (-ν) x} := densityOne_halfspace (neg_ne_zero.mpr hν)
  · -- both halfspaces outside: the set is null
    exfalso
    have hc : volume D = 0 := by
      refine measure_mono_null (fun x hx => ?_) hP
      rcases htri x with h | h | h
      · exact absurd hx (disjoint_left.mp hA h)
      · exact absurd hx (disjoint_left.mp hB h)
      · exact h
    have : volume S = 0 := by rw [← measure_congr hDS]; exact hc
    exact hnt.1.ne' this

/-- **Frontier in a hyperplane forces a halfspace** (unit-normal form). -/
theorem densityOne_eq_halfspace_of_frontier_subset (hn : 0 < n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    {ν : EuclideanSpace ℝ (Fin n)} (hν : ν ≠ 0)
    (hfr : frontier (densityOne S) ⊆ {x | inner ℝ ν x = 0})
    (hnt : 0 < volume S ∧ 0 < volume Sᶜ) :
    ∃ μ : EuclideanSpace ℝ (Fin n), ‖μ‖ = 1 ∧ inner ℝ μ ν ≠ 0 ∧
      densityOne S = {x | 0 < inner ℝ μ x} := by
  have hνν : inner ℝ ν ν ≠ 0 := inner_self_ne_zero.mpr hν
  rcases densityOne_eq_halfspace_or_of_frontier_subset hn hS hν hfr hnt with h | h
  · obtain ⟨h1, h2⟩ := halfspace_normalize hν
    refine ⟨‖ν‖⁻¹ • ν, h1, ?_, h.trans h2.symm⟩
    rw [real_inner_smul_left]
    exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hν)) hνν
  · have hν' : -ν ≠ 0 := neg_ne_zero.mpr hν
    obtain ⟨h1, h2⟩ := halfspace_normalize hν'
    refine ⟨‖-ν‖⁻¹ • -ν, h1, ?_, h.trans h2.symm⟩
    rw [real_inner_smul_left, inner_neg_left]
    exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hν')) (neg_ne_zero.mpr hνν)

/-- For a dilation-invariant set, a hyperplane containing the link of the frontier contains the
whole frontier. -/
lemma frontier_subset_hyperplane_of_link {D : Set (EuclideanSpace ℝ (Fin n))}
    (hcone : IsDilationInvariant D) {ν : EuclideanSpace ℝ (Fin n)}
    (hlink : link (frontier D) ⊆ {x | inner ℝ ν x = 0}) :
    frontier D ⊆ {x | inner ℝ ν x = 0} := by
  intro x hx
  by_cases h0 : x = 0
  · subst h0
    simp
  · have hpos : (0 : ℝ) < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr h0)
    have hmem : ‖x‖⁻¹ • x ∈ link (frontier D) :=
      mem_link_iff.mpr ⟨hcone.frontier.smul_mem hpos hx,
        by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]⟩
    have := hlink hmem
    simp only [mem_setOf_eq, real_inner_smul_right] at this ⊢
    exact (mul_eq_zero.mp this).resolve_left hpos.ne'

/-- **Blueprint `thm:cone-3d`, geometric endgame.**  A nontrivial dilation-invariant density-one
representative whose frontier has its link inside a great sphere `ν^⊥ ∩ S^{n-1}` is an open
halfspace. -/
theorem densityOne_eq_halfspace_of_link (hn : 0 < n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (hcone : IsDilationInvariant (densityOne S))
    {ν : EuclideanSpace ℝ (Fin n)} (hν : ν ≠ 0)
    (hlink : link (frontier (densityOne S)) ⊆ {x | inner ℝ ν x = 0})
    (hnt : 0 < volume S ∧ 0 < volume Sᶜ) :
    ∃ μ : EuclideanSpace ℝ (Fin n), ‖μ‖ = 1 ∧ densityOne S = {x | 0 < inner ℝ μ x} := by
  obtain ⟨μ, h1, -, h3⟩ := densityOne_eq_halfspace_of_frontier_subset hn hS hν
    (frontier_subset_hyperplane_of_link hcone hlink) hnt
  exact ⟨μ, h1, h3⟩

/-- Equality form: the link of the frontier is exactly a great sphere. -/
theorem densityOne_eq_halfspace_of_link_eq (hn : 0 < n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (hcone : IsDilationInvariant (densityOne S))
    {ν : EuclideanSpace ℝ (Fin n)} (hν : ν ≠ 0)
    (hlink : link (frontier (densityOne S)) = {x | inner ℝ ν x = 0} ∩ sphere 0 1)
    (hnt : 0 < volume S ∧ 0 < volume Sᶜ) :
    ∃ μ : EuclideanSpace ℝ (Fin n), ‖μ‖ = 1 ∧ densityOne S = {x | 0 < inner ℝ μ x} :=
  densityOne_eq_halfspace_of_link hn hS hcone hν (hlink.trans_subset inter_subset_left) hnt

end LiquidDrop
