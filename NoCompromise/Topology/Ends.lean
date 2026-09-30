module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Two ends of the real line

We count the components of a compact complement whose closures are noncompact.
The count is invariant under homeomorphism, and is two for the real line.
-/

namespace LiquidDrop

open Set

/-- The unbounded components of the complement of `K`: components of `Kᶜ` whose
closure is not compact. -/
def unboundedComponents {X : Type*} [TopologicalSpace X] (K : Set X) : Set (Set X) :=
  {U | ∃ x ∈ Kᶜ, U = connectedComponentIn Kᶜ x ∧ ¬ IsCompact (closure U)}

/-- `X` has exactly two ends (Freudenthal–Hopf count): for every compact `K` the
complement has at most two unbounded components, and for some compact `K` exactly two. -/
def HasExactlyTwoEnds (X : Type*) [TopologicalSpace X] : Prop :=
  (∀ K : Set X, IsCompact K → (unboundedComponents K).encard ≤ 2) ∧
    ∃ K : Set X, IsCompact K ∧ (unboundedComponents K).encard = 2

/-- A compact ambient space has no components with noncompact closure. -/
theorem unboundedComponents_eq_empty_of_compactSpace {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (K : Set X) :
    unboundedComponents K = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro U ⟨x, hx, hU, hnc⟩
  exact hnc isClosed_closure.isCompact

/-- A homeomorphism carries components of a set to components of its image. -/
theorem Homeomorph.image_connectedComponentIn_ends {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {S : Set X} {x : X} (hx : x ∈ S) :
    e '' connectedComponentIn S x = connectedComponentIn (e '' S) (e x) := by
  apply Subset.antisymm (e.continuous.continuousOn.image_connectedComponentIn_subset hx)
  intro y hy
  have h := e.symm.continuous.continuousOn.image_connectedComponentIn_subset
    (mem_image_of_mem e hx)
  have hy' := h (mem_image_of_mem e.symm hy)
  have hy'' : e.symm y ∈ connectedComponentIn S x := by
    simpa only [← image_comp, e.symm_comp_self, image_id, e.symm_apply_apply] using hy'
  exact ⟨e.symm y, hy'', e.apply_symm_apply y⟩

/-- Homeomorphic images preserve membership in the set of unbounded components. -/
theorem Homeomorph.image_mem_unboundedComponents {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {K U : Set X} (hU : U ∈ unboundedComponents K) :
    e '' U ∈ unboundedComponents (e '' K) := by
  obtain ⟨x, hx, rfl, hnc⟩ := hU
  refine ⟨e x, ?_, ?_, ?_⟩
  · rw [← e.image_compl]
    exact mem_image_of_mem e hx
  · rw [Homeomorph.image_connectedComponentIn_ends e hx, e.image_compl]
  · rwa [← e.image_closure, e.isCompact_image]

/-- The image operation gives a bijection on unbounded components. -/
theorem Homeomorph.image_unboundedComponents {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (K : Set X) :
    (fun U : Set X => e '' U) '' unboundedComponents K =
      unboundedComponents (e '' K) := by
  apply Subset.antisymm
  · rintro _ ⟨U, hU, rfl⟩
    exact Homeomorph.image_mem_unboundedComponents e hU
  · intro U hU
    refine ⟨e.symm '' U, ?_, e.image_symm_image U⟩
    simpa only [← image_comp, e.symm_comp_self, image_id] using
      Homeomorph.image_mem_unboundedComponents e.symm hU

/-- The count of unbounded components is unchanged by a homeomorphism. -/
theorem Homeomorph.encard_unboundedComponents_image {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (K : Set X) :
    (unboundedComponents (e '' K)).encard = (unboundedComponents K).encard := by
  rw [← Homeomorph.image_unboundedComponents e]
  exact e.injective.image_injective.encard_image _

/-- Having exactly two ends is invariant under homeomorphism. -/
theorem Homeomorph.hasExactlyTwoEnds {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (h : HasExactlyTwoEnds X) : HasExactlyTwoEnds Y := by
  constructor
  · intro K hK
    have hc := (Homeomorph.encard_unboundedComponents_image e (e.symm '' K)).le.trans
      (h.1 _ (hK.image e.symm.continuous))
    simpa only [← image_comp, e.self_comp_symm, image_id] using hc
  · obtain ⟨K, hK, hc⟩ := h.2
    exact ⟨e '' K, hK.image e.continuous,
      (Homeomorph.encard_unboundedComponents_image e K).trans hc⟩

/-- A compact subset of the real line has at most two unbounded complementary components. -/
theorem encard_unboundedComponents_real_le_two {K : Set ℝ} (hK : IsCompact K) :
    (unboundedComponents K).encard ≤ 2 := by
  obtain ⟨a, ha⟩ := hK.bddBelow
  obtain ⟨b, hb⟩ := hK.bddAbove
  have hleft : Iio a ⊆ Kᶜ := fun y hy hyK => (not_lt_of_ge (ha hyK)) hy
  have hright : Ioi b ⊆ Kᶜ := fun y hy hyK => (not_lt_of_ge (hb hyK)) hy
  have hsub : unboundedComponents K ⊆
      {connectedComponentIn Kᶜ (a - 1), connectedComponentIn Kᶜ (b + 1)} := by
    rintro U ⟨x, hx, rfl, hnc⟩
    by_cases hbelow : BddBelow (connectedComponentIn Kᶜ x)
    · have habove : ¬ BddAbove (connectedComponentIn Kᶜ x) := by
        rintro ⟨d, hd⟩
        obtain ⟨c, hc⟩ := hbelow
        apply hnc
        exact isCompact_Icc.of_isClosed_subset isClosed_closure
          (closure_minimal (fun y hy => ⟨hc hy, hd hy⟩) isClosed_Icc)
      obtain ⟨y, hy, hby⟩ := not_bddAbove_iff.mp habove b
      apply mem_insert_of_mem
      apply mem_singleton_iff.mpr
      exact (connectedComponentIn_eq hy).trans
        (connectedComponentIn_eq
          (isPreconnected_Ioi.subset_connectedComponentIn hby hright (by simp)))
    · obtain ⟨y, hy, hya⟩ := not_bddBelow_iff.mp hbelow a
      apply mem_insert_iff.mpr
      left
      exact (connectedComponentIn_eq hy).trans
        (connectedComponentIn_eq
          (isPreconnected_Iio.subset_connectedComponentIn hya hleft (by simp)))
  exact (encard_mono hsub).trans (by
    calc
      _ ≤ ({connectedComponentIn Kᶜ (b + 1)} : Set (Set ℝ)).encard + 1 :=
        encard_insert_le _ _
      _ = 2 := by simp; rfl)

/-- Removing zero leaves the negative ray as the component of `-1`. -/
theorem connectedComponentIn_compl_zero_neg_one :
    connectedComponentIn ({0}ᶜ : Set ℝ) (-1) = Iio 0 := by
  have hx : (-1 : ℝ) ∈ ({0}ᶜ : Set ℝ) := by simp
  apply Subset.antisymm
  · intro y hy
    by_contra h
    have hy0 : 0 ≤ y := le_of_not_gt h
    have hz := isPreconnected_connectedComponentIn.Icc_subset
      (mem_connectedComponentIn hx) hy (show (0 : ℝ) ∈ Icc (-1) y from ⟨by norm_num, hy0⟩)
    exact (connectedComponentIn_subset _ _ hz) (by simp)
  · exact isPreconnected_Iio.subset_connectedComponentIn (by norm_num)
      (fun y hy => by simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_lt hy)

/-- Removing zero leaves the positive ray as the component of `1`. -/
theorem connectedComponentIn_compl_zero_one :
    connectedComponentIn ({0}ᶜ : Set ℝ) 1 = Ioi 0 := by
  have hx : (1 : ℝ) ∈ ({0}ᶜ : Set ℝ) := by simp
  apply Subset.antisymm
  · intro y hy
    by_contra h
    have hy0 : y ≤ 0 := le_of_not_gt h
    have hz := isPreconnected_connectedComponentIn.Icc_subset hy
      (mem_connectedComponentIn hx) (show (0 : ℝ) ∈ Icc y 1 from ⟨hy0, by norm_num⟩)
    exact (connectedComponentIn_subset _ _ hz) (by simp)
  · exact isPreconnected_Ioi.subset_connectedComponentIn (by norm_num)
      (fun y hy => by simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_gt hy)

/-- The real line has exactly two ends. -/
theorem hasExactlyTwoEnds_real : HasExactlyTwoEnds ℝ := by
  refine ⟨fun _ hK => encard_unboundedComponents_real_le_two hK,
    {0}, isCompact_singleton, le_antisymm (encard_unboundedComponents_real_le_two
      isCompact_singleton) ?_⟩
  have hneg : Iio (0 : ℝ) ∈ unboundedComponents {0} := by
    refine ⟨-1, by simp, connectedComponentIn_compl_zero_neg_one.symm, ?_⟩
    intro hc
    obtain ⟨a, ha⟩ := hc.bddBelow
    have := ha (subset_closure (show min a 0 - 1 ∈ Iio (0 : ℝ) by
      have := min_le_right a 0
      simp only [mem_Iio]
      linarith))
    have := min_le_left a 0
    linarith
  have hpos : Ioi (0 : ℝ) ∈ unboundedComponents {0} := by
    refine ⟨1, by simp, connectedComponentIn_compl_zero_one.symm, ?_⟩
    intro hc
    obtain ⟨b, hb⟩ := hc.bddAbove
    have := hb (subset_closure (show max b 0 + 1 ∈ Ioi (0 : ℝ) by
      have := le_max_right b 0
      simp only [mem_Ioi]
      linarith))
    have := le_max_left b 0
    linarith
  have hne : Iio (0 : ℝ) ≠ Ioi 0 := by
    intro h
    have : (-1 : ℝ) ∈ Ioi 0 := h ▸ (show (-1 : ℝ) ∈ Iio 0 by norm_num)
    norm_num at this
  rw [← encard_pair hne]
  exact encard_mono (pair_subset hneg hpos)

end LiquidDrop
