import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Slabs and levels of the capacitary potential have compact closure off `K`

Chapter 30 input for chapter 31 (`hslabs`, `hlevels` of
`CapacitaryK.capacitary_inequalities_of_harmonic`). For a continuous `u` on `ℝ³` with `u = 1` on
the closed set `K` and `u → 0` at infinity, every set on which `a ≤ u ≤ b`, `0 < a ≤ b < 1`, has
compact closure contained in `Kᶜ`. In particular this holds for the slabs `{a < u < b}`,
`{a < u ≤ b}` and the levels `{u = t}`, `0 < t < 1`. If moreover `K` is compact and nonempty and
`Kᶜ` is preconnected, every level `{u = t}`, `0 < t < 1`, is nonempty.
-/

noncomputable section
open Set Filter Topology

namespace LiquidDrop

variable {K : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → ℝ}

/-- A superlevel `{u ≥ a}`, `a > 0`, of a continuous function tending to zero at infinity is
compact. -/
theorem isCompact_preimage_Ici_of_tendsto_zero (hu : Continuous u)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    IsCompact (u ⁻¹' Ici a) := by
  obtain ⟨C, hC, hCsub⟩ := mem_cocompact.mp (hinf.eventually (gt_mem_nhds ha))
  refine hC.of_isClosed_subset (isClosed_Ici.preimage hu) ?_
  intro x hx
  by_contra hxC
  exact (not_lt.mpr (show a ≤ u x from hx)) (hCsub hxC)

/-- Any set on which `a ≤ u ≤ b`, with `0 < a` and `b < 1`, has compact closure in `Kᶜ`. -/
theorem capacitary_closure_compact_subset (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) {a b : ℝ} (ha : 0 < a)
    (hb1 : b < 1) {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : S ⊆ u ⁻¹' Icc a b) :
    IsCompact (closure S) ∧ closure S ⊆ Kᶜ := by
  have hcl : closure S ⊆ u ⁻¹' Icc a b :=
    closure_minimal hS (isClosed_Icc.preimage hu)
  refine ⟨(isCompact_preimage_Ici_of_tendsto_zero hu hinf ha).of_isClosed_subset
    isClosed_closure (hcl.trans fun x hx => (show u x ∈ Icc a b from hx).1), ?_⟩
  intro x hx hxK
  have h := (show u x ∈ Icc a b from hcl hx).2
  rw [hb x hxK] at h
  linarith

/-- Open slabs `Kᶜ ∩ {a < u < b}`, `0 < a < b < 1`, have compact closure in `Kᶜ`
(the hypothesis `hslabs` of chapter 31, with `U = Kᶜ`). -/
theorem capacitary_slab_Ioo (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      IsCompact (closure (Kᶜ ∩ u ⁻¹' Ioo a b)) ∧ closure (Kᶜ ∩ u ⁻¹' Ioo a b) ⊆ Kᶜ :=
  fun _ _ ha _ hb1 => capacitary_closure_compact_subset hu hb hinf ha hb1
    fun _ hx => Ioo_subset_Icc_self hx.2

/-- Half-open slabs `{a < u ≤ b}`, `0 < a ≤ b < 1`, have compact closure in `Kᶜ`. -/
theorem capacitary_slab_Ioc (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) {a b : ℝ} (ha : 0 < a)
    (hb1 : b < 1) :
    IsCompact (closure {x | a < u x ∧ u x ≤ b}) ∧ closure {x | a < u x ∧ u x ≤ b} ⊆ Kᶜ :=
  capacitary_closure_compact_subset hu hb hinf ha hb1 fun _ hx => ⟨hx.1.le, hx.2⟩

/-- Levels `{u = t}`, `0 < t < 1`, are compact subsets of `Kᶜ`. -/
theorem capacitary_level_compact (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) : u ⁻¹' {t} ⊆ Kᶜ ∧ IsCompact (u ⁻¹' {t}) := by
  have hS : u ⁻¹' {t} ⊆ u ⁻¹' Icc t t := by simp
  obtain ⟨hc, hsub⟩ := capacitary_closure_compact_subset hu hb hinf ht0 ht1 hS
  have hclosed : IsClosed (u ⁻¹' {t}) := isClosed_singleton.preimage hu
  rw [hclosed.closure_eq] at hc hsub
  exact ⟨hsub, hc⟩

/-- Levels `{u = t}`, `0 < t < 1`, are nonempty when `K` is compact and nonempty and `Kᶜ` is
preconnected (as for the filled hull). -/
theorem capacitary_level_nonempty (hK : IsCompact K) (hKne : K.Nonempty)
    (hconn : IsPreconnected Kᶜ) (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) : (u ⁻¹' {t}).Nonempty := by
  -- a far point with `u < t`
  have hfar : ∀ᶠ x in cocompact (EuclideanSpace ℝ (Fin 3)), u x < t ∧ x ∈ Kᶜ :=
    (hinf.eventually (gt_mem_nhds ht0)).and hK.compl_mem_cocompact
  obtain ⟨y, hyt, hyK⟩ := hfar.exists
  -- a point of `Kᶜ` near `frontier K` with `u > t`
  have hKne' : (Kᶜ).Nonempty := ⟨y, hyK⟩
  have hKuniv : Kᶜ ≠ univ := fun h => by
    obtain ⟨z, hz⟩ := hKne
    exact (h ▸ mem_univ z : z ∈ Kᶜ) hz
  obtain ⟨p, hp⟩ := nonempty_frontier_iff.mpr ⟨hKne', hKuniv⟩
  have hpK : p ∈ K := by
    rw [frontier_compl] at hp
    exact hK.isClosed.frontier_subset hp
  have hnhds : u ⁻¹' Ioi t ∈ 𝓝 p :=
    hu.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by rw [hb p hpK]; exact ht1))
  obtain ⟨z, hzt, hzK⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hp) _ hnhds
  obtain ⟨x, -, hx⟩ := hconn.intermediate_value hyK hzK hu.continuousOn
    ⟨hyt.le, (show t < u z from hzt).le⟩
  exact ⟨x, hx⟩

/-- The hypothesis `hlevels` of chapter 31, with `U = Kᶜ`. -/
theorem capacitary_levels (hK : IsCompact K) (hKne : K.Nonempty) (hconn : IsPreconnected Kᶜ)
    (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∀ t : ℝ, 0 < t → t < 1 →
      u ⁻¹' {t} ⊆ Kᶜ ∧ IsCompact (u ⁻¹' {t}) ∧ (u ⁻¹' {t}).Nonempty := fun _ ht0 ht1 =>
  ⟨(capacitary_level_compact hu hb hinf ht0 ht1).1,
    (capacitary_level_compact hu hb hinf ht0 ht1).2,
    capacitary_level_nonempty hK hKne hconn hu hb hinf ht0 ht1⟩

end LiquidDrop
