import NoCompromise.Surface.SublevelStable
import NoCompromise.Surface.MorseCount

/-!
# The attaching step of `lem:sublevel-closure`

Adjoining level points of `{h = c}` to `N := S ∩ {h < c}` joins no two components of `N`,
except through points where the local lower trace meets several components.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LiquidDrop

/-- A connected component of `F` is relatively closed in `F`. -/
theorem closure_connectedComponentIn_inter_subset {F : Set E₃} {x : E₃} :
    closure (connectedComponentIn F x) ∩ F ⊆ connectedComponentIn F x := by
  rintro z ⟨hzcl, hzF⟩
  by_cases hx : x ∈ F
  · have hpre : IsPreconnected (insert z (connectedComponentIn F x)) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
        (insert_subset hzcl subset_closure)
    have hsub : insert z (connectedComponentIn F x) ⊆ F :=
      insert_subset hzF (connectedComponentIn_subset F x)
    exact hpre.subset_connectedComponentIn
      (mem_insert_of_mem _ (mem_connectedComponentIn hx)) hsub (mem_insert z _)
  · rw [connectedComponentIn_eq_empty hx, closure_empty] at hzcl
    exact hzcl.elim

/-- `lem:sublevel-closure`, attaching step: adjoining level points does not join distinct
components of `N := S ∩ {h < c}`, provided each adjoined level point `q ∉ Z` has an open
neighbourhood `U` whose lower trace `S ∩ U ∩ {h < c}` lies in a single component of `N` and
whose level points all lie in the closure of that trace. If `C` is a preconnected subset of
`(S ∩ {h ≤ c}) \ Z` containing `x ∈ N`, then `C ∩ {h < c}` lies in the component of `N` through
`x`. The hypothesis `hlc` is local connectedness of `S`. -/
theorem preconnected_inter_levelBelow_subset_of_adj {S : Set E₃} {h : E₃ → ℝ}
    (hhc : Continuous h) {c : ℝ} {Z : Set E₃}
    (hadj : ∀ q ∈ S, h q = c → q ∉ Z → ∃ U : Set E₃, IsOpen U ∧ q ∈ U ∧
      (∀ a ∈ S ∩ U ∩ {y | h y < c}, ∀ b ∈ S ∩ U ∩ {y | h y < c},
        b ∈ connectedComponentIn (S ∩ {y | h y < c}) a) ∧
      ∀ q' ∈ S ∩ U, h q' = c → q' ∈ closure (S ∩ U ∩ {y | h y < c}))
    (hlc : ∀ z ∈ S, ∀ O : Set E₃, IsOpen O → z ∈ O →
      ∃ N ⊆ S ∩ O, IsPreconnected N ∧ N ∈ 𝓝[S] z)
    {C : Set E₃} (hC : IsPreconnected C) (hCK : C ⊆ (S ∩ {y | h y ≤ c}) \ Z)
    {x : E₃} (hxC : x ∈ C) (hxN : h x < c) :
    C ∩ {y | h y < c} ⊆ connectedComponentIn (S ∩ {y | h y < c}) x := by
  set N := S ∩ {y | h y < c} with hNdef
  set A := connectedComponentIn N x with hAdef
  set K' := (S ∩ {y | h y ≤ c}) \ Z with hK'
  have hxS : x ∈ S := (hCK hxC).1.1
  have hxA : x ∈ A := mem_connectedComponentIn ⟨hxS, hxN⟩
  have hNo : IsOpen {y : E₃ | h y < c} := isOpen_lt hhc continuous_const
  -- local step: every point of `closure A ∩ K'` has an open neighbourhood whose trace on `K'`
  -- lies in `closure A`
  have hloc : ∀ z ∈ closure A ∩ K', ∃ W : Set E₃, IsOpen W ∧ z ∈ W ∧ W ∩ K' ⊆ closure A := by
    rintro z ⟨hzcl, ⟨hzS, hzle⟩, hzZ⟩
    rcases lt_or_eq_of_le (show h z ≤ c from hzle) with hzc | hzc
    · have hzA : z ∈ A := closure_connectedComponentIn_inter_subset ⟨hzcl, hzS, hzc⟩
      obtain ⟨N', hN'sub, hN'pre, hN'nhds⟩ := hlc z hzS _ hNo hzc
      obtain ⟨W, hWo, hzW, hWsub⟩ := mem_nhdsWithin.mp hN'nhds
      have hzN' : z ∈ N' := hWsub ⟨hzW, hzS⟩
      have hN'A : N' ⊆ A := by
        rw [hAdef, connectedComponentIn_eq hzA]
        exact hN'pre.subset_connectedComponentIn hzN' hN'sub
      refine ⟨W, hWo, hzW, fun q hq => subset_closure (hN'A (hWsub ⟨hq.1, hq.2.1.1⟩))⟩
    · obtain ⟨U, hUo, hzU, hB, hcl⟩ := hadj z hzS hzc hzZ
      obtain ⟨a, haU, haA⟩ := mem_closure_iff.mp hzcl U hUo hzU
      have haS : a ∈ S := (connectedComponentIn_subset N x haA).1
      have hac : h a < c := (connectedComponentIn_subset N x haA).2
      have hBA : S ∩ U ∩ {y | h y < c} ⊆ A := by
        intro b hb
        have hbA : b ∈ connectedComponentIn N a := hB a ⟨⟨haS, haU⟩, hac⟩ b hb
        rw [hAdef, connectedComponentIn_eq haA]
        exact hbA
      refine ⟨U, hUo, hzU, ?_⟩
      rintro q ⟨hqU, ⟨hqS, hqle⟩, -⟩
      rcases lt_or_eq_of_le (show h q ≤ c from hqle) with hqc | hqc
      · exact subset_closure (hBA ⟨⟨hqS, hqU⟩, hqc⟩)
      · exact closure_mono hBA (hcl q ⟨hqS, hqU⟩ hqc)
  -- the two open sets separating `C`
  let u : Set E₃ := ⋃₀ {W | IsOpen W ∧ W ∩ K' ⊆ closure A}
  let v : Set E₃ := (closure A)ᶜ
  have hu : IsOpen u := isOpen_sUnion fun W hW => hW.1
  have hv : IsOpen v := isClosed_closure.isOpen_compl
  have huK : u ∩ K' ⊆ closure A := by
    rintro z ⟨⟨W, hW, hzW⟩, hzK⟩
    exact hW.2 ⟨hzW, hzK⟩
  have hCuv : C ⊆ u ∪ v := by
    intro z hz
    by_cases hzcl : z ∈ closure A
    · obtain ⟨W, hWo, hzW, hWsub⟩ := hloc z ⟨hzcl, hCK hz⟩
      exact Or.inl ⟨W, ⟨hWo, hWsub⟩, hzW⟩
    · exact Or.inr hzcl
  have hxu : x ∈ u := by
    obtain ⟨W, hWo, hxW, hWsub⟩ := hloc x ⟨subset_closure hxA, hCK hxC⟩
    exact ⟨W, ⟨hWo, hWsub⟩, hxW⟩
  rintro y ⟨hyC, hyc⟩
  by_contra hyA
  have hyv : y ∈ v := fun hycl =>
    hyA (closure_connectedComponentIn_inter_subset ⟨hycl, (hCK hyC).1.1, hyc⟩)
  obtain ⟨z, hzC, hzu, hzv⟩ := hC u v hu hv hCuv ⟨x, hxC, hxu⟩ ⟨y, hyC, hyv⟩
  exact hzv (huK ⟨hzu, hCK hzC⟩)

/-- `lem:level-adjacency` in the form required by `preconnected_inter_levelBelow_subset_of_adj`:
a regular level point has a neighbourhood whose lower trace lies in one component of
`S ∩ {h < c}` and adjoins every level point of the neighbourhood. -/
theorem levelBelow_adj_of_regular {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h) {c : ℝ} {q : E₃} (hq : q ∈ S) (hc : h q = c)
    (hn : ¬ IsSurfaceCriticalPoint S h q) :
    ∃ U : Set E₃, IsOpen U ∧ q ∈ U ∧
      (∀ a ∈ S ∩ U ∩ {y | h y < c}, ∀ b ∈ S ∩ U ∩ {y | h y < c},
        b ∈ connectedComponentIn (S ∩ {y | h y < c}) a) ∧
      ∀ q' ∈ S ∩ U, h q' = c → q' ∈ closure (S ∩ U ∩ {y | h y < c}) := by
  obtain ⟨U, hUo, hqU, hB, -, hcl⟩ := exists_levelAdjacency_nhds hS hh hq hc hn
  refine ⟨U, hUo, hqU, fun a ha b hb => ?_, fun q' hq' hq'c => (hcl q' hq' hq'c).1⟩
  have hsub : S ∩ U ∩ {y | h y < c} ⊆ S ∩ {y | h y < c} := fun y hy => ⟨hy.1.1, hy.2⟩
  exact hB.isPreconnected.subset_connectedComponentIn ha hsub hb

/-- `lem:sublevel-closure`, regular attaching step: adjoining regular level points does not join
distinct components of `N := S ∩ {h < c}`: if `C` is a preconnected subset of
`(S ∩ {h ≤ c}) \ Z`, all level-`c` points outside `Z` are regular, and `x ∈ C ∩ N`, then
`C ∩ {h < c}` lies in the component of `N` through `x`. -/
theorem preconnected_inter_levelBelow_subset {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h) {c : ℝ} {Z : Set E₃}
    (hreg : ∀ q ∈ S, h q = c → q ∉ Z → ¬ IsSurfaceCriticalPoint S h q)
    {C : Set E₃} (hC : IsPreconnected C) (hCK : C ⊆ (S ∩ {y | h y ≤ c}) \ Z)
    {x : E₃} (hxC : x ∈ C) (hxN : h x < c) :
    C ∩ {y | h y < c} ⊆ connectedComponentIn (S ∩ {y | h y < c}) x :=
  preconnected_inter_levelBelow_subset_of_adj hh.continuous
    (fun q hq hqc hqZ => levelBelow_adj_of_regular hS hh hq hqc (hreg q hq hqc hqZ))
    (fun _ hz _ hO hzO => hS.exists_preconnected_nhdsWithin hz hO hzO) hC hCK hxC hxN

end LiquidDrop
