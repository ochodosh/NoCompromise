module

public import NoCompromise.Flow.FlowCkHigher

@[expose] public section

/-!
# `C^k` localization of vector fields

`cor:flow-manifold`, `thm:flow-box`: a `C^k` field (`k : ℕ∞`, including `k = ∞`) on an open
subset `U` of a finite-dimensional real space agrees, on an open neighbourhood of any compact
`K ⊆ U`, with a compactly supported globally `C^k` field. For `k ≥ 1` the localized field is
bounded and globally Lipschitz, so `contDiff_globalFlow_uncurry` gives its jointly `C^k` flow.
-/

open Set Filter
open scoped NNReal Topology

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : E → E} {U K : Set E}

/-- `C^k` version of `exists_compactSupport_eq_near`: localize a `C^k` field near a compact
set in its open domain by a smooth partition-of-unity cutoff. -/
theorem exists_compactSupport_eq_near_contDiff {k : ℕ∞} (hU : IsOpen U)
    (hX : ContDiffOn ℝ k X U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ Y : E → E, ContDiff ℝ k Y ∧ HasCompactSupport Y ∧
      ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn Y X V := by
  obtain ⟨W, hWo, hKW, hWc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨A, hAo, hKA, hAU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hWo).mem_nhdsSet.mpr (subset_inter hKU hKW))
  obtain ⟨V, hVo, hKV, hVA⟩ := hK.exists_isOpen_closure_subset (hAo.mem_nhdsSet.mpr hKA)
  obtain ⟨f, hfs, hf, hf01⟩ := hAo.exists_contDiff_support_eq (n := k)
  obtain ⟨g, hgs, hg, hg01⟩ := isClosed_closure.isOpen_compl.exists_contDiff_support_eq
    (n := k) (s := (closure V)ᶜ)
  have hpos (x : E) : 0 < f x + g x := by
    have hf0 := (hf01 (mem_range_self x)).1
    have hg0 := (hg01 (mem_range_self x)).1
    by_cases hx : x ∈ A
    · have hn : f x ≠ 0 := by simpa only [← hfs, Function.mem_support] using hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hf0 (Ne.symm hn)) hg0
    · have hn : g x ≠ 0 := by
        rw [← Function.mem_support, hgs]
        exact fun h => hx (hVA h)
      exact add_pos_of_nonneg_of_pos hf0 (lt_of_le_of_ne hg0 (Ne.symm hn))
  let ρ : E → ℝ := fun x => f x / (f x + g x)
  have hρ : ContDiff ℝ k ρ := hf.div (hf.add hg) (fun x => (hpos x).ne')
  have hρs : Function.support ρ ⊆ A := by
    intro x hx
    apply hfs.subset
    contrapose! hx
    simp [ρ, Function.mem_support] at *
    simp [hx]
  have hρc : HasCompactSupport ρ :=
    hWc.of_isClosed_subset isClosed_closure
      ((closure_mono hρs).trans (hAU.trans inter_subset_right |>.trans subset_closure))
  refine ⟨fun x => ρ x • X x, ?_, hρc.smul_right, V, hVo, hKV,
    (subset_closure.trans hVA).trans (subset_closure.trans (hAU.trans inter_subset_left)), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ closure A
    · exact hρ.contDiffAt.smul ((hX x ((hAU hx).1)).contDiffAt (hU.mem_nhds (hAU hx).1))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      have hyρ : ρ y = 0 := by
        by_contra hn
        exact hy (subset_closure (hρs hn))
      simp [hyρ]
  · intro x hx
    have hgx : g x = 0 := by
      rw [← Function.notMem_support, hgs]
      exact not_not.mpr (subset_closure hx)
    have hfx : f x ≠ 0 := by
      rw [← Function.mem_support, hfs]
      exact hVA (subset_closure hx)
    simp [ρ, hgx, hfx]

end LiquidDrop
