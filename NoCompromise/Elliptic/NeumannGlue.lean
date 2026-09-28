import NoCompromise.Elliptic.NeumannLocalize

/-!
# Gluing an interior representative with local boundary representatives

Step (5) of the passage from the weak ABP Neumann solution to a classical one: an interior
C² representative of an a.e. class on an open set `G`, together with, near each boundary
point, a C¹ function on an open neighbourhood that represents the same class on the part of
`G` inside it and has prescribed derivative `g` in the direction `ν` on the boundary, glue to
one function that is C² in `G`, C¹ on `closure G`, and has the prescribed derivative within
`closure G` on `frontier G`. The only geometric input is unique differentiability of
`closure G` at boundary points.
-/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology

namespace LiquidDrop

/-- Two continuous functions agreeing on `G ∩ W` agree at every point of `closure G ∩ W`
where both are continuous, for `W` open. -/
lemma neumann_glue_eq_of_closure {G W : Set AmbientSpace} (hW : IsOpen W)
    {f g : AmbientSpace → ℝ} {x : AmbientSpace} (hx : x ∈ closure G) (hxW : x ∈ W)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (he : EqOn f g (G ∩ W)) :
    f x = g x := by
  have hcl : x ∈ closure (W ∩ G) := hW.inter_closure ⟨hxW, hx⟩
  have hne : (𝓝[W ∩ G] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hf' : Tendsto f (𝓝[W ∩ G] x) (𝓝 (f x)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have hg' : Tendsto g (𝓝[W ∩ G] x) (𝓝 (g x)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  have hfg : Tendsto g (𝓝[W ∩ G] x) (𝓝 (f x)) :=
    hf'.congr' (eventually_nhdsWithin_of_forall fun y hy => he ⟨hy.2, hy.1⟩)
  exact tendsto_nhds_unique hfg hg'

/-- The gluing theorem. `z` is any function (an a.e. representative of the weak solution),
`v₀` its interior C² representative; `ν` and `g` are the direction and the prescribed
derivative on the boundary. -/
theorem neumann_glue_c1_closure {G : Set AmbientSpace} (hGo : IsOpen G)
    {z v₀ g : AmbientSpace → ℝ} {ν : AmbientSpace → AmbientSpace}
    (hv₀ : ContDiffOn ℝ 2 v₀ G) (hz₀ : z =ᵐ[volume.restrict G] v₀)
    (hloc : ∀ p ∈ frontier G, ∃ V : Set AmbientSpace, ∃ w : AmbientSpace → ℝ,
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 1 w V ∧ z =ᵐ[volume.restrict (G ∩ V)] w ∧
      ∀ x ∈ frontier G ∩ V, fderiv ℝ w x (ν x) = g x)
    (huniq : ∀ x ∈ frontier G, UniqueDiffWithinAt ℝ (closure G) x) :
    ∃ v : AmbientSpace → ℝ, EqOn v v₀ G ∧ z =ᵐ[volume.restrict G] v ∧
      ContDiffOn ℝ 2 v G ∧ ContDiffOn ℝ 1 v (closure G) ∧
      ∀ x ∈ frontier G, fderivWithin ℝ v (closure G) x (ν x) = g x := by
  classical
  choose! V w hV hpV hw hzw hν using hloc
  let v : AmbientSpace → ℝ := fun x => if x ∈ G then v₀ x else w x x
  have hvG : EqOn v v₀ G := fun x hx => by simp only [v, hx, ↓reduceIte]
  have hfront : frontier G = closure G \ G := hGo.frontier_eq
  -- On `G ∩ V p` the interior representative and the local one agree.
  have hint (p) (hp : p ∈ frontier G) : EqOn v₀ (w p) (G ∩ V p) := by
    have hae : v₀ =ᵐ[volume.restrict (G ∩ V p)] w p :=
      (show z =ᵐ[volume.restrict (G ∩ V p)] v₀ from
        ae_restrict_of_ae_restrict_of_subset inter_subset_left hz₀).symm.trans (hzw p hp)
    exact Measure.eqOn_open_of_ae_eq hae (hGo.inter (hV p hp))
      (hv₀.continuousOn.mono inter_subset_left)
      ((hw p hp).continuousOn.mono inter_subset_right)
  have hwcont (p) (hp : p ∈ frontier G) (x) (hx : x ∈ V p) : ContinuousAt (w p) x :=
    ((hw p hp).continuousOn.continuousAt ((hV p hp).mem_nhds hx))
  -- The glued function agrees with each local representative on `closure G ∩ V p`.
  have hloc (p) (hp : p ∈ frontier G) : EqOn v (w p) (closure G ∩ V p) := by
    intro x hx
    by_cases hxG : x ∈ G
    · rw [hvG hxG]
      exact hint p hp ⟨hxG, hx.2⟩
    · have hxf : x ∈ frontier G := by rw [hfront]; exact ⟨hx.1, hxG⟩
      change (if x ∈ G then v₀ x else w x x) = w p x
      simp only [hxG, ↓reduceIte]
      apply neumann_glue_eq_of_closure ((hV x hxf).inter (hV p hp)) hx.1 ⟨hpV x hxf, hx.2⟩
        (hwcont x hxf x (hpV x hxf)) (hwcont p hp x hx.2)
      intro y hy
      rw [← hint x hxf ⟨hy.1, hy.2.1⟩, hint p hp ⟨hy.1, hy.2.2⟩]
  have hev (p) (hp : p ∈ frontier G) : v =ᶠ[𝓝[closure G] p] w p := by
    filter_upwards [inter_mem_nhdsWithin (closure G) ((hV p hp).mem_nhds (hpV p hp))]
      with x hx using hloc p hp hx
  have hvp (p) (hp : p ∈ frontier G) : v p = w p p :=
    hloc p hp ⟨frontier_subset_closure hp, hpV p hp⟩
  refine ⟨v, hvG, ?_, hv₀.congr hvG, ?_, ?_⟩
  · filter_upwards [hz₀, ae_restrict_mem hGo.measurableSet] with x hx hxG
    rw [hx, hvG hxG]
  · intro x hx
    by_cases hxG : x ∈ G
    · have he : v =ᶠ[𝓝 x] v₀ :=
        Filter.eventually_of_mem (hGo.mem_nhds hxG) (fun y hy => hvG hy)
      have hc : ContDiffAt ℝ 1 v₀ x :=
        ((hv₀.contDiffAt (hGo.mem_nhds hxG)).of_le (by norm_num))
      exact (hc.congr_of_eventuallyEq he).contDiffWithinAt
    · have hxf : x ∈ frontier G := by rw [hfront]; exact ⟨hx, hxG⟩
      have hc : ContDiffAt ℝ 1 (w x) x :=
        (hw x hxf).contDiffAt ((hV x hxf).mem_nhds (hpV x hxf))
      exact hc.contDiffWithinAt.congr_of_eventuallyEq (hev x hxf) (hvp x hxf)
  · intro x hxf
    have hc : ContDiffAt ℝ 1 (w x) x :=
      (hw x hxf).contDiffAt ((hV x hxf).mem_nhds (hpV x hxf))
    have hd : HasFDerivWithinAt v (fderiv ℝ (w x) x) (closure G) x :=
      ((hc.differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt).congr_of_eventuallyEq
        (hev x hxf) (hvp x hxf)
    rw [hd.fderivWithin (huniq x hxf)]
    exact hν x hxf x ⟨hxf, hpV x hxf⟩

end LiquidDrop
