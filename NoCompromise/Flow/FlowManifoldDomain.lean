module

public import NoCompromise.Flow.FlowManifoldAbstract

@[expose] public section

/-!
# The domain and regularity of the abstract maximal flow

Local regularity propagates by the group law. Connectedness of each maximal
time interval then propagates the zero-time neighbourhood to every time in
that interval.
-/

open Set Filter Function Manifold
open scoped Topology

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}

/-- Joint regularity together with a neighbourhood contained in the flow domain. -/
private def mFlowRegularAt (v : (x : M) → TangentSpace I x) (k : ℕ∞)
    (t : ℝ) (x : M) : Prop :=
  {q : ℝ × M | q.1 ∈ mMaxFlowInterval v q.2} ∈ 𝓝 (t, x) ∧
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) I k (fun q : ℝ × M => mMaxFlow v q.1 q.2) (t, x)

private theorem mFlowRegularAt_add {k : ℕ∞}
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {t s : ℝ} {x : M} (ht : mFlowRegularAt v k t x)
    (hs : mFlowRegularAt v k s (mMaxFlow v t x)) :
    mFlowRegularAt v k (s + t) x := by
  let F : ℝ × M → M := fun q => mMaxFlow v q.1 q.2
  let g : ℝ × M → ℝ × M := fun q => (q.1 - t, mMaxFlow v t q.2)
  have hslice : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I k
      (fun q : ℝ × M => mMaxFlow v t q.2) (s + t, x) :=
    ht.2.comp_of_eq (contMDiffAt_const.prodMk contMDiffAt_snd) rfl
  have hsub : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun q : ℝ × M => q.1 - t) (s + t, x) := by
    have h : ContDiffAt ℝ k (fun r : ℝ => r - t) (s + t) :=
      contDiffAt_id.sub contDiffAt_const
    exact h.contMDiffAt.comp (s + t, x)
      (contMDiffAt_fst (I := 𝓘(ℝ, ℝ)) (J := I))
  have hg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) k g (s + t, x) :=
    hsub.prodMk hslice
  have hgval : g (s + t, x) = (s, mMaxFlow v t x) := by simp [g]
  have htD : ∀ᶠ q : ℝ × M in 𝓝 (s + t, x), t ∈ mMaxFlowInterval v q.2 := by
    have h : ContinuousAt (fun q : ℝ × M => (t, q.2)) (s + t, x) :=
      continuousAt_const.prodMk continuousAt_snd
    exact h.preimage_mem_nhds ht.1
  have hsD : ∀ᶠ q : ℝ × M in 𝓝 (s + t, x),
      q.1 - t ∈ mMaxFlowInterval v (mMaxFlow v t q.2) := by
    have h := hg.continuousAt.preimage_mem_nhds (hgval.symm ▸ hs.1)
    exact h
  have hD : ∀ᶠ q : ℝ × M in 𝓝 (s + t, x), q.1 ∈ mMaxFlowInterval v q.2 := by
    filter_upwards [htD, hsD] with q hqt hqs
    simpa using (mMaxFlow_add hv hqt (q.1 - t)).1.mp hqs
  refine ⟨hD, ?_⟩
  have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I k (F ∘ g) (s + t, x) :=
    hs.2.comp_of_eq hg hgval
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [htD, hD] with q hqt hq
  have heq := (mMaxFlow_add hv hqt (q.1 - t)).2 (by simpa using hq)
  simpa [F, g] using heq.symm

private theorem mFlowRegularAt_nhds_zero [IsManifold I (⊤ : ℕ∞) M] {k : ℕ∞}
    (hk : 1 ≤ k) (hvk : CMDiff k (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x : M) :
    ∃ N ∈ 𝓝 ((0 : ℝ), x), ∀ q ∈ N, mFlowRegularAt v k q.1 q.2 := by
  obtain ⟨N, hN, hND, hNF⟩ := exists_contMDiffOn_mMaxFlow_nhds hk hvk x
  refine ⟨interior N, interior_mem_nhds.mpr hN, ?_⟩
  intro q hq
  have hNq : N ∈ 𝓝 q := mem_of_superset (isOpen_interior.mem_nhds hq) interior_subset
  exact ⟨mem_of_superset hNq hND, hNF.contMDiffAt hNq⟩

/-- `cor:flow-manifold`: the maximal flow domain on an abstract manifold is
open, and a `C^k` vector field has a jointly `C^k` maximal flow on all of it,
for `1 ≤ k ≤ ∞`. -/
theorem isOpen_mMaxFlowDomain_and_contMDiffOn [IsManifold I (⊤ : ℕ∞) M] {k : ℕ∞}
    (hk : 1 ≤ k) (hvk : CMDiff k (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    IsOpen {q : ℝ × M | q.1 ∈ mMaxFlowInterval v q.2} ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k (fun q : ℝ × M => mMaxFlow v q.1 q.2)
        {q : ℝ × M | q.1 ∈ mMaxFlowInterval v q.2} := by
  have hk' : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
  have hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) := hvk.of_le hk'
  have key : ∀ (x : M) (t : ℝ), t ∈ mMaxFlowInterval v x → mFlowRegularAt v k t x := by
    intro x t ht
    have hzero : mFlowRegularAt v k 0 x := by
      obtain ⟨N, hN, hreg⟩ := mFlowRegularAt_nhds_zero hk hvk x
      exact hreg (0, x) (mem_of_mem_nhds hN)
    have hlocal : ∀ a ∈ mMaxFlowInterval v x, ∀ᶠ b in 𝓝[mMaxFlowInterval v x] a,
        mFlowRegularAt v k a x ↔ mFlowRegularAt v k b x := by
      intro a ha
      obtain ⟨N, hN, hreg⟩ := mFlowRegularAt_nhds_zero hk hvk (mMaxFlow v a x)
      have hγ : ContinuousAt (fun b : ℝ => mMaxFlow v b x) a :=
        (isMIntegralCurveOn_mMaxFlow hv x).continuousOn.continuousAt
          ((isOpen_mMaxFlowInterval x).mem_nhds ha)
      have hforward : ∀ᶠ b in 𝓝 a, (b - a, mMaxFlow v a x) ∈ N := by
        have hc : ContinuousAt (fun b : ℝ => (b - a, mMaxFlow v a x)) a :=
          (continuousAt_id.sub continuousAt_const).prodMk continuousAt_const
        exact hc.preimage_mem_nhds (by simpa using hN)
      have hbackward : ∀ᶠ b in 𝓝 a, (a - b, mMaxFlow v b x) ∈ N := by
        have hc : ContinuousAt (fun b : ℝ => (a - b, mMaxFlow v b x)) a :=
          (continuousAt_const.sub continuousAt_id).prodMk hγ
        exact hc.preimage_mem_nhds (by simpa using hN)
      filter_upwards [hforward.filter_mono nhdsWithin_le_nhds,
        hbackward.filter_mono nhdsWithin_le_nhds] with b hbf hbb
      constructor
      · intro h
        simpa using mFlowRegularAt_add hv h (hreg (b - a, mMaxFlow v a x) hbf)
      · intro h
        simpa using mFlowRegularAt_add hv h (hreg (a - b, mMaxFlow v b x) hbb)
    have heq := (ordConnected_mMaxFlowInterval (v := v) x).isPreconnected.induction₂
      (fun a b => mFlowRegularAt v k a x ↔ mFlowRegularAt v k b x) hlocal
      (fun _ _ _ _ _ _ hab hbc => hab.trans hbc)
      (fun _ _ _ _ hab => hab.symm) (zero_mem_mMaxFlowInterval hv x) ht
    exact heq.mp hzero
  exact ⟨isOpen_iff_mem_nhds.mpr (fun q hq => (key q.2 q.1 hq).1),
    fun q hq => (key q.2 q.1 hq).2.contMDiffWithinAt⟩

end LiquidDrop
