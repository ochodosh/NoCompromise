import NoCompromise.Elliptic.BoundaryNeumannC2InhomBounds
import NoCompromise.Elliptic.NeumannChartC1Data

/-! Smooth flat Neumann data supply all the quantitative C¹ hypotheses. -/

noncomputable section
open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient
namespace LiquidDrop

lemma boundaryNeumannNormalCoefficient_contDiffOn
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (boundaryNeumannNormalCoefficient A)
      (graphBaseEmbedding ⁻¹' O) := by
  have he := hA.comp graphBaseEmbedding.contDiff.contDiffOn (fun _ ht => ht)
  exact (he.clm_apply contDiffOn_const).inner ℝ contDiffOn_const

lemma boundaryNeumannLift_smoothOn {h b : EuclideanSpace ℝ (Fin 2) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h U) (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U)
    (hb0 : ∀ y ∈ U, b y ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (boundaryNeumannLift h b) ((graphProjectionN 2) ⁻¹' U) := by
  exact (EuclideanSpace.proj (Fin.last 2)).contDiff.contDiffOn.mul
    ((hh.div hb hb0).comp (graphProjectionN 2).contDiff.contDiffOn (fun _ hx => hx))

/-- No coefficient, forcing, or boundary-data norm is assumed: the constants
in the C¹ conormal theorem follow from smoothness on the stated neighborhoods. -/
theorem boundary_neumann_c2_inhom_smooth_exists_data
    {α lam : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A O) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) i = 0)
    (hpos : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ closedBall 0 1 ⊆ U ∧
      ∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x) :
    ∃ cap HA K : ℝ, 0 ≤ cap ∧ 0 ≤ HA ∧ 0 ≤ K ∧
      NeumannChartC1Data A f h α lam cap HA K := by
  obtain ⟨U, hU, hUs, hUp⟩ := hpos
  let V := U ∩ graphBaseEmbedding ⁻¹' O
  have hV : IsOpen V := hU.inter (hO.preimage graphBaseEmbedding.continuous)
  have hVs : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ V := by
    intro x hx
    refine ⟨hUs hx, hsub ?_⟩
    simpa only [mem_closedBall, dist_zero_right, norm_graphBaseEmbedding] using hx
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (boundaryNeumannNormalCoefficient A) V :=
    (boundaryNeumannNormalCoefficient_contDiffOn hA).mono inter_subset_right
  have hgrad (g : EuclideanSpace ℝ (Fin 2) → ℝ)
      (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V) :
      ContDiffOn ℝ (⊤ : ℕ∞) (gradient g) V :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp_contDiffOn
      (hg.fderiv_of_isOpen hV (by simp))
  have bounds {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {g : EuclideanSpace ℝ (Fin n) → E} {W : Set (EuclideanSpace ℝ (Fin n))}
      (hW : IsOpen W) (hs : closedBall 0 1 ⊆ W)
      (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) :=
    boundary_neumann_c2_inhom_compact_bounds hα.le hα1.le
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) hW hs
      (hg.of_le (by simp))
  obtain ⟨BA, hBA, hbA, hhA⟩ := bounds hO hsub hA
  obtain ⟨Kf, hKf, hbf, hhf⟩ := bounds hO hsub hf
  obtain ⟨Kh, hKh, hbh, -⟩ := bounds hV hVs hh.contDiffOn
  obtain ⟨Kb, hKb, hbb, -⟩ := bounds hV hVs hb
  obtain ⟨KDh, hKDh, hbDh, hhDh⟩ := bounds hV hVs (hgrad h hh.contDiffOn)
  obtain ⟨KDb, hKDb, hbDb, hhDb⟩ := bounds hV hVs (hgrad _ hb)
  let K := Kf + Kh + Kb + KDh + KDb
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKf' : Kf ≤ K := by dsimp [K]; linarith
  have hKh' : Kh ≤ K := by dsimp [K]; linarith
  have hKb' : Kb ≤ K := by dsimp [K]; linarith
  have hKDh' : KDh ≤ K := by dsimp [K]; linarith
  have hKDb' : KDb ≤ K := by dsimp [K]; linarith
  have hclosed : closure (boundaryHalfBall 1) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun x hx => by simpa only [mem_closedBall, dist_zero_right] using
      boundary_neumann_closed_norm_le hx
  refine ⟨BA, BA, K, hBA, hBA, hK, ?_⟩
  refine ⟨hA.continuousOn.mono (hclosed.trans hsub),
    fun x hx => hbA x (hclosed hx), hell,
    fun x hx y hy => hhA x (hclosed hx) y (hclosed hy), hcross,
    ⟨V, hV, hVs, (hh.of_le (by simp)).contDiffOn,
      hb.of_le (by simp), fun x hx => hUp x hx.1⟩,
    fun x hx => (hbh x hx).trans hKh', fun x hx => (hbb x hx).trans hKb',
    fun x hx => (hbDh x hx).trans hKDh', fun x hx => (hbDb x hx).trans hKDb',
    ?_, ?_, hf.continuousOn.mono (hclosed.trans hsub),
    fun x hx => (hbf x (hclosed hx)).trans hKf', ?_⟩
  · intro x hx y hy
    exact (hhDh x hx y hy).trans
      (mul_le_mul_of_nonneg_right hKDh' (Real.rpow_nonneg dist_nonneg _))
  · intro x hx y hy
    exact (hhDb x hx y hy).trans
      (mul_le_mul_of_nonneg_right hKDb' (Real.rpow_nonneg dist_nonneg _))
  · intro x hx y hy
    exact (hhf x (hclosed hx) y (hclosed hy)).trans
      (mul_le_mul_of_nonneg_right hKf' (Real.rpow_nonneg dist_nonneg _))

end LiquidDrop
