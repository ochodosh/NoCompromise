import NoCompromise.Energy.Scaling
import NoCompromise.BV.GoodTruncation

/-!
# Bounded approximation at fixed volume

Good spherical truncations converge in volume and perimeter. After discarding
a finite prefix, positive dilations restore the volume. The dilation factors
converge to one, preserving both the perimeter and Coulomb energy limits.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Pointwise symmDiff
namespace LiquidDrop

/-- Blueprint `lem:bounded-approx`. The perimeter limit uses `perimeterN`.
Good spherical truncations are dilated to restore the original volume. -/
theorem exists_bounded_approximation (E : Set AmbientSpace)
    (hmE : NullMeasurableSet E volume) (hvol : 0 < volume E)
    (hvolfin : volume E < ∞) (hper : HasFinitePerimeter E) :
    ∃ F : ℕ → Set AmbientSpace, (∀ n, NullMeasurableSet (F n) volume) ∧
      (∀ n, Bornology.IsBounded (F n)) ∧ (∀ n, HasFinitePerimeter (F n)) ∧
      (∀ n, volume (F n) = volume E) ∧
      Tendsto (fun n => perimeterN (F n)) atTop (𝓝 (perimeterN E)) ∧
      Tendsto (fun n => coulombEnergy (F n)) atTop (𝓝 (coulombEnergy E)) := by
  obtain ⟨R, hR, hmono, _, _, _, htail, hp⟩ :=
    exists_good_truncation hmE hvolfin hper (0 : AmbientSpace)
  let G : ℕ → Set AmbientSpace := fun n => E ∩ ball 0 (R n)
  have hmG (n : ℕ) : NullMeasurableSet (G n) volume :=
    hmE.inter measurableSet_ball.nullMeasurableSet
  have hvG (n : ℕ) : volume (G n) < ∞ :=
    (measure_mono inter_subset_left).trans_lt hvolfin
  have hVG : Tendsto (fun n => volume (G n)) atTop (𝓝 (volume E)) := by
    have hinc : Monotone G := fun i j hij =>
      inter_subset_inter_right E (ball_subset_ball (hmono.monotone hij))
    have hU : (⋃ n, G n) = E := by
      apply Subset.antisymm
      · exact iUnion_subset fun _ => inter_subset_left
      · intro x hx
        obtain ⟨n, hn⟩ := exists_nat_gt (dist x (0 : AmbientSpace))
        exact mem_iUnion.mpr ⟨n, hx, hn.trans (hR n).1⟩
    simpa only [Function.comp_def, hU] using tendsto_measure_iUnion_atTop hinc
  have hPG : Tendsto (fun n => perimeterN (G n)) atTop (𝓝 (perimeterN E)) := by
    simpa only [perimeterN_eq_perimeter _ (hmG _), perimeterN_eq_perimeter E hmE] using hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hVG.eventually (eventually_gt_nhds hvol)).and
      (hPG.eventually (eventually_lt_nhds hper)))
  let H : ℕ → Set AmbientSpace := fun n => G (n + N)
  have hmH (n : ℕ) : NullMeasurableSet (H n) volume := hmG _
  have hvH (n : ℕ) : volume (H n) < ∞ := hvG _
  have hpos (n : ℕ) : 0 < volume (H n) := (hN (n + N) (Nat.le_add_left _ _)).1
  have hpH (n : ℕ) : HasFinitePerimeter (H n) := (hN (n + N) (Nat.le_add_left _ _)).2
  have hVH := hVG.comp (tendsto_add_atTop_nat N)
  have hPH := hPG.comp (tendsto_add_atTop_nat N)
  have hrealpos : 0 < (volume E).toReal := ENNReal.toReal_pos hvol.ne' hvolfin.ne
  have hrealH (n : ℕ) : 0 < (volume (H n)).toReal :=
    ENNReal.toReal_pos (hpos n).ne' (hvH n).ne
  let r : ℕ → ℝ := fun n => ((volume E).toReal / (volume (H n)).toReal) ^ (1 / 3 : ℝ)
  have hr (n : ℕ) : 0 < r n := Real.rpow_pos_of_pos (div_pos hrealpos (hrealH n)) _
  have hrpow (n : ℕ) : r n ^ 3 = (volume E).toReal / (volume (H n)).toReal := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (div_pos hrealpos (hrealH n)))]
    norm_num
  have hratio : Tendsto (fun n => (volume E).toReal / (volume (H n)).toReal)
      atTop (𝓝 1) := by
    have ht : Tendsto (fun n => (volume E).toReal / (volume (H n)).toReal)
        atTop (𝓝 ((volume E).toReal / (volume E).toReal)) :=
      Tendsto.div tendsto_const_nhds
        ((ENNReal.tendsto_toReal hvolfin.ne).comp hVH) hrealpos.ne'
    simpa only [div_self hrealpos.ne'] using ht
  have hrt : Tendsto r atTop (𝓝 1) := by
    simpa only [Real.one_rpow] using hratio.rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have htailH : Tendsto (fun n => volume (H n ∆ E)) atTop (𝓝 0) := by
    have heq (n : ℕ) : H n ∆ E = E \ ball 0 (R (n + N)) := by
      dsimp [H, G]
      ext x
      simp only [mem_symmDiff, mem_inter_iff, Set.mem_sdiff]
      tauto
    simp_rw [heq]
    exact htail.comp (tendsto_add_atTop_nat N)
  have hCHreal := tendsto_coulombEnergy_of_symmDiff hmH hmE ENNReal.toReal_nonneg
    (fun n => (measure_mono (show H n ⊆ E from inter_subset_left)).trans
      (le_of_eq (ENNReal.ofReal_toReal hvolfin.ne).symm))
    (le_of_eq (ENNReal.ofReal_toReal hvolfin.ne).symm)
    (by simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp htailH)
  have hCH : Tendsto (fun n => coulombEnergy (H n)) atTop (𝓝 (coulombEnergy E)) := by
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hCHreal
    simpa only [Function.comp_def, ENNReal.ofReal_toReal (coulombEnergy_lt_top E hvolfin).ne,
      ENNReal.ofReal_toReal (coulombEnergy_lt_top (H _) (hvH _)).ne] using ht
  let F : ℕ → Set AmbientSpace := fun n => (fun x => r n • x) '' H n
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact nullMeasurableSet_image_of_differentiable (by fun_prop)
      (smul_right_injective _ (hr n).ne') (hmH n)
  · intro n
    exact (isBounded_ball.subset
      (show H n ⊆ ball 0 (R (n + N)) from inter_subset_right)).smul₀ (r n)
  · intro n
    change perimeterN ((fun x => r n • x) '' H n) < ∞
    rw [perimeterN_smul (by decide : 0 < 3) _ (hr n)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hpH n)
  · intro n
    rw [show F n = (fun x => r n • x) '' H n from rfl, volume_image_smul _ (hr n), hrpow,
      ENNReal.ofReal_div_of_pos (hrealH n), ENNReal.ofReal_toReal hvolfin.ne,
      ENNReal.ofReal_toReal (hvH n).ne, ENNReal.div_mul_cancel (hpos n).ne' (hvH n).ne]
  · have ht : Tendsto (fun n => ENNReal.ofReal (r n ^ 2)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, one_pow, ENNReal.ofReal_one] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hrt.pow 2)
    have ht' := ENNReal.Tendsto.mul ht (Or.inl one_ne_zero) hPH (Or.inr ENNReal.one_ne_top)
    simpa only [one_mul, F, H, Function.comp_def, Nat.reduceSub,
      perimeterN_smul (by decide : 0 < 3) _ (hr _)] using ht'
  · have ht : Tendsto (fun n => ENNReal.ofReal (r n ^ 5)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, one_pow, ENNReal.ofReal_one] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hrt.pow 5)
    have ht' := ENNReal.Tendsto.mul ht (Or.inl one_ne_zero) hCH (Or.inr ENNReal.one_ne_top)
    simpa only [one_mul, F, coulombEnergy_smul _ (hr _)] using ht'

end LiquidDrop
