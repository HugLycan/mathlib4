import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic

theorem NormedSpace.exists_mem_convex_compact_finDim_isFixedPt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hcv : Convex ℝ s) (hcm : IsCompact s) (hn : s.Nonempty) (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := sorry

theorem NormedSpace.exists_mem_convex_compact_isFixedPt {E : Type*}
    [NormedField E] [NormedSpace ℝ E] [CompleteSpace E]
    {s : Set E} (hcv : Convex ℝ s) (hcm : IsCompact s) (hn : s.Nonempty) (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := by
  choose ci hc h using fun M : ℕ ↦ @finite_cover_balls_of_compact _ _ _ hcm M.succ⁻¹ (by positivity)
  have hz (M : ℕ) : ∃ z : s, dist (f z) z ≤ (M.succ⁻¹ : ℝ) := by
    let cs := (h M).1.toFinset
    let gs (c : cs) (x : E) : ℝ :=
      if dist c.1 x ≤ (M.succ⁻¹ : ℝ) then (M.succ⁻¹ : ℝ) - dist c.1 x else 0
    let s' := convexHull ℝ (cs : Set E)
    let E₀ := Submodule.span ℝ (cs : Set E)
    let s₀' : Set E₀ := {x | x.1 ∈ s'}
    have hs'E₀ : s' ⊆ E₀ :=
      (convexHull_subset_affineSpan (𝕜 := ℝ) (cs : Set E)).trans affineSpan_subset_span
    have hs₀'_s' : Subtype.val '' s₀' = s' := by
      simp [·''·, s₀', s']
      exact hs'E₀
    have hs's : s' ⊆ s := convexHull_min (by simp only [Set.Finite.coe_toFinset, hc, cs]) hcv
    let ι := Module.Basis.ofVectorSpaceIndex ℝ E₀
    let coord : E₀ →ₗ[ℝ] ι →₀ ℝ := (Module.Basis.ofVectorSpace ℝ E₀).1.1
    let g (x : E) : E := (∑ c, gs c x)⁻¹ • ∑ c, gs c x • c.1
    have hgs_C (c : cs) : Continuous (gs c) := by
      sorry
    have hgs_nonneg (c : cs) (x : E) : 0 ≤ gs c x := by
      sorry
    have hgs_sumpos (x : E) : 0 < ∑ c, gs c x := by
      sorry
    have hg : g '' s ⊆ s' := by
      intro gx ⟨x, hx, hgx⟩
      rw [←hgx, Finset.mem_convexHull']
      classical let w (y : E) : ℝ := if hy : y ∈ cs then (∑ c, gs c x)⁻¹ * gs ⟨y, hy⟩ x else 0
      use w, ?_, ?_, ?_
      · intro y hy
        simp only [Finset.univ_eq_attach, hy, ↓reduceDIte, w]
        have : 0 < (∑ c, gs c x)⁻¹ := by positivity [hgs_sumpos x]
        positivity [hgs_nonneg ⟨y, hy⟩ x]
      · simp only [w]
        classical simp_rw [Finset.sum_dite_of_true (s := cs) (by tauto), mul_comm]
        simp only [Finset.univ_eq_attach, Subtype.coe_eta]
        rw [←Finset.sum_mul, mul_inv_cancel₀]
        positivity [hgs_sumpos x]
      · classical simp only [Finset.univ_eq_attach, dite_smul, zero_smul,
          Finset.sum_dite_of_true (s := cs) (by tauto), Subtype.coe_eta, w, g]
        simp_rw [←smul_smul, ←Finset.smul_sum]
    have hg_tends (x : s) : dist (g x) x ≤ (M.succ⁻¹ : ℝ) := by
      sorry
    let g' (x : s₀') : s₀' := by
      use ⟨g (f ?x), hs'E₀ (hg ?m)⟩, hg ?m
      · use x, hs's x.2
      · use f ?x, (f ?x).2
    have hg' (x : s) : dist (g x) x ≤ (M.succ⁻¹ : ℝ) := by specialize hgs_sumpos x; calc
      _ = ‖g x - x‖ := dist_eq_norm _ _
      _ = ‖(∑ c, gs c x)⁻¹ • ∑ c, gs c x • (c.1 - x)‖ := by
        have : x = (∑ c, gs c x)⁻¹ • ∑ c, gs c x • x.1 := by
          rw [←Finset.sum_smul, inv_smul_smul₀]
          positivity
        rw [show g x - x = (∑ c, gs c x)⁻¹ • ∑ c, gs c x • (c.1 - x) by calc
          _ = (∑ c, gs c x)⁻¹ • ∑ c, gs c x • c.1 - x := by simp [g]
          _ = (∑ c, gs c x)⁻¹ • ∑ c, gs c x • c.1 - (∑ c, gs c x)⁻¹ • ∑ c, gs c x • x.1 := by congr
          _ = (∑ c, gs c x)⁻¹ • ∑ c, gs c x • (c.1 - x) := by
            simp_rw [smul_sub, Finset.sum_sub_distrib, smul_sub]
        ]
      _ = (∑ c, gs c x)⁻¹ * ‖∑ c, gs c x • (c.1 - x)‖ := by
        rw [norm_smul]
        congr
        simp
        positivity
      _ ≤ (∑ c, gs c x)⁻¹ * ∑ c, ‖gs c x • (c.1 - x)‖ := by grw [norm_sum_le]
      _ = (∑ c, gs c x)⁻¹ * ∑ c, gs c x * ‖c.1 - x‖ := by
        congr
        ext
        rw [norm_smul]
        congr
        simp [hgs_nonneg]
      _ ≤ (∑ c, gs c x)⁻¹ * ∑ c, gs c x * (M.succ⁻¹ : ℝ) := by
        gcongr 2 with c
        specialize hgs_nonneg c x
        obtain hgs0 | hgs_pos := hgs_nonneg.eq_or_lt
        · rw [←hgs0]; simp
        · simp [gs] at hgs_pos
          rw [←dist_eq_norm]
          gcongr
          convert (ite_ne_right_iff.1 hgs_pos.ne.symm).1
          simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      _ = (M.succ⁻¹ : ℝ) := by
        rw [←Finset.sum_mul, ←mul_assoc, inv_mul_cancel₀ (by positivity)]
        apply one_mul
    have ⟨⟨⟨z, _⟩, hz⟩, hz_fixPt⟩ : ∃ x, Function.IsFixedPt g' x := by
      apply exists_mem_convex_compact_finDim_isFixedPt ?_ ?_ ?_ ⟨g', ?_⟩
      ·
        sorry
      · sorry
      · sorry
      · repeat apply Continuous.subtype_mk
        change Continuous (g ∘ Subtype.val ∘ f ∘ fun y : s₀' ↦ ⟨y.1.1, hs's y.2⟩)
        apply Continuous.comp ?_ <| Continuous.comp ?_ <| Continuous.comp f.2 ?_
        · simp [g]
          sorry
        · fun_prop
        · fun_prop
    use ⟨z, hs's <| Set.mem_setOf_eq ▸ hz⟩
    simp [Function.IsFixedPt, g'] at hz_fixPt
    conv => arg 1; arg 2; arg 1; rw [←hz_fixPt]
    rw [dist_comm]
    exact hg_tends (f ⟨z, hs's <| Set.mem_setOf_eq ▸ hz⟩)
  choose z hfz_z using hz
  have ⟨z0, hz0, j, hj, hlim⟩ := hcm.tendsto_subseq fun M ↦ (z M).2
  let z₀ : s := ⟨z0, hz0⟩
  have hzj_z₀ (M : ℕ) : ∃ N, ∀ (n : ℕ), N ≤ n → dist (z (j n)) z₀ < (M.succ⁻¹ : ℝ) := by
    conv in dist _ _ < _ => rw [←Metric.mem_ball]
    apply tendsto_atTop_nhds.1 hlim (Metric.ball z₀ M.succ⁻¹)
    · apply Metric.mem_ball_self; positivity
    · simp
  have hfzj_zj (M : ℕ) : dist (f (z (j M))) (z (j M)) ≤ (M.succ⁻¹ : ℝ) := by calc
    _ ≤ ((j M).succ⁻¹ : ℝ) := hfz_z (j M)
    _ ≤ (M.succ⁻¹ : ℝ) := by
      apply inv_anti₀
      · positivity
      · norm_cast
        gcongr
        exact hj.le_apply
  have hfzj_z₀ (M : ℕ) : ∃ N, ∀ (n : ℕ), N ≤ n → dist (f (z (j n))) z₀ < 3 / M.succ := by
    have ⟨N₀, hN₀⟩ := hzj_z₀ M
    use max M N₀; intro n hn
    have ⟨hMn, hN₀n⟩ := max_le_iff.1 hn
    calc
      _ ≤ dist (f (z (j n))) (z (j n)) + dist (z (j n)) z₀ := dist_triangle _ _ _
      _ ≤ (M.succ⁻¹ : ℝ) + (M.succ⁻¹ : ℝ) := by grw [hfzj_zj, hN₀ n hN₀n]; gcongr
      _ = 2 / M.succ := by ring
      _ < 3 / M.succ := div_lt_div_of_pos_right (by norm_num) (by positivity)
  have hlim_z₀ : Filter.atTop.Tendsto (f ∘ z ∘ j) (nhds z₀) := by
    rw [tendsto_atTop_nhds]
    intro U hz₀U hUO
    have ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUO z₀ hz₀U
    let M₀ := ⌈3/ε⌉₊
    have ⟨N, hN⟩ := hfzj_z₀ M₀
    use N; intro n hn
    apply hball; simp
    calc
      _ < 3 / (M₀.succ : ℝ) := hN n hn
      _ < 3 / M₀ := div_lt_div_of_pos_left (by norm_num) (by positivity) (by simp)
      _ ≤ ε := by
        rw [div_le_comm₀]
        · apply Nat.le_ceil
        · positivity
        · assumption
  have hlim_fz₀ : Filter.atTop.Tendsto (f ∘ z ∘ j) (nhds (f z₀)) :=
    (f.2.tendsto z₀).comp (tendsto_subtype_rng.2 hlim)
  use z₀, tendsto_nhds_unique hlim_fz₀ hlim_z₀

-- theorem convexHull_homeo_closedBall {E : Type*}
--     [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
--     (s : Set E) (hcv : Convex ℝ s) (hcm : IsCompact s)
--     (hin : (interior s).Nonempty) :
--     Nonempty (s ≃ₜ Metric.closedBall (0 : E) 1) := by
--   have ⟨f, _, hf, _⟩
--     := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcv hin hcm.isBounded
--   rw [closure_eq_iff_isClosed.2 hcm.isClosed] at hf
--   rw [←hf]
--   exact ⟨f.image s⟩

-- theorem convex_compact_homeo_unitCube {E : Type*}
--     [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
--     (s : Set E) (hcv : Convex ℝ s) (hcm : IsCompact s) (hn : s.Nonempty)
--     : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by
--   sorry

-- def unitCube n := Set.Icc (0 : Fin n → ℝ) 1

-- theorem exists_mem_unitCube_isFixedPt {n : ℕ} (f : C(@unitCube n, @unitCube n))
--     : ∃ x, Function.IsFixedPt f x := by
--   sorry

-- theorem exists_mem_convex_compact_isFixedPt {E : Type*}
--     [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
--     (s : Set E) (hcv : Convex ℝ s) (hcm : IsCompact s) (hn : Set.Nonempty s)
--     (f : C(s, s))
--     : ∃ x, Function.IsFixedPt f x := by
--   intro s hcv hcm hn f
--   have ⟨k, ⟨e⟩⟩ := convex_compact_homeo_unitCube s hcv hcm hn
--   let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
--   have ⟨y, hy⟩ := @exists_mem_unitCube_isFixedPt k g
--   use toContinuousMap e.symm y
--   exact EquivLike.inv_apply_eq.mp hy

-- def HomotopyGroup.mulEquiv_of_homotopy {N X Y : Type*}
--     [Nonempty N] [DecidableEq N] [TopologicalSpace X] [TopologicalSpace Y]
--     (H : ContinuousMap.HomotopyEquiv X Y) (x : X) (y : Y) (hH₁ : H x = y) (hH₂ : H.2 y = x) :
--     HomotopyGroup N X x ≃* HomotopyGroup N Y y where
--   toFun := .map (fun p ↦ ⟨
--     H.1.comp p.1, by
--       intro q hq
--       simp only [ContinuousMap.comp_apply, p.2 q hq, hH₁]
--     ⟩) <| by
--       intros
--       apply ContinuousMap.HomotopicRel.comp_continuousMap
--       assumption
--   invFun := .map (fun p ↦ ⟨
--     H.2.comp p.1, by
--       intro q hq
--       simp only [ContinuousMap.comp_apply, p.2 q hq, hH₂]
--     ⟩) <| by
--       intros
--       apply ContinuousMap.HomotopicRel.comp_continuousMap
--       assumption
--   map_mul' := by
--     apply Quotient.ind₂
--     intro p₁ p₂
--     let i := Classical.arbitrary N
--     have hx := @HomotopyGroup.mul_spec N _ _ x _ _ i
--     have hy := @HomotopyGroup.mul_spec N _ _ y _ _ i
--     simp only at hx hy
--     rw [hx]
--     simp only [Quotient.map_mk]
--     rw [hy, Quotient.eq]
--     constructor
--     sorry

--   left_inv := sorry
--   right_inv := sorry
