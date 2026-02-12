import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.LocallyConvex.AbsConvex

theorem exists_mem_convex_compact_finDim_isFixedPt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hcv : Convex ℝ s) (hcm : IsCompact s) (hn : s.Nonempty) (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := sorry

theorem exists_mem_convex_compact_isFixedPt {E : Type*}
    [NormedField E] [NormedSpace ℝ E]
    {s : Set E} (hsv : Convex ℝ s) (hsk : IsCompact s) (hsn : s.Nonempty) (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := by
  choose ci hc h using fun M : ℕ ↦ @finite_cover_balls_of_compact _ _ _ hsk M.succ⁻¹ (by positivity)
  have hz (M : ℕ) : ∃ z : s, dist (f z) z ≤ (M.succ⁻¹ : ℝ) := by
    let cs := (h M).1.toFinset
    let gs (c : cs) (x : E) : ℝ :=
      if dist c.1 x ≤ (M.succ⁻¹ : ℝ) then (M.succ⁻¹ : ℝ) - dist c.1 x else 0
    let s' := convexHull ℝ (cs : Set E)
    let E₀ := Submodule.span ℝ (cs : Set E)
    let s₀' : Set E₀ := Subtype.val ⁻¹' s'
    have hs'E₀ : s' ⊆ E₀ :=
      convexHull_subset_affineSpan (cs : Set E) |>.trans affineSpan_subset_span
    have hs₀'_s' : Subtype.val '' s₀' = s' := by
      simpa only [Set.image, Set.mem_preimage, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, Set.sep_eq_self_iff_mem_true, s₀', s']
    have hs's : s' ⊆ s := convexHull_min (by simp only [Set.Finite.coe_toFinset, hc, cs]) hsv
    let g (x : E) : E := (∑ c, gs c x)⁻¹ • ∑ c, gs c x • c.1
    have hgs_cont (c : cs) : Continuous (gs c) := by
      refine Continuous.if_le ?_ ?_ ?_ ?_ fun _ hx ↦ by rw [hx, sub_self]
      all_goals fun_prop
    have hgs_nonneg (c : cs) (x : E) : 0 ≤ gs c x := iteInduction sub_nonneg_of_le fun _ ↦ by rfl
    have hgs_sumpos (x : s) : 0 < ∑ c, gs c x := by
      have ⟨c₀, b, ⟨hc₀, hb⟩, hxb⟩ := Set.mem_iUnion.1 ((h M).2 x.2)
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hb
      rw [←hb, Metric.mem_ball, dist_comm] at hxb
      apply Finset.sum_pos' fun c _ ↦ hgs_nonneg c x
      use ⟨c₀, by simpa [cs]⟩
      simpa [gs, hxb.le]
    have hg : g '' s ⊆ s' := by
      intro gx ⟨x, hx, hgx⟩
      rw [←hgx, Finset.mem_convexHull']
      classical let w (y : E) : ℝ := if hy : y ∈ cs then (∑ c, gs c x)⁻¹ * gs ⟨y, hy⟩ x else 0
      use w, ?_, ?_, ?_
      · intro y hy
        simp only [Finset.univ_eq_attach, hy, ↓reduceDIte, w]
        have : 0 < (∑ c, gs c x)⁻¹ := by positivity [hgs_sumpos ⟨x, hx⟩]
        positivity [hgs_nonneg ⟨y, hy⟩ x]
      · simp only [w]
        classical simp_rw [Finset.sum_dite_of_true (s := cs) (by tauto), mul_comm]
        simp only [Finset.univ_eq_attach, Subtype.coe_eta]
        rw [←Finset.sum_mul, mul_inv_cancel₀]
        positivity [hgs_sumpos ⟨x, hx⟩]
      · classical simp only [Finset.univ_eq_attach, dite_smul, zero_smul,
          Finset.sum_dite_of_true (s := cs) (by tauto), Subtype.coe_eta, w, g]
        simp_rw [←smul_smul, ←Finset.smul_sum]
    have hg_tends (x : s) : dist (g x) x ≤ (M.succ⁻¹ : ℝ) := by specialize hgs_sumpos x; calc
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
        simp only [Finset.univ_eq_attach, norm_inv, Real.norm_eq_abs, inv_inj, abs_eq_self]
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
    let g' (x : s₀') : s₀' :=
      let x₁ : s := ⟨x, hs's x.2⟩
      have hgfx₁ := hg <| by use f x₁, (f x₁).2
      ⟨⟨g (f x₁), hs'E₀ hgfx₁⟩, hgfx₁⟩
    have ⟨⟨⟨z, _⟩, hz⟩, hz_fixPt⟩ : ∃ x, Function.IsFixedPt g' x := by
      apply exists_mem_convex_compact_finDim_isFixedPt ?_ ?_ ?_ ⟨g', ?_⟩
      · apply (convex_convexHull ℝ (cs : Set E)).is_linear_preimage
        apply IsLinearMap.mk
        all_goals intros; norm_cast
      · rw [Subtype.isCompact_iff, hs₀'_s']
        convert (h M).1.isCompact_convexHull
        simp [cs]
      · rw [Subtype.preimage_coe_nonempty, Set.inter_eq_self_of_subset_right hs'E₀,
          convexHull_nonempty_iff]
        simp only [Set.Nonempty, Set.Finite.coe_toFinset, cs]
        have := hsn.mono (h M).2
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Set.nonempty_iUnion,
          Metric.nonempty_ball, inv_pos, exists_prop, exists_and_right] at this
        exact this.1
      · repeat apply Continuous.subtype_mk
        change Continuous (g ∘ Subtype.val ∘ f ∘ fun y : s₀' ↦ ⟨y.1.1, hs's y.2⟩)
        refine continuous_finset_sum _ ?_ |>.comp ?_ |>.comp f.2 |>.comp ?_ |>.inv₀ ?_ |>.smul ?_
        all_goals try fun_prop
        intro ⟨x, hx⟩
        simp only [Set.mem_preimage, s₀'] at hx
        simp only [Finset.univ_eq_attach, ContinuousMap.toFun_eq_coe, Function.comp_apply, ne_eq]
        positivity [hgs_sumpos <| f ⟨x, hs's hx⟩]
    use ⟨z, hs's <| Set.mem_setOf_eq ▸ hz⟩
    simp only [Function.IsFixedPt, Subtype.mk.injEq, g'] at hz_fixPt
    conv => arg 1; arg 2; arg 1; rw [←hz_fixPt]
    rw [dist_comm]
    exact hg_tends (f ⟨z, hs's <| Set.mem_setOf_eq ▸ hz⟩)
  choose z hfz_z using hz
  have ⟨z0, hz0, j, hj, hlim⟩ := hsk.tendsto_subseq fun M ↦ (z M).2
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
    have ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hUO z₀ hz₀U
    let M₀ := ⌈3/ε⌉₊
    have ⟨N, hN⟩ := hfzj_z₀ M₀
    use N; intro n hn
    apply hb; simp only [Function.comp_apply, Metric.mem_ball]
    calc
      _ < 3 / (M₀.succ : ℝ) := hN n hn
      _ < 3 / M₀ := div_lt_div_of_pos_left (by norm_num) (by positivity) (by simp)
      _ ≤ ε := by
        rw [div_le_comm₀]
        · apply Nat.le_ceil
        · positivity
        · assumption
  have hlim_fz₀ : Filter.atTop.Tendsto (f ∘ z ∘ j) (nhds (f z₀)) :=
    f.2.tendsto z₀ |>.comp <| tendsto_subtype_rng.2 hlim
  use z₀, tendsto_nhds_unique hlim_fz₀ hlim_z₀

theorem exists_isFixedPt_of_bounded_solutions_of_eq_smul {E : Type*}
    [NormedField E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E →ₗ[ℝ] E) (hfc : Continuous f) (hfk : IsCompactOperator f)
    (hbs : Bornology.IsBounded {x | ∃ t ∈ Set.Icc (0 : ℝ) 1, x = t • f x}) :
    ∃ x, Function.IsFixedPt f x := by
  classical
  have ⟨M, hM0, hM⟩ := hbs.exists_pos_norm_lt
  let B : Set E := Metric.closedBall 0 M
  let p (x : E) : E := if x ∈ B then x else (M / ‖x‖) • x
  have hpc : Continuous p := by
    apply continuous_if
    · intro x hx
      simp only [Metric.mem_closedBall, dist_zero_right, B] at hx
      rw [frontier_le_subset_eq continuous_norm continuous_const hx, div_self hM0.ne', one_smul]
    · apply continuousOn_id
    · refine ContinuousOn.smul ?_ continuousOn_id
      apply ContinuousOn.div₀ continuousOn_const (ContinuousOn.norm continuousOn_id)
      simp only [id_eq, ne_eq, norm_eq_zero]
      intro x hx
      contrapose hx
      rw [hx, ←B.compl_def, closure_compl, Set.mem_compl_iff, not_not,
        interior_closedBall 0 hM0.ne']
      exact Metric.mem_ball_self hM0.lt
  let f' : E → E := p ∘ f
  have hf'c : Continuous f' := hpc.comp hfc
  let K : Set E := p '' closure (f '' B)
  have hKk : IsCompact K :=
    hfk.isCompact_closure_image_of_bounded Metric.isBounded_closedBall |>.image hpc
  let C : Set E := closedAbsConvexHull ℝ K
  have hf'CC : Set.MapsTo f' C C := by
    have hBav : AbsConvex ℝ B := ⟨balanced_closedBall_zero, convex_closedBall _ _⟩
    have hKB : K ⊆ B := by
      intro x hx
      have ⟨y, _, hy⟩ := Set.mem_image p _ x |>.1 hx
      have hpM : ‖p y‖ ≤ M := by
        unfold p
        by_cases h : y ∈ B
        · simp only [h, ↓reduceIte]
          simp only [Metric.mem_closedBall, dist_zero_right, B] at h
          assumption
        · simp only [h, ↓reduceIte, norm_smul, norm_div, Real.norm_eq_abs, abs_norm]
          rw [div_mul_cancel₀]
          · grind
          · simp [B] at h
            linarith
      rw [hy] at hpM
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hpM
    intro x hx
    apply subset_closedAbsConvexHull
    apply Set.image_mono subset_closure
    repeat apply Set.mem_image_of_mem
    exact closedAbsConvexHull_min hKB hBav Metric.isClosed_closedBall hx
  let f'' : C(C, C) := ⟨hf'CC.restrict, by
    simp only [Set.MapsTo.restrict, f']
    apply hpc.comp hfc |>.subtype_map
  ⟩
  have ⟨z₀, hz₀⟩ := exists_mem_convex_compact_isFixedPt ?_ ?_ ?_ f''
  · simp only [Function.IsFixedPt, ContinuousMap.coe_mk, f''] at hz₀
    rw [Subtype.ext_iff, hf'CC.val_restrict_apply z₀] at hz₀
    simp only [Metric.mem_closedBall, dist_zero_right, Function.comp_apply, f', p, B] at hz₀
    use z₀
    by_cases h : ‖f z₀‖ ≤ M
    · simp only [h] at hz₀
      exact hz₀
    · absurd le_refl M; push_neg
      calc
        M = ‖(M / ‖f z₀‖) • f z₀‖ := by
          simp only [norm_smul, norm_div, Real.norm_eq_abs, abs_norm]
          symm
          push_neg at h
          rw [div_mul_cancel₀ |M|, abs_eq_self]
          · exact hM0.le
          · linarith
        _ = ‖z₀.1‖ := by
          simp only [h] at hz₀
          congr
        _ < M := by
          obtain hfz₀pos | hfz₀0 := norm_nonneg (f z₀) |>.lt_or_eq'
          · simp only [Set.mem_Icc, Set.mem_setOf_eq, forall_exists_index, and_imp] at hM
            simp only [h] at hz₀
            apply hM z₀ (M / ‖f z₀‖)
            · positivity
            · push_neg at h
              rw [div_le_one hfz₀pos]
              exact h.le
            exact hz₀.symm
          · linarith
  · exact absConvex_convexClosedHull.2
  · exact isCompact_closedAbsConvexHull_of_totallyBounded hKk.totallyBounded
  · refine Set.Nonempty.image f ?_ |>.closure |>.image p |>.mono subset_closedAbsConvexHull
    use 0, Metric.mem_closedBall_self hM0.le
