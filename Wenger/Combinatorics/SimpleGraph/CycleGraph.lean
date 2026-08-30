import Mathlib

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A copy of `cycleGraph n` in a graph `G` is an injective cyclic sequence `ZMod n → V` such that
consecutive values are adjacent. -/
lemma cycleGraph_isContained_iff_exists_inj_adj {n : ℕ} (hn : 2 < n) :
    cycleGraph n ⊑ G ↔ ∃ f : ZMod n → V, Function.Injective f ∧ ∀ i, G.Adj (f i) (f (i + 1)) := by
  haveI : NeZero n := ⟨ne_of_gt <| two_pos.trans hn⟩
  refine ⟨fun ⟨c⟩ ↦ ⟨c.toHom ∘ (ZMod.finEquiv n).symm,
      c.injective.comp (ZMod.finEquiv n).symm.injective, fun i ↦ ?_⟩,
    fun ⟨f, hf_inj, hf_adj⟩ ↦ ⟨⟨⟨f ∘ ZMod.finEquiv n, fun {i j} hij ↦ ?_⟩,
      hf_inj.comp (ZMod.finEquiv n).injective⟩⟩⟩
  · refine c.toHom.map_adj <| cycleGraph_adj'.mpr (Or.inr ?_)
    rw [← map_sub, add_sub_cancel_left, map_one,
      ← Nat.mod_eq_of_lt (one_lt_two.trans hn), ← Fin.val_one']
  · show G.Adj ((f ∘ ZMod.finEquiv n) i) ((f ∘ ZMod.finEquiv n) j)
    replace hij := cycleGraph_adj'.mp hij
    rw [← Nat.mod_eq_of_lt (one_lt_two.trans hn), ← Fin.val_one',
      Fin.val_inj, sub_eq_iff_eq_add', Fin.val_inj, sub_eq_iff_eq_add'] at hij
    rcases hij with hi | hj
    · rw [Function.comp_apply (x := i), hi, map_add, map_one, adj_comm]
      exact hf_adj <| (ZMod.finEquiv n) j
    · rw [Function.comp_apply (x := j), hj, map_add, map_one]
      exact hf_adj <| (ZMod.finEquiv n) i

section sum

variable {V W : Type*} {G : SimpleGraph (V ⊕ W)}

/-- A copy of `cycleGraph (2 * k)` in a bipartite graph `G` is two injective cyclic
sequences `v : ZMod k → V` and `w : ZMod k → W` such that `w i` is adjacent to both
`v i` and `v (i + 1)`. -/
lemma cycleGraph_isContained_iff_exists_inj_inj_adj_adj
    (hbi : G ≤ completeBipartiteGraph V W) {k : ℕ} (hk : 2 ≤ k) :
    cycleGraph (2 * k) ⊑ G ↔ ∃ (v : ZMod k → V) (w : ZMod k → W),
      Function.Injective v ∧ Function.Injective w
      ∧ (∀ i, G.Adj (.inl (v i)) (.inr (w i)))
      ∧ (∀ i, G.Adj (.inr (w i)) (.inl (v (i + 1)))) := by
  haveI : Fact (1 < k) := ⟨by linarith⟩
  haveI : Fact (1 < 2 * k) := ⟨by linarith⟩
  refine ⟨fun h ↦ ?_, fun ⟨v, w, hv, hw, hvw, hwv⟩ ↦ ?_⟩
  · obtain ⟨f, hf_inj, hf_adj⟩ :=
      (cycleGraph_isContained_iff_exists_inj_adj <| lt_mul_right two_pos hk).mp h
    have hf_isLeft_succ_eq (j) : (f (j + 1)).isLeft = !(f j).isLeft := by
      have hadj := hbi (hf_adj j)
      cases hj : f j <;> cases hj1 : f (j + 1)
        <;> rw [hj, hj1, completeBipartiteGraph_adj] at hadj <;> simp_all
    -- start the cycle at an index `v₀` in `V`
    obtain ⟨v₀, hv₀⟩ : ∃ c : ZMod (2 * k), (f c).isLeft := by
      cases hf0 : f 0 with
      | inl _ =>
        refine ⟨0, ?_⟩
        rw [hf0, Sum.isLeft_inl]
      | inr _ =>
        refine ⟨0 + 1, ?_⟩
        rw [hf_isLeft_succ_eq, hf0, Sum.isLeft_inr, Bool.not_false]
    -- the vertices at even distance from `v₀` lie in `V`
    have hf_left (x) : (f (v₀ + 2 * x)).isLeft := by
      obtain ⟨x', rfl⟩ := ZMod.natCast_zmod_surjective x
      induction x' with
      | zero => rwa [Nat.cast_zero, mul_zero, add_zero]
      | succ m ih =>
        rw [Nat.cast_add_one, mul_add, ← add_assoc, two_mul 1,
          ← add_assoc, hf_isLeft_succ_eq, hf_isLeft_succ_eq, Bool.not_not]
        exact ih
    -- the vertices at odd distance from `v₀` lie in `W`
    have hf_right (x) : (f (v₀ + 2 * x + 1)).isRight := by
      rw [← Sum.not_isLeft, hf_isLeft_succ_eq,
        Sum.bnot_isLeft, Bool.not_eq_true, Sum.isRight_eq_false]
      exact hf_left x
    choose v hv using fun x ↦ Sum.isLeft_iff.mp (hf_left x)
    choose w hw using fun x ↦ Sum.isRight_iff.mp (hf_right x)
    -- doubling embeds `ZMod k` into `ZMod (2 * k)`
    have hmul2_inj (i j : ZMod k)
        (hmul2_eq : 2 * (i.cast : ZMod (2 * k)) = 2 * (j.cast : ZMod (2 * k))) : i = j := by
      rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j, ZMod.natCast_eq_natCast_iff,
        Nat.modEq_iff_dvd, ← mul_dvd_mul_iff_left two_ne_zero, ← Nat.cast_two, ← Nat.cast_mul,
        ← ZMod.intCast_zmod_eq_zero_iff_dvd, mul_sub, Int.cast_sub, sub_eq_zero, Int.cast_mul,
        Int.cast_mul, Nat.cast_ofNat, Int.cast_ofNat, ZMod.natCast_val, ZMod.intCast_cast,
        ZMod.natCast_val, ZMod.intCast_cast]
      exact hmul2_eq.symm
    -- doubling succ is succ succ
    have hmul2_succ_eq (i : ZMod k) :
        2 * ((i + 1).cast : ZMod (2 * k)) = 2 * (i.cast : ZMod (2 * k)) + 1 + 1 := by
      rw [add_assoc, one_add_one_eq_two, ← ZMod.natCast_val (i + 1), ← ZMod.natCast_val i,
        ← Nat.cast_two (R := ZMod (2 * k)), ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add,
        ZMod.natCast_eq_natCast_iff, ZMod.val_add, ZMod.val_one, ← mul_add_one]
      exact Nat.ModEq.mul_left' 2 <| Nat.mod_modEq (i.val + 1) k
    refine ⟨fun i ↦ v i.cast, fun i ↦ w i.cast,
        fun i j heq ↦ hmul2_inj i j ?_, fun i j heq ↦ hmul2_inj i j ?_, fun i ↦ ?_, fun i ↦ ?_⟩
    · exact add_left_cancel <| hf_inj <|
        (hv i.cast).trans <| (congrArg Sum.inl heq).trans (hv j.cast).symm
    · exact add_left_cancel <| add_right_cancel <| hf_inj <|
        (hw i.cast).trans <| (congrArg Sum.inr heq).trans (hw j.cast).symm
    · rw [← hv, ← hw]
      exact hf_adj (v₀ + 2 * i.cast)
    · rw [← hw, ← hv, hmul2_succ_eq, ← add_assoc, ← add_assoc]
      exact hf_adj (v₀ + 2 * i.cast + 1)
  · refine (cycleGraph_isContained_iff_exists_inj_adj <| lt_mul_right two_pos hk).mpr
      -- even to `v` odd to `w`
      ⟨fun i ↦ (if Even i.val then .inl ∘ v else .inr ∘ w) (i.val / 2 : ℕ),
        fun i j hij ↦ ZMod.val_injective (2 * k) ?_, fun i ↦ ?_⟩
    · beta_reduce at hij
      have hi_div_2_lt_k : i.val / 2 < k := Nat.div_lt_of_lt_mul (ZMod.val_lt i)
      have hj_div_2_lt_k : j.val / 2 < k := Nat.div_lt_of_lt_mul (ZMod.val_lt j)
      by_cases hi : Even i.val <;> by_cases hj : Even j.val
      · rw [if_pos hi, if_pos hj] at hij
        rw [← Nat.two_mul_div_two_of_even hi, ← Nat.two_mul_div_two_of_even hj,
          ← ZMod.val_natCast_of_lt hi_div_2_lt_k, ← ZMod.val_natCast_of_lt hj_div_2_lt_k,
          hv <| Sum.inl_injective hij]
      · absurd hij
        rw [if_pos hi, if_neg hj]
        exact Sum.inl_ne_inr
      · absurd hij
        rw [if_neg hi, if_pos hj]
        exact Sum.inr_ne_inl
      · rw [if_neg hi, if_neg hj] at hij
        rw [Nat.not_even_iff_odd] at hi hj
        rw [← Nat.two_mul_div_two_add_one_of_odd hi, ← Nat.two_mul_div_two_add_one_of_odd hj,
          ← ZMod.val_natCast_of_lt hi_div_2_lt_k, ← ZMod.val_natCast_of_lt hj_div_2_lt_k,
          hw <| Sum.inr_injective hij]
    · beta_reduce
      rw [ZMod.val_add, ZMod.val_one]
      by_cases hi : Even i.val
      · have hi_add_one_lt_two_k : i.val + 1 < 2 * k := by
          refine Nat.lt_of_le_of_ne (ZMod.val_lt i) fun heq ↦ absurd hi ?_
          rw [← Nat.even_add_one, heq]
          exact ⟨k, two_mul k⟩
        have hi_add_one : ¬Even (i.val + 1) := Nat.not_even_iff_odd.mpr hi.add_one
        rw [Nat.mod_eq_of_lt hi_add_one_lt_two_k, if_pos hi, if_neg hi_add_one,
          Nat.succ_div_of_not_dvd <| even_iff_two_dvd.not.mp hi_add_one]
        exact hvw _
      · have hi_add_one : Even (i.val + 1) := Nat.even_add_one.mpr hi
        rw [if_neg hi, ← Nat.two_mul_div_two_of_even hi_add_one, Nat.mul_mod_mul_left,
          if_pos ⟨_, two_mul _⟩, Nat.mul_div_cancel_left _ two_pos, ZMod.natCast_mod,
          Nat.succ_div_of_dvd <| even_iff_two_dvd.mp hi_add_one, Nat.cast_add_one]
        exact hwv _

end sum

end SimpleGraph
