module

public import WeightedMIS.RegisterAllHalf
public import WeightedMIS.RegisterCutReadback
public import WeightedMIS.ExecutableMIS

/-!
# Final assembly of the deterministic independent-set output

Inputs: the stored class words `classWord (z v)` of the preprocessing point
`z = OriginalReduction.preprocessingPoint`, the stored nonnegativity mask of
the original weights, the stored table and vertex range words of the ribbon,
and the stored truncated weights. The procedure reads the half mask off the
class words (`01` is the class of `1/2`), builds the induced ribbon of the
half vertices, runs the compiled all-half solver on it, reads the local
output back to original vertex words, and finally walks the range words, the
class words and the mask in lockstep: a vertex is output when its original
weight is nonnegative and either its class is `1`, or its class is `1/2` and
its word was selected. The result is the stored word list of
`ExecutableMIS.solve`.
-/

@[expose] public section

namespace WeightedMIS.RegisterFinalAssembly

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords WeightedMIS.EmbeddingFaces WeightedMIS.RegisterWordFilter
open WeightedMIS.RegisterComponentSolve WeightedMIS.RegisterAllHalf
open WeightedMIS.RegisterCutReadback (classWord)
open WeightedMIS.GraphReachEncoded (setWords)

variable {p : ℕ}

/-! ## Class words -/

/-- The first bit of a class word (class `1`). -/
def hiBit : Bits 2 → Bool
  | .cons a _ => a

/-- The second bit of a class word (class `1/2`). -/
def loBit : Bits 2 → Bool
  | .cons _ (.cons b _) => b

theorem hiBit_classWord (z : ℚ) : hiBit (classWord z) = decide (z = 1) := by
  unfold classWord
  by_cases h1 : z = 1
  · simp [h1, hiBit]
  · by_cases h0 : z = 0 <;> simp [h1, h0, hiBit]

theorem loBit_classWord {z : ℚ} (hz : z = 0 ∨ z = 1 / 2 ∨ z = 1) :
    loBit (classWord z) = decide (z = 1 / 2) := by
  unfold classWord
  rcases hz with rfl | rfl | rfl <;> norm_num [loBit]

/-! ## The half mask -/

theorem maskAt_allocated {h : Heap} {ptr : Ptr} {bs : List Bool} (hm : MaskAt h ptr bs) :
    ptr < h.length := by
  cases bs with
  | nil => exact (List.getElem?_eq_some_iff.mp hm).1
  | cons b bs =>
    obtain ⟨t, hc, -⟩ := hm
    exact (List.getElem?_eq_some_iff.mp hc).1

/-- Argument 0 = class words; the result is the mask of their second bits. -/
def keepMaskBody (self : Fin p) : Command p :=
  .load (.register 0) 1 2 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call self [.register 2] [3]
      (.load (.register 1) 4 5 6 { CompiledTrie.failCases with
        bit := .load (.register 4) 7 8 9 { CompiledTrie.failCases with
          bit := .allocate 10 (.bit (.register 9) (.register 3)) (.ret [.register 10]) } }) }

def keepMaskBudget (k : ℕ) : ℕ := 50 * k + 13

theorem keepMask_compiled (code : Code p) (self : Fin p) (hself : code self = keepMaskBody self)
    {h : Heap} (hh : Valid h) {cp : Ptr} {cs : List (Bits 2)} (hc : WordsAt h cp cs) :
    ∃ out q, Extends h out ∧ Valid out ∧ MaskAt out q (cs.map loBit) ∧
      Within code h (initialRegisters [.pointer cp]) (code self) [.pointer q] out
        (keepMaskBudget cs.length) := by
  induction cs generalizing h cp with
  | nil =>
    have cell := WordsAt.nil_iff.mp hc
    refine ⟨h, 0, .refl h, hh, hh.1, ?_⟩
    rw [hself]
    refine (Within.load (pointer := cp) (c := Cell.nil) (by reg_simp) cell
      (ret_values (by reg_simp) le_rfl)).mono ?_
    simp [keepMaskBudget]
  | cons c cs ih =>
    obtain ⟨ch, ct, cell, hch, hct⟩ := WordsAt.cons_iff.mp hc
    obtain ⟨mid, mp, he, hv, hmp, hw⟩ := ih hh hct
    rcases c with _ | ⟨hi, _ | ⟨lo, _ | _⟩⟩
    cases hch with
    | @cons _ t1 _ _ _ c1 h1 =>
    cases h1 with
    | @cons _ t2 _ _ _ c2 h2 =>
    have hs := safe_allocate mid hv (.bit lo mp) (by
      intro q hq
      simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      exact maskAt_allocated hmp)
    have hext : Extends mid (mid ++ [Cell.bit lo mp]) := hs.1
    have hnew : (mid ++ [Cell.bit lo mp])[mid.length]? = some (Cell.bit lo mp) := by
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    refine ⟨mid ++ [Cell.bit lo mp], mid.length, he.trans hext, hs.2.1,
      ⟨mp, hnew, MaskAt.mono hext hmp⟩, ?_⟩
    rw [hself]
    refine (Within.load (pointer := cp) (c := Cell.cons ch ct) (by reg_simp) cell
      (call_of (by reg_simp) hw
      (Within.load (pointer := ch) (c := Cell.bit hi t1) (by reg_simp) (he.lookup c1)
      (Within.load (pointer := t1) (c := Cell.bit lo t2) (by reg_simp) (he.lookup c2)
      (Within.allocate (c := Cell.bit lo mp) (by reg_simp)
      (ret_values (by reg_simp) le_rfl)))))).mono ?_
    simp [keepMaskBudget, CellExpr.args]; omega

/-! ## The final selection -/

/-- Output the range words of vertices with nonnegative weight whose class is
`1`, or `1/2` with a selected word. -/
def finalE {W : ℕ} (sel : List (Bits W)) : List (Bits W) → List (Bits 2) → List Bool →
    List (Bits W)
  | x :: xs, c :: cs, b :: bs =>
    if b && (hiBit c || (loBit c && RegisterMembership.found x sel)) then
      x :: finalE sel xs cs bs
    else finalE sel xs cs bs
  | _, _, _ => []

/-- Copy the range word in register 4 in front of the rest in register 11. -/
def keepCmd : Command p :=
  .allocate 13 (.cons (.register 4) (.register 11)) (.ret [.register 13])

/-- Arguments 0 = range words, 1 = class words, 2 = nonnegativity mask,
3 = selected words. -/
def finalBody (self member : Fin p) : Command p :=
  .load (.register 0) 4 5 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .load (.register 1) 6 7 15 { CompiledTrie.failCases with
      cons := .load (.register 2) 8 9 10 { CompiledTrie.failCases with
        bit := .call self [.register 5, .register 7, .register 8, .register 3] [11]
          (.branch (.register 10)
            (.load (.register 6) 12 13 14 { CompiledTrie.failCases with
              bit := .branch (.register 14) keepCmd
                (.load (.register 12) 12 13 14 { CompiledTrie.failCases with
                  bit := .branch (.register 14)
                    (.call member [.register 4, .register 3] [12]
                      (.branch (.register 12) keepCmd (.ret [.register 11])))
                    (.ret [.register 11]) }) })
            (.ret [.register 11])) } } }

def finalBudget (W s k : ℕ) : ℕ := (RegisterMembership.budget W s + 100) * k + 13

theorem keepCmd_within (code : Code p) {h : Heap} (hh : Valid h) {regs : Registers}
    {W : ℕ} {xp rp : Ptr} {x : Bits W} {rest : List (Bits W)}
    (r4 : regs 4 = .pointer xp) (r11 : regs 11 = .pointer rp)
    (hx : BitsAt h xp x) (hr : WordsAt h rp rest) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (x :: rest) ∧
      Within code h regs keepCmd [.pointer q] out 11 := by
  obtain ⟨hs, hl⟩ := allocate_word_cons hh hx hr
  refine ⟨h ++ [Cell.cons xp rp], h.length, hs.1, hs.2.1, by simpa [Program.allocate] using hl, ?_⟩
  exact (Within.allocate (c := Cell.cons xp rp) (by reg_simp [r4, r11])
    (ret_values (by reg_simp) le_rfl)).mono (by simp [CellExpr.args])

theorem final_compiled (code : Code p) (self member cmp : Fin p)
    (hself : code self = finalBody self member)
    (hmem : code member = RegisterMembership.membershipBody member cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {W : ℕ} {h : Heap} (hh : Valid h) {sp : Ptr} {sel : List (Bits W)}
    (hs : WordsAt h sp sel) {xs : List (Bits W)} {cs : List (Bits 2)} {bs : List Bool}
    (hcs : cs.length = xs.length) (hbs : bs.length = xs.length) {xp cp bp : Ptr}
    (hx : WordsAt h xp xs) (hc : WordsAt h cp cs) (hb : MaskAt h bp bs) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (finalE sel xs cs bs) ∧
      Within code h (initialRegisters [.pointer xp, .pointer cp, .pointer bp, .pointer sp])
        (code self) [.pointer q] out (finalBudget W sel.length xs.length) := by
  induction xs generalizing h cs bs xp cp bp with
  | nil =>
    have cell := WordsAt.nil_iff.mp hx
    refine ⟨h, 0, .refl h, hh, ?_, ?_⟩
    · cases cs <;> cases bs <;> exact WordsAt.nil hh.1
    rw [hself]
    refine (Within.load (pointer := xp) (c := Cell.nil) (by reg_simp) cell
      (ret_values (by reg_simp) le_rfl)).mono ?_
    simp [finalBudget]
  | cons x xs ih =>
    obtain ⟨c, cs, rfl⟩ : ∃ c cs', cs = c :: cs' := by
      cases cs with
      | nil => simp at hcs
      | cons c cs' => exact ⟨c, cs', rfl⟩
    obtain ⟨b, bs, rfl⟩ : ∃ b bs', bs = b :: bs' := by
      cases bs with
      | nil => simp at hbs
      | cons b bs' => exact ⟨b, bs', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hcs hbs
    obtain ⟨xh, xt, xcell, hxh, hxt⟩ := WordsAt.cons_iff.mp hx
    obtain ⟨ch, ct, ccell, hch, hct⟩ := WordsAt.cons_iff.mp hc
    obtain ⟨bt, bcell, hbt⟩ := hb
    obtain ⟨mid, rp, he, hv, hrp, wr⟩ := ih hh hs hcs hbs hxt hct hbt
    have hxh' := hxh.mono he
    rcases c with _ | ⟨hi, _ | ⟨lo, _ | _⟩⟩
    cases hch with
    | @cons _ t1 _ _ _ c1 h1 =>
    cases h1 with
    | @cons _ t2 _ _ _ c2 h2 =>
    have c1' := he.lookup c1
    have c2' := he.lookup c2
    have hmw := RegisterMembership.compiled code member cmp hmem hcmp hxh' (hs.mono he)
    -- the registers after the recursive call
    let regs := bindResults (loadRegisters (loadRegisters (loadRegisters
      (initialRegisters [.pointer xp, .pointer cp, .pointer bp, .pointer sp]) 4 5 15
        (.cons xh xt)) 6 7 15 (.cons ch ct)) 8 9 10 (.bit b bt)) [11] [.pointer rp]
    have r4 : regs 4 = .pointer xh := by simp [regs, bindResults, loadRegisters, decoded]
    have r11 : regs 11 = .pointer rp := by simp [regs, bindResults]
    have r3 : regs 3 = .pointer sp := by
      simp [regs, bindResults, loadRegisters, decoded, initialRegisters]
    have r6 : regs 6 = .pointer ch := by simp [regs, bindResults, loadRegisters, decoded]
    have r10 : regs 10 = .flag b := by simp [regs, bindResults, loadRegisters, decoded]
    have pre : ∀ {out : Heap} {outs : List Value} {bud : ℕ},
        Within code mid regs
          (.branch (.register 10)
            (.load (.register 6) 12 13 14 { CompiledTrie.failCases with
              bit := .branch (.register 14) keepCmd
                (.load (.register 12) 12 13 14 { CompiledTrie.failCases with
                  bit := .branch (.register 14)
                    (.call member [.register 4, .register 3] [12]
                      (.branch (.register 12) keepCmd (.ret [.register 11])))
                    (.ret [.register 11]) }) })
            (.ret [.register 11])) outs out bud →
        Within code h (initialRegisters [.pointer xp, .pointer cp, .pointer bp, .pointer sp])
          (code self) outs out (bud + finalBudget W sel.length xs.length + 39) := by
      intro out outs bud hw
      rw [hself]
      refine (Within.load (pointer := xp) (c := Cell.cons xh xt) (by reg_simp [r3, r4, r6, r10, r11]) xcell
        (Within.load (pointer := cp) (c := Cell.cons ch ct) (by reg_simp [r3, r4, r6, r10, r11]) ccell
        (Within.load (pointer := bp) (c := Cell.bit b bt) (by reg_simp [r3, r4, r6, r10, r11]) bcell
        (call_of (by reg_simp [r3, r4, r6, r10, r11]) wr hw)))).mono ?_
      simp; omega
    have hbud : ∀ bud, bud ≤ RegisterMembership.budget W sel.length + 60 →
        bud + finalBudget W sel.length xs.length + 39 ≤
          finalBudget W sel.length (xs.length + 1) := by
      intro bud hb
      simp only [finalBudget]
      nlinarith
    have hrest : WordsAt mid rp (finalE sel xs cs bs) := hrp
    cases b
    · refine ⟨mid, rp, he, hv, by simpa [finalE] using hrest, ?_⟩
      refine (pre (Within.branch (b := false) (by reg_simp [r3, r4, r6, r10, r11])
        (ret_values (by reg_simp [r3, r4, r6, r10, r11]) le_rfl))).mono (hbud _ (by simp only [List.length_cons, List.length_nil]; omega))
    cases hi
    · cases lo
      · refine ⟨mid, rp, he, hv, by simpa [finalE, hiBit, loBit] using hrest, ?_⟩
        refine (pre (Within.branch (b := true) (by reg_simp [r3, r4, r6, r10, r11])
          (Within.load (pointer := ch) (c := Cell.bit false t1) (by reg_simp [r3, r4, r6, r10, r11]) c1'
          (Within.branch (b := false) (by reg_simp [r3, r4, r6, r10, r11])
          (Within.load (pointer := t1) (c := Cell.bit false t2) (by reg_simp [r3, r4, r6, r10, r11]) c2'
          (Within.branch (b := false) (by reg_simp [r3, r4, r6, r10, r11])
          (ret_values (by reg_simp [r3, r4, r6, r10, r11]) le_rfl))))))).mono (hbud _ (by simp only [List.length_cons, List.length_nil]; omega))
      · cases hf : RegisterMembership.found x sel
        · rw [hf] at hmw
          refine ⟨mid, rp, he, hv, by simpa [finalE, hiBit, loBit, hf] using hrest, ?_⟩
          refine (pre (Within.branch (b := true) (by reg_simp [r3, r4, r6, r10, r11])
            (Within.load (pointer := ch) (c := Cell.bit false t1) (by reg_simp [r3, r4, r6, r10, r11]) c1'
            (Within.branch (b := false) (by reg_simp [r3, r4, r6, r10, r11])
            (Within.load (pointer := t1) (c := Cell.bit true t2) (by reg_simp [r3, r4, r6, r10, r11]) c2'
            (Within.branch (b := true) (by reg_simp [r3, r4, r6, r10, r11])
            (call_of (by reg_simp [r3, r4, r6, r10, r11]) hmw (Within.branch (b := false) (by reg_simp [r3, r4, r6, r10, r11])
            (ret_values (by reg_simp [r3, r4, r6, r10, r11]) le_rfl))))))))).mono (hbud _ (by simp only [List.length_cons, List.length_nil]; omega))
        · rw [hf] at hmw
          obtain ⟨out, q, eo, vo, hq, wk⟩ := keepCmd_within code hv
            (regs := bindResults (loadRegisters (loadRegisters regs 12 13 14 (.bit false t1))
              12 13 14 (.bit true t2)) [12] [.flag true])
            (by simp [bindResults, loadRegisters, decoded, r4])
            (by simp [bindResults, loadRegisters, decoded, r11]) hxh' hrest
          refine ⟨out, q, he.trans eo, vo, by simpa [finalE, hiBit, loBit, hf] using hq, ?_⟩
          refine (pre (Within.branch (b := true) (by reg_simp [r3, r4, r6, r10, r11])
            (Within.load (pointer := ch) (c := Cell.bit false t1) (by reg_simp [r3, r4, r6, r10, r11]) c1'
            (Within.branch (b := false) (by reg_simp [r3, r4, r6, r10, r11])
            (Within.load (pointer := t1) (c := Cell.bit true t2) (by reg_simp [r3, r4, r6, r10, r11]) c2'
            (Within.branch (b := true) (by reg_simp [r3, r4, r6, r10, r11])
            (call_of (by reg_simp [r3, r4, r6, r10, r11]) hmw (Within.branch (b := true) (by reg_simp [r3, r4, r6, r10, r11])
            wk)))))))).mono (hbud _ (by simp only [List.length_cons, List.length_nil]; omega))
    · obtain ⟨out, q, eo, vo, hq, wk⟩ := keepCmd_within code hv
        (regs := loadRegisters regs 12 13 14 (.bit true t1))
        (by simp [loadRegisters, decoded, r4]) (by simp [loadRegisters, decoded, r11]) hxh' hrest
      refine ⟨out, q, he.trans eo, vo, by simpa [finalE, hiBit] using hq, ?_⟩
      refine (pre (Within.branch (b := true) (by reg_simp [r3, r4, r6, r10, r11])
        (Within.load (pointer := ch) (c := Cell.bit true t1) (by reg_simp [r3, r4, r6, r10, r11]) c1'
        (Within.branch (b := true) (by reg_simp [r3, r4, r6, r10, r11]) wk)))).mono (hbud _ (by omega))

/-! ## The encoded output -/

theorem finalE_map {W n : ℕ} (sel : List (Bits W)) (L : List (Fin n)) (cls : Fin n → Bits 2)
    (msk : Fin n → Bool) :
    finalE sel (L.map (fun v => word W v.val)) (L.map cls) (L.map msk) =
      (L.filter (fun v => msk v && (hiBit (cls v) ||
        (loBit (cls v) && RegisterMembership.found (word W v.val) sel)))).map
        (fun v => word W v.val) := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    simp only [List.map_cons, finalE, ih, List.filter_cons]
    split_ifs <;> simp_all

section Solve

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- The preprocessing point of the original weights. -/
abbrev zPoint (left right : Fin m → Fin n) (weights : Fin n → ℚ) : Fin n → ℚ :=
  OriginalReduction.preprocessingPoint (left := left) (right := right) weights (List.finRange n)

/-- The retained half vertices. -/
abbrev halfKeep (left right : Fin m → Fin n) (weights : Fin n → ℚ) : Fin n → Prop :=
  fun v => zPoint left right weights v = 1 / 2

/-- The truncated weights of the half vertices, in local order. -/
abbrev halfWeights (left right : Fin m → Fin n) (weights : Fin n → ℚ) :
    Fin (ComputedInduced.vertices (halfKeep left right weights)).length → ℚ :=
  fun v => NegativeWeights.nonnegative weights
    (ComputedInduced.vertexEquiv (halfKeep left right weights) v).val

/-- The sum of the hard budgets over the actual components of the induced
all-half instance solved by `ExecutableMIS.solve`. -/
def residualHardSum (hb : HardBudget) (R : Ribbon left right) (weights : Fin n → ℚ) : ℕ :=
  hardSum hb (ComputedInduced.ribbon left right (halfKeep left right weights) R)
    (halfWeights left right weights)

/-- The all-half solution of the induced half graph. -/
abbrev halfSolution (R : Ribbon left right) (weights : Fin n → ℚ) :
    Finset (Fin (ComputedInduced.vertices (halfKeep left right weights)).length) :=
  ExecutableReduction.allHalfSolve (ComputedInduced.ribbon left right (halfKeep left right weights) R)
    (halfWeights left right weights)

theorem mem_solve_iff (R : Ribbon left right) (weights : Fin n → ℚ) (v : Fin n) :
    v ∈ ExecutableMIS.solve R weights ↔ 0 ≤ weights v ∧
      (zPoint left right weights v = 1 ∨ (zPoint left right weights v = 1 / 2 ∧
        ∃ i ∈ halfSolution R weights,
          (ComputedInduced.vertices (halfKeep left right weights)).get i = v)) := by
  simp only [ExecutableMIS.solve, NegativeWeights.prune, Finset.mem_filter,
    Persistence.mem_replacement, InducedReduction.mem_lift, GraphRelabeling.mem_mapSet]
  constructor
  · rintro ⟨h1 | ⟨hk, hk', hJ⟩, hw⟩
    · exact ⟨hw, Or.inl h1⟩
    · exact ⟨hw, Or.inr ⟨hk, _, hJ, by
        rw [show (ComputedInduced.vertices (halfKeep left right weights)).get _ =
          (ComputedInduced.vertexEquiv (halfKeep left right weights) _).val from rfl,
          Equiv.apply_symm_apply]⟩⟩
  · rintro ⟨hw, h1 | ⟨hk, i, hi, hiv⟩⟩
    · exact ⟨Or.inl h1, hw⟩
    · refine ⟨Or.inr ⟨hk, hk, ?_⟩, hw⟩
      have he : (ComputedInduced.vertexEquiv (halfKeep left right weights)).symm ⟨v, hk⟩ = i := by
        rw [Equiv.symm_apply_eq]
        exact Subtype.ext hiv.symm
      rw [he]
      exact hi

/-- The encoded final selection is the stored output of `ExecutableMIS.solve`. -/
theorem finalE_solve {W : ℕ} (hn : n < 2 ^ W) (R : Ribbon left right) (weights : Fin n → ℚ) :
    finalE (selectFilter (rangeWords W (ComputedInduced.vertices (halfKeep left right weights)).length)
        ((ComputedInduced.vertices (halfKeep left right weights)).map (fun u => word W u.val))
        (setWords W (halfSolution R weights)))
      (rangeWords W n) ((List.finRange n).map fun v => classWord (zPoint left right weights v))
      (List.ofFn fun v => decide (0 ≤ weights v)) =
      setWords W (ExecutableMIS.solve R weights) := by
  have hz := OriginalReduction.preprocessingPoint_correct (left := left) (right := right)
    weights (List.finRange n) (fun v => List.mem_finRange v)
  have hL : (ComputedInduced.vertices (halfKeep left right weights)).length < 2 ^ W :=
    lt_of_le_of_lt (by simpa [ComputedInduced.vertices] using
      List.length_filter_le _ (List.finRange n)) hn
  rw [← AllHalfEncoded.rangeWords_eq W n, List.ofFn_eq_map]
  change finalE _ ((List.finRange n).map fun v => word W v.val) _ _ = _
  rw [finalE_map]
  conv_rhs => rw [setWords]
  change _ = ((List.finRange n).filter (· ∈ ExecutableMIS.solve R weights)).map
    (fun v => word W v.val)
  congr 1
  apply List.filter_congr
  intro v _
  rw [hiBit_classWord, loBit_classWord (hz.1 v)]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    ResidualListReach.found_iff_mem]
  rw [AllHalfEncoded.mem_selectFilter hn _ hL, mem_solve_iff]

end Solve

/-! ## The assembly procedure -/

/-- Arguments 0 = class words, 1 = nonnegativity mask, 2 = table,
3 = vertex range words, 4 = truncated weights. -/
def assemblyBody (keepMask induced allHalf select final : Fin p) : Command p :=
  .call keepMask [.register 0] [5]
    (.call induced [.register 2, .register 3, .register 5, .register 4] [6, 7, 8, 9]
      (.call allHalf [.register 6, .register 7, .register 9] [10]
        (.call select [.register 7, .register 8, .register 10] [11]
          (.call final [.register 3, .register 0, .register 1, .register 11] [12]
            (.ret [.register 12])))))

structure Procedures (p : ℕ) where
  assembly : Fin p
  keepMask : Fin p
  final : Fin p
  allHalf : RegisterAllHalf.Procedures p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.assembly = assemblyBody ids.keepMask ids.allHalf.component.induced.induced
    ids.allHalf.allHalf ids.allHalf.component.induced.filter.select ids.final ∧
  code ids.keepMask = keepMaskBody ids.keepMask ∧
  code ids.final = finalBody ids.final ids.allHalf.component.roots.residual.member ∧
  ids.allHalf.Matches code

/-- Events of the assembly apart from the hard calls. -/
def assemblyBudget (W n m : ℕ) : ℕ :=
  keepMaskBudget n + RegisterInducedRibbon.inducedRibbonBudget W n m + allHalfBudget W n m +
    selectBudget W n n + finalBudget W n n + 60

/-- All budget definitions entering `assemblyBudget`. -/
syntax "unfold_assembly_budget" : tactic

macro_rules
  | `(tactic| unfold_assembly_budget) => `(tactic| (set_option linter.unusedSimpArgs false in
      simp only [assemblyBudget, keepMaskBudget, finalBudget,
        RegisterInducedRibbon.inducedRibbonBudget, RegisterWordFilter.maskBudget,
        RegisterEdgeWords.inducedBudget, allHalfBudget, RegisterGraphArcs.adjBudget,
        RegisterComponentRoots.rootsBudget, RegisterComponentRoots.rootItemBudget,
        RegisterComponentRoots.allLeBudget, RegisterResidualSearch.budget,
        RegisterResidualReach.budget, RegisterResidualReach.stepBudget,
        RegisterResidualCrossing.budget, RegisterResidualPredicate.budget,
        RegisterMembership.budget, RegisterRouteLookup.budget, itemBudget,
        RegisterInducedRibbon.componentRibbonBudget, RegisterWordFilter.membersBudget,
        RegisterEdgeWords.componentBudget, RegisterEdgeWords.keysBudget,
        RegisterInducedRibbon.tailBudget, RegisterRestrictTable.restrictBudget,
        RegisterRestrictTable.tableBudget, RegisterRestrictTable.recordBudget,
        RegisterRestrictTable.endpointsBudget, RegisterRestrictCorner.cornersBudget,
        RegisterRestrictCorner.cornerRBudget, RegisterFirstReturn.scanBudget,
        RegisterFirstReturn.stepBudget, RegisterRecordLookup.cornerBudget,
        RegisterRecordLookup.findBudget, RegisterWordAssoc.relabelBudget,
        RegisterWordAssoc.assocBudget, RegisterWordFilter.selectBudget,
        RegisterWordFilter.takeBudget, localBudget, colorBudget, RegisterGraphArcs.parityBudget,
        RegisterGraphArcs.nodesBudget]))

/-- The polynomial part of the assembly budget in closed form. -/
theorem assemblyBudget_le (W n m : ℕ) :
    assemblyBudget W n m ≤ 40000 * (W + 1) * (n + m + 1) ^ 4 := by
  have hmono : assemblyBudget W n m ≤ assemblyBudget W (n + m + 1) (n + m + 1) := by
    unfold_assembly_budget
    gcongr <;> omega
  refine hmono.trans ?_
  have hN : 1 ≤ n + m + 1 := by omega
  generalize n + m + 1 = N at hN ⊢
  have h1 : N ≤ N ^ 4 := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ 4 := Nat.pow_le_pow_right hN (by norm_num)
  have h2 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN (by norm_num)
  have h3 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right hN (by norm_num)
  have h0 : 1 ≤ N ^ 4 := Nat.one_le_pow 4 N hN
  have w1 := Nat.mul_le_mul_left W h1
  have w2 := Nat.mul_le_mul_left W h2
  have w3 := Nat.mul_le_mul_left W h3
  have w0 := Nat.mul_le_mul_left W h0
  unfold_assembly_budget
  ring_nf
  ring_nf at w1 w2 w3 w0
  nlinarith

/-- **Final assembly.** From the stored preprocessing classes, the
nonnegativity mask of the weights, the stored table and range words of the
ribbon, and the stored truncated weights, the procedure returns the stored
words of the actual output `ExecutableMIS.solve R weights`, within a
polynomial budget plus the hard budgets of the actual components of the
induced all-half instance. -/
theorem assembly_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} (WeightAt : Heap → Ptr → ℚ → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    (hb : HardBudget) (hard : HardSpec code ids.allHalf.component.hard W WeightAt hb)
    {n m : ℕ} (hn : n < 2 ^ W) (hmW : m < 2 ^ W) {left right : Fin m → Fin n}
    (R : Ribbon left right) (weights : Fin n → ℚ)
    {h : Heap} (hh : Valid h) {cp np tp rp wp : Ptr}
    (hc : WordsAt h cp ((List.finRange n).map fun v =>
      classWord (OriginalReduction.preprocessingPoint (left := left) (right := right) weights
        (List.finRange n) v)))
    (hnn : MaskAt h np (List.ofFn fun v => decide (0 ≤ weights v)))
    (hT : RecordsAt h tp (encodeRibbon W R)) (hr : WordsAt h rp (rangeWords W n))
    (hw : ListRep WeightAt h wp (List.ofFn (NegativeWeights.nonnegative weights))) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (setWords W (ExecutableMIS.solve R weights)) ∧
      Within code h
        (initialRegisters [.pointer cp, .pointer np, .pointer tp, .pointer rp, .pointer wp])
        (code ids.assembly) [.pointer q] out
        (assemblyBudget W n m + residualHardSum hb R weights) := by
  have hm' := hm
  obtain ⟨hasm, hkeep, hfinal, hall⟩ := hm'
  have hall' := hall
  obtain ⟨-, -, hcomp⟩ := hall'
  obtain ⟨-, -, -, -, -, hroots, -, hind⟩ := hcomp
  obtain ⟨-, -, -, -, -, hres⟩ := hroots
  have hfm := hind.2.2.2.1
  have hz := OriginalReduction.preprocessingPoint_correct (left := left) (right := right)
    weights (List.finRange n) (fun v => List.mem_finRange v)
  -- the half mask
  obtain ⟨o1, mp, e1, v1, hmp, w1⟩ := keepMask_compiled code ids.keepMask hkeep hh hc
  have hmask : (((List.finRange n).map fun v => classWord (zPoint left right weights v)).map
      loBit) = List.ofFn (fun v => decide (halfKeep left right weights v)) := by
    rw [List.map_map, List.ofFn_eq_map]
    apply List.map_congr_left
    intro v _
    exact loBit_classWord (hz.1 v)
  rw [hmask] at hmp
  -- the induced ribbon
  obtain ⟨o2, q, l, vp, s, e2, v2, hq, hl, hvp, hs, w2⟩ :=
    RegisterInducedRibbon.induced_compiled ids.allHalf.component.induced code hind WeightAt
      weightMono hn hmW R (halfKeep left right weights) (NegativeWeights.nonnegative weights) v1
      (hT.mono e1) (hr.mono e1) hmp (ListRep.mono e1 (weightMono e1) hw)
  have e12 := e1.trans e2
  -- the all-half solver
  have hkn : (ComputedInduced.vertices (halfKeep left right weights)).length ≤ n := by
    simpa [ComputedInduced.vertices] using List.length_filter_le _ (List.finRange n)
  have hkm : (ComputedInduced.edges left right (halfKeep left right weights)).length ≤ m := by
    simpa [ComputedInduced.edges] using List.length_filter_le _ (List.finRange m)
  have hzr := InducedReduction.residual_optimal (EdgeTransport.Adj left right)
    (NegativeWeights.nonnegative weights) (zPoint left right weights) hz.2 hz.1
  have hopt := ComputedInduced.half_optimal left right (halfKeep left right weights)
    (NegativeWeights.nonnegative weights) hzr
  obtain ⟨o3, jp, e3, v3, hj, w3⟩ := allHalf_compiled ids.allHalf code hall WeightAt weightMono hb
    hard (lt_of_le_of_lt hkn hn) (lt_of_le_of_lt hkm hmW)
    (ComputedInduced.ribbon left right (halfKeep left right weights) R)
    (halfWeights left right weights)
    (fun v => NegativeWeights.nonnegative_nonnegative weights _) hopt v2 hq hl hs
  -- reading the half solution back
  obtain ⟨o4, sel, e4, v4, hsel, w4⟩ := select_compiled code
    ids.allHalf.component.induced.filter.select ids.allHalf.component.induced.filter.mem
    ids.allHalf.component.induced.filter.cmp hfm.2.1 hfm.2.2.2.2.2.1 hfm.2.2.2.2.2.2
    (fun h p (w : Bits W) => BitsAt h p w) (fun he _ _ hb => hb.mono he) v3 (hl.mono e3)
    (hvp.mono e3) hj
  -- the final selection
  have e14 := (e12.trans e3).trans e4
  obtain ⟨o5, q5, e5, v5, hq5, w5⟩ := final_compiled code ids.final
    ids.allHalf.component.roots.residual.member ids.allHalf.component.roots.residual.cmp hfinal
    hres.2.2.2.1 hres.2.2.2.2.2.2.2 v4 hsel (by simp) (by simp) (hr.mono e14) (hc.mono e14)
    (MaskAt.mono e14 hnn)
  rw [finalE_solve hn R weights] at hq5
  refine ⟨o5, q5, e14.trans e5, v5, hq5, ?_⟩
  rw [hasm]
  refine (call_of (by reg_simp) w1 (call_of (by reg_simp) w2 (call_of (by reg_simp) w3
    (call_of (by reg_simp) w4 (call_of (by reg_simp) w5 (ret_values (by reg_simp) le_rfl)))))).mono ?_
  have hb3 := allHalfBudget_mono (W := W) hkn hkm
  have hks := AllHalfEncoded.setWords_length_le (W := W) (halfSolution R weights)
  have hb4 := selectBudget_mono (W := W) (hks.trans hkn) (show
    ((ComputedInduced.vertices (halfKeep left right weights)).map (fun u => word W u.val)).length
      ≤ n by simpa using hkn)
  have hsl := AllHalfEncoded.selectFilter_length_le
    (rangeWords W (ComputedInduced.vertices (halfKeep left right weights)).length)
    ((ComputedInduced.vertices (halfKeep left right weights)).map (fun u => word W u.val))
    (setWords W (halfSolution R weights))
  have hb5 : finalBudget W (selectFilter
      (rangeWords W (ComputedInduced.vertices (halfKeep left right weights)).length)
      ((ComputedInduced.vertices (halfKeep left right weights)).map (fun u => word W u.val))
      (setWords W (halfSolution R weights))).length n ≤ finalBudget W n n := by
    have := membershipBudget_mono (k := W) (hsl.trans (by simpa using hkn))
    simp only [finalBudget]
    gcongr
  simp only [assemblyBudget, residualHardSum, halfSolution, rangeWords_length, List.length_map,
    List.length_finRange, List.length_cons, List.length_nil] at hb3 hb4 hb5 ⊢
  omega

end WeightedMIS.RegisterFinalAssembly
