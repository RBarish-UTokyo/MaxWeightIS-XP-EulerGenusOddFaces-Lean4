module

public import WeightedMIS.RegisterComponentSolve
public import WeightedMIS.RegisterListFold

/-!
# The compiled all-half solver

From the stored table of a ribbon, its vertex range words and its stored
weights, the procedure builds the adjacency arcs and the unit word, computes
the component roots, folds the component procedure over the roots (each call
prepends the original words of one solved component), and finally keeps the
range words that occur in the collected words. The result is the stored word
list of `ExecutableReduction.allHalfSolve`. The budget is a polynomial in the
width and the sizes plus the sum of the hard-solver budgets of the actual
computed components.
-/

@[expose] public section

namespace WeightedMIS.RegisterAllHalf

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.ExpandedWords WeightedMIS.ResidualWords WeightedMIS.EmbeddingFaces
open WeightedMIS.RegisterComponentSolve
open WeightedMIS.GraphReachEncoded (one adjArcs edgeWords setWords)

variable {p : ℕ}

/-- Arguments 0 = table, 1 = vertex range words, 2 = weights. -/
def allHalfBody (adjArcs roots fold members : Fin p) : Command p :=
  .allocate 3 (.bit (.flag true) .null)
    (.call adjArcs [.register 0, .register 3, .null] [4]
      (.call roots [.register 4, .register 3, .register 1] [5]
        (.allocate 6 (.pair (.register 4) (.register 3))
          (.allocate 7 (.pair (.register 2) (.register 6))
            (.allocate 8 (.pair (.register 1) (.register 7))
              (.allocate 9 (.pair (.register 0) (.register 8))
                (.call fold [.register 5, .register 9, .null] [10]
                  (.call members [.register 1, .register 10] [11]
                    (.ret [.register 11])))))))))

structure Procedures (p : ℕ) where
  allHalf : Fin p
  fold : Fin p
  component : RegisterComponentSolve.Procedures p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.allHalf = allHalfBody ids.component.arcs.adjArcs ids.component.roots.roots ids.fold
    ids.component.induced.filter.members ∧
  code ids.fold = RegisterListFold.body ids.fold ids.component.item ∧
  ids.component.Matches code

/-- Events of the all-half solver apart from the hard calls. -/
def allHalfBudget (W n m : ℕ) : ℕ :=
  RegisterGraphArcs.adjBudget m + RegisterComponentRoots.rootsBudget W (2 * m) n +
    (itemBudget W n m + 30) * n + RegisterWordFilter.membersBudget W (n * n) n + 120

/-- The sum of the hard budgets of the actual computed components. -/
def hardSum (hb : HardBudget) {n m : ℕ} {left right : Fin m → Fin n} (H : Ribbon left right)
    (w : Fin n → ℚ) : ℕ :=
  ((ComputedComponents.roots left right).map (componentHardBudget hb H w)).sum

set_option linter.unusedSimpArgs false in
/-- The polynomial part of the all-half budget is monotone in the sizes. -/
theorem allHalfBudget_mono {W n m n' m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') :
    allHalfBudget W n m ≤ allHalfBudget W n' m' := by
  simp only [allHalfBudget, RegisterGraphArcs.adjBudget, RegisterComponentRoots.rootsBudget,
    RegisterComponentRoots.rootItemBudget, RegisterComponentRoots.allLeBudget,
    RegisterResidualSearch.budget, RegisterResidualReach.budget, RegisterResidualReach.stepBudget,
    RegisterResidualCrossing.budget, RegisterResidualPredicate.budget, RegisterMembership.budget,
    RegisterRouteLookup.budget, itemBudget, RegisterInducedRibbon.componentRibbonBudget,
    RegisterWordFilter.membersBudget, RegisterEdgeWords.componentBudget,
    RegisterEdgeWords.keysBudget, RegisterInducedRibbon.tailBudget,
    RegisterRestrictTable.restrictBudget, RegisterRestrictTable.tableBudget,
    RegisterRestrictTable.recordBudget, RegisterRestrictTable.endpointsBudget,
    RegisterRestrictCorner.cornersBudget, RegisterRestrictCorner.cornerRBudget,
    RegisterFirstReturn.scanBudget, RegisterFirstReturn.stepBudget,
    RegisterRecordLookup.cornerBudget, RegisterRecordLookup.findBudget,
    RegisterWordAssoc.relabelBudget, RegisterWordAssoc.assocBudget,
    RegisterWordFilter.selectBudget, RegisterWordFilter.takeBudget, localBudget, colorBudget,
    RegisterGraphArcs.parityBudget, RegisterGraphArcs.nodesBudget]
  gcongr

theorem sum_map_add {α : Type*} (xs : List α) (a : ℕ) (f : α → ℕ) :
    (xs.map (fun x => a + f x)).sum = a * xs.length + (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

/-- The compiled all-half solver returns the stored words of
`ExecutableReduction.allHalfSolve` within a polynomial budget plus the hard
budgets of the computed components. -/
theorem allHalf_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} (WeightAt : Heap → Ptr → ℚ → Prop)
    (weightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, WeightAt h ptr x → WeightAt h' ptr x)
    (hb : HardBudget) (hard : HardSpec code ids.component.hard W WeightAt hb)
    {n m : ℕ} (hn : n < 2 ^ W) (hmW : m < 2 ^ W) {left right : Fin m → Fin n}
    (H : Ribbon left right) (w : Fin n → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    {h : Heap} (hh : Valid h) {tp rp wp : Ptr}
    (hT : RecordsAt h tp (encodeRibbon W H)) (hr : WordsAt h rp (rangeWords W n))
    (hwp : ListRep WeightAt h wp (List.ofFn w)) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (setWords W (ExecutableReduction.allHalfSolve H w)) ∧
      Within code h (initialRegisters [.pointer tp, .pointer rp, .pointer wp]) (code ids.allHalf)
        [.pointer q] out (allHalfBudget W n m + hardSum hb H w) := by
  have hm' := hm
  obtain ⟨hall, hfold, hcomp⟩ := hm'
  have hcomp' := hcomp
  obtain ⟨-, -, -, -, -, hroots, harcs, hind⟩ := hcomp'
  have hfm := hind.2.2.2.1
  -- the unit word and the adjacency arcs
  obtain ⟨e0, v0, b0⟩ := RegisterGraphArcs.alloc_one hh
  obtain ⟨o1, ap, e1, v1, hap, w1⟩ :=
    RegisterGraphArcs.adjArcs_compiled ids.component.arcs code harcs v0 (hT.mono e0) b0
  rw [RegisterGraphArcs.edgePairs_encode] at hap
  have e01 := e0.trans e1
  -- the roots
  obtain ⟨o2, rts, e2, v2, hrts, w2⟩ := RegisterComponentRoots.graphRoots_compiled
    ids.component.roots code hroots hn v1 hap (b0.mono e1) (hr.mono e01)
  have e02 := e01.trans e2
  -- the context record
  have hop := b0.mono (e1.trans e2)
  have hap2 := hap.mono e2
  obtain ⟨f3, u3, c3⟩ := alloc_pair v2 hap2.allocated hop.allocated
  set o3 := o2 ++ [Cell.pair ap h.length] with ho3
  have hwp3 : wp < o3.length := lt_of_lt_of_le hwp.allocated (e02.trans f3).length_le
  have hl3 : o2.length < o3.length := by rw [ho3]; simp
  obtain ⟨f4, u4, c4⟩ := alloc_pair u3 hwp3 hl3
  set o4 := o3 ++ [Cell.pair wp o2.length] with ho4
  have hrp4 : rp < o4.length := lt_of_lt_of_le hr.allocated ((e02.trans f3).trans f4).length_le
  have hl4 : o3.length < o4.length := by rw [ho4]; simp
  obtain ⟨f5, u5, c5⟩ := alloc_pair u4 hrp4 hl4
  set o5 := o4 ++ [Cell.pair rp o3.length] with ho5
  have htp5 : tp < o5.length :=
    lt_of_lt_of_le hT.allocated (((e02.trans f3).trans f4).trans f5).length_le
  have hl5 : o4.length < o5.length := by rw [ho5]; simp
  obtain ⟨f6, u6, c6⟩ := alloc_pair u5 htp5 hl5
  set o6 := o5 ++ [Cell.pair tp o4.length] with ho6
  have e26 := ((f3.trans f4).trans f5).trans f6
  have e06 := e02.trans e26
  have hctx : CtxAt WeightAt W H w o6 o5.length :=
    ⟨tp, o4.length, rp, o3.length, wp, o2.length, ap, h.length, c6, f6.lookup c5,
      (f5.trans f6).lookup c4, ((f4.trans f5).trans f6).lookup c3, hT.mono e06, hr.mono e06,
      ListRep.mono e06 (weightMono e06) hwp, hap2.mono e26, hop.mono e26⟩
  -- the fold over the roots
  obtain ⟨o7, cp, e7, v7, hcp, w7⟩ := RegisterListFold.compiled code ids.fold ids.component.item
    hfold (fun h p (r : Fin n) => BitsAt h p (word W r.val))
    (fun h p (_ : Unit) => CtxAt WeightAt W H w h p) WordsAt
    (fun he _ _ hb => hb.mono he) (fun he _ _ hc => CtxAt.mono weightMono he hc)
    (fun _ acc r => AllHalfEncoded.step W H w acc r)
    (fun r => itemBudget W n m + componentHardBudget hb H w r) u6
    (ListRep.mono e26 (fun _ _ hb => hb.mono e26) hrts) (data := ()) hctx
    (WordsAt.nil u6.1 : WordsAt o6 0 ([] : List (Bits W)))
    (fun _ r _ _ _ hv _ _ hx hd hs =>
      item_compiled ids.component code hcomp WeightAt weightMono hb hard hn hmW H w hw ho r hv
        hx hd hs)
  change WordsAt o7 cp (AllHalfEncoded.collect W H w (ComputedComponents.roots left right)) at hcp
  -- the range words that were collected
  obtain ⟨o8, q, e8, v8, hq, w8⟩ := RegisterWordFilter.members_compiled
    ids.component.induced.filter code hfm v7 (hr.mono (e06.trans e7)) hcp
  rw [AllHalfEncoded.filter_collect W hn] at hq
  refine ⟨o8, q, (e06.trans e7).trans e8, v8, hq, ?_⟩
  rw [hall]
  refine (Within.allocate (c := Cell.bit true 0) (by reg_simp)
    (call_of (by reg_simp) w1 (call_of (by reg_simp) w2
    (Within.allocate (c := Cell.pair ap h.length) (by reg_simp)
    (Within.allocate (c := Cell.pair wp o2.length) (by reg_simp)
    (Within.allocate (c := Cell.pair rp o3.length) (by reg_simp [ho3])
    (Within.allocate (c := Cell.pair tp o4.length) (by reg_simp [ho3, ho4])
    (call_of (by reg_simp [ho3, ho4, ho5]) w7 (call_of (by reg_simp) w8
    (ret_values (by reg_simp) le_rfl)))))))))).mono ?_
  have hrl := ComputedComponents.roots_length_le left right
  have hcl := AllHalfEncoded.collect_length_le W H w (ComputedComponents.roots left right)
  have hcl' : (AllHalfEncoded.collect W H w (ComputedComponents.roots left right)).length ≤
      n * n := hcl.trans (Nat.mul_le_mul_left n hrl)
  have hmb : RegisterWordFilter.membersBudget W
      (AllHalfEncoded.collect W H w (ComputedComponents.roots left right)).length n ≤
      RegisterWordFilter.membersBudget W (n * n) n := by
    have := membershipBudget_mono (k := W) hcl'
    simp only [RegisterWordFilter.membersBudget]
    gcongr
  have hfb : (itemBudget W n m) * (ComputedComponents.roots left right).length +
      30 * (ComputedComponents.roots left right).length ≤ (itemBudget W n m + 30) * n := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_left _ hrl
  simp only [sum_map_add, encodeRibbon_length, rangeWords_length, CellExpr.args,
    List.length_cons, List.length_nil, allHalfBudget, hardSum] at hmb ⊢
  omega

end WeightedMIS.RegisterAllHalf
