module

public import WeightedMIS.RegisterNetworkTable
public import WeightedMIS.RegisterMembership

/-!
# Reading the half-integral point from the stored cut

For every vertex word `x` the procedure builds the two node words `10·x` and
`11·x` of its left and right copies, tests their membership in the stored
reached cut with the compiled membership scan, and emits a two-bit class word:
`10` when only the left copy is reached (value `1`), `00` when only the right
copy is reached (value `0`), and `01` otherwise (value `1/2`).

When the stored cut represents the source side `X`, the emitted list is
`classWord` of `DoubleCover.rounded (leftCover X) (rightCover X)`, the point
computed by `MaxFlowPreprocessing.lpPoint`.
-/

@[expose] public section

namespace WeightedMIS.RegisterCutReadback

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords
open WeightedMIS.DoubleCoverNetwork WeightedMIS.GraphReachEncoded WeightedMIS.NetworkWords
open WeightedMIS.RegisterNetworkWeights (allocate_fits bit_fits null_lt)

/-! ## Class words -/

/-- The two-bit class of a half-integral value: `0 ↦ 00`, `1/2 ↦ 01`, `1 ↦ 10`. -/
def classWord (z : ℚ) : Bits 2 :=
  if z = 1 then .cons true (.cons false .nil)
  else if z = 0 then .cons false (.cons false .nil)
  else .cons false (.cons true .nil)

/-- The class word computed from the two membership flags. -/
def classBits (inL inR : Bool) : Bits 2 :=
  .cons (inL && !inR) (.cons (inL == inR) .nil)

theorem classBits_eq {n : ℕ} (X : Finset (Node (Fin n))) (v : Fin n) :
    classBits (decide ((Sum.inr (false, v) : Node (Fin n)) ∈ X))
      (decide ((Sum.inr (true, v) : Node (Fin n)) ∈ X)) =
      classWord (DoubleCover.rounded (leftCover (MaxFlowPreprocessing.membership X))
        (rightCover (MaxFlowPreprocessing.membership X)) v) := by
  by_cases hl : (Sum.inr (false, v) : Node (Fin n)) ∈ X <;>
    by_cases hr : (Sum.inr (true, v) : Node (Fin n)) ∈ X <;>
    simp [classBits, classWord, DoubleCover.rounded, Persistence.indicator, leftCover, rightCover,
      MaxFlowPreprocessing.membership, hl, hr] <;> norm_num

/-- Membership of node words in a stored cut list. -/
theorem found_nodeWord {W n : ℕ} (hn : n < 2 ^ W) {seen : List (Bits (W + 2))}
    {X : Finset (Node (Fin n))} (hseen : seen.toFinset = X.image (nodeWord W)) (u : Node (Fin n)) :
    RegisterMembership.found (nodeWord W u) seen = decide (u ∈ X) := by
  apply Bool.eq_iff_iff.mpr
  rw [ResidualListReach.found_iff_mem, decide_eq_true_eq, ← List.mem_toFinset, hseen,
    Finset.mem_image]
  constructor
  · rintro ⟨y, hy, he⟩
    exact nodeWord_injective hn he ▸ hy
  · intro hu
    exact ⟨u, hu, rfl⟩

/-! ## Procedures -/

structure Procedures (p : ℕ) where
  cmp : Fin p
  member : Fin p
  item : Fin p
  self : Fin p

variable {p : ℕ}

/-- Allocate the class word `hi lo` and return it. -/
def leaf (hi lo : Bool) : Command p :=
  .allocate 8 (.bit (.flag lo) .null)
    (.allocate 9 (.bit (.flag hi) (.register 8)) (.ret [.register 9]))

/-- Arguments: vertex word, cut list. Result: the class word. -/
def itemBody (member : Fin p) : Command p :=
  .allocate 2 (.bit (.flag false) (.register 0))
    (.allocate 3 (.bit (.flag true) (.register 2))
      (.allocate 4 (.bit (.flag true) (.register 0))
        (.allocate 5 (.bit (.flag true) (.register 4))
          (.call member [.register 3, .register 1] [6]
            (.call member [.register 5, .register 1] [7]
              (.branch (.register 6)
                (.branch (.register 7) (leaf false true) (leaf true false))
                (.branch (.register 7) (leaf false false) (leaf false true))))))))

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  code d.cmp = RegisterComparator.comparatorBody d.cmp ∧
  code d.member = RegisterMembership.membershipBody d.member d.cmp ∧
  code d.item = itemBody d.member ∧
  code d.self = RegisterListMap.body d.self d.item

theorem leaf_within (code : Code p) {h : Heap} (hh : Valid h) (regs : Registers) (hi lo : Bool) :
    ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (.cons hi (.cons lo .nil)) ∧
      Within code h regs (leaf hi lo) [.pointer q] out 19 := by
  let H1 := h ++ [Cell.bit lo 0]
  obtain ⟨e1, v1, c1⟩ := allocate_fits hh (bit_fits (b := lo) (null_lt hh))
  obtain ⟨e2, v2, c2⟩ := allocate_fits v1 (bit_fits (b := hi) (h := H1) (a := h.length)
    (by simp [H1]))
  refine ⟨H1 ++ [Cell.bit hi h.length], H1.length, e1.trans e2, v2,
    .cons c2 (.cons (e2.lookup c1) (.nil ((e1.trans e2).lookup hh.1))), ?_⟩
  let r1 := Function.update regs 8 (.pointer h.length)
  let r2 := Function.update r1 9 (.pointer H1.length)
  have last : Within code (H1 ++ [Cell.bit hi h.length]) r2 (.ret [.register 9])
      [.pointer H1.length] (H1 ++ [Cell.bit hi h.length]) 3 := by
    simpa [values, Atom.eval, r2] using
      Within.ret code (H1 ++ [Cell.bit hi h.length]) r2 [.register 9]
  have a9 := Within.allocate (regs := r1) (dst := 9) (h := H1)
    (expr := .bit (.flag hi) (.register 8)) (c := .bit hi h.length)
    (by simp [CellExpr.eval, Atom.eval, r1, Value.asPointer, Value.asFlag]) last
  have a8 := Within.allocate (regs := regs) (dst := 8) (h := h)
    (expr := .bit (.flag lo) .null) (c := .bit lo 0)
    (by simp [CellExpr.eval, Atom.eval, Value.asPointer, Value.asFlag]) a9
  exact a8.mono (by simp [CellExpr.args])

def itemBudget (W len : ℕ) : ℕ := 2 * RegisterMembership.budget (W + 2) len + 80

theorem item_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {xp cp : Ptr} {x : Bits W} {seen : List (Bits (W + 2))}
    (hx : BitsAt h xp x) (hc : WordsAt h cp seen) :
    ∃ out q, Extends h out ∧ Valid out ∧
      BitsAt out q (classBits (RegisterMembership.found (.cons true (.cons false x)) seen)
        (RegisterMembership.found (.cons true (.cons true x)) seen)) ∧
      Within code h (initialRegisters [.pointer xp, .pointer cp]) (code d.item) [.pointer q] out
        (itemBudget W seen.length) := by
  obtain ⟨hcmp, hmember, hitem, -⟩ := hm
  let H1 := h ++ [Cell.bit false xp]
  let H2 := H1 ++ [Cell.bit true h.length]
  let H3 := H2 ++ [Cell.bit true xp]
  let H4 := H3 ++ [Cell.bit true H2.length]
  obtain ⟨e1, v1, c1⟩ := allocate_fits hh (bit_fits (b := false) hx.allocated)
  obtain ⟨e2, v2, c2⟩ := allocate_fits v1 (bit_fits (b := true) (h := H1) (a := h.length)
    (by simp [H1]))
  obtain ⟨e3, v3, c3⟩ := allocate_fits v2 (bit_fits (b := true) (h := H2) (a := xp)
    (RegisterNetworkNodes.lt_of_ext (e1.trans e2) hx.allocated))
  obtain ⟨e4, v4, c4⟩ := allocate_fits v3 (bit_fits (b := true) (h := H3) (a := H2.length)
    (by simp [H3]))
  have e14 := e1.trans (e2.trans (e3.trans e4))
  have hL : BitsAt H4 H1.length (.cons true (.cons false x)) :=
    .cons ((e3.trans e4).lookup c2) (.cons ((e2.trans (e3.trans e4)).lookup c1) (hx.mono e14))
  have hR : BitsAt H4 H3.length (.cons true (.cons true x)) :=
    .cons c4 (.cons (e4.lookup c3) (hx.mono e14))
  have hc4 := hc.mono e14
  have mL := RegisterMembership.compiled code d.member d.cmp hmember hcmp hL hc4
  have mR := RegisterMembership.compiled code d.member d.cmp hmember hcmp hR hc4
  let fL := RegisterMembership.found (.cons true (.cons false x)) seen
  let fR := RegisterMembership.found (.cons true (.cons true x)) seen
  let r0 := initialRegisters [Value.pointer xp, .pointer cp]
  let r1 := Function.update r0 2 (.pointer h.length)
  let r2 := Function.update r1 3 (.pointer H1.length)
  let r3 := Function.update r2 4 (.pointer H2.length)
  let r4 := Function.update r3 5 (.pointer H3.length)
  let r5 := bindResults r4 [6] [.flag fL]
  let r6 := bindResults r5 [7] [.flag fR]
  have tree : ∃ out q, Extends H4 out ∧ Valid out ∧ BitsAt out q (classBits fL fR) ∧
      Within code H4 r6 (.branch (.register 6)
        (.branch (.register 7) (leaf false true) (leaf true false))
        (.branch (.register 7) (leaf false false) (leaf false true))) [.pointer q] out 25 := by
    have g6 : r6 6 = .flag fL := by simp [r6, r5, bindResults]
    have g7 : r6 7 = .flag fR := by simp [r6, bindResults]
    clear_value fL fR
    cases fL <;> cases fR
    · obtain ⟨out, q, e, v, hq, run⟩ := leaf_within code v4 r6 false true
      exact ⟨out, q, e, v, hq, (RegisterNetworkTable.branch_reg g6
        (RegisterNetworkTable.branch_reg g7 run)).mono (by omega)⟩
    · obtain ⟨out, q, e, v, hq, run⟩ := leaf_within code v4 r6 false false
      exact ⟨out, q, e, v, hq, (RegisterNetworkTable.branch_reg g6
        (RegisterNetworkTable.branch_reg g7 run)).mono (by omega)⟩
    · obtain ⟨out, q, e, v, hq, run⟩ := leaf_within code v4 r6 true false
      exact ⟨out, q, e, v, hq, (RegisterNetworkTable.branch_reg g6
        (RegisterNetworkTable.branch_reg g7 run)).mono (by omega)⟩
    · obtain ⟨out, q, e, v, hq, run⟩ := leaf_within code v4 r6 false true
      exact ⟨out, q, e, v, hq, (RegisterNetworkTable.branch_reg g6
        (RegisterNetworkTable.branch_reg g7 run)).mono (by omega)⟩
  obtain ⟨out, q, e5, v5, hq, treeRun⟩ := tree
  refine ⟨out, q, e14.trans e5, v5, hq, ?_⟩
  have aR : values r5 [.register 5, .register 1] = [.pointer H3.length, .pointer cp] := by
    simp [values, Atom.eval, r5, r4, r3, r2, r1, r0, bindResults, initialRegisters]
  have cR := Within.call (procedure := d.member) (regs := r5)
    (arguments := [.register 5, .register 1]) (results := [7])
    (by simpa only [aR] using mR) treeRun
  have aL : values r4 [.register 3, .register 1] = [.pointer H1.length, .pointer cp] := by
    simp [values, Atom.eval, r4, r3, r2, r1, r0, initialRegisters]
  have cL := Within.call (procedure := d.member) (regs := r4)
    (arguments := [.register 3, .register 1]) (results := [6])
    (by simpa only [aL] using mL) cR
  have a5 := Within.allocate (regs := r3) (dst := 5) (h := H3)
    (expr := .bit (.flag true) (.register 4)) (c := .bit true H2.length)
    (by simp [CellExpr.eval, Atom.eval, r3, Value.asPointer, Value.asFlag]) cL
  have a4 := Within.allocate (regs := r2) (dst := 4) (h := H2)
    (expr := .bit (.flag true) (.register 0)) (c := .bit true xp)
    (by simp [CellExpr.eval, Atom.eval, r2, r1, r0, initialRegisters, Value.asPointer,
      Value.asFlag]) a5
  have a3 := Within.allocate (regs := r1) (dst := 3) (h := H1)
    (expr := .bit (.flag true) (.register 2)) (c := .bit true h.length)
    (by simp [CellExpr.eval, Atom.eval, r1, Value.asPointer, Value.asFlag]) a4
  have a2 := Within.allocate (regs := r0) (dst := 2) (h := h)
    (expr := .bit (.flag false) (.register 0)) (c := .bit false xp)
    (by simp [CellExpr.eval, Atom.eval, r0, initialRegisters, Value.asPointer, Value.asFlag]) a3
  rw [hitem]
  have hb : RegisterMembership.budget (W + 1 + 1) seen.length =
      RegisterMembership.budget (W + 2) seen.length := rfl
  exact a2.mono (by simp [itemBudget, CellExpr.args]; omega)

/-! ## The readback -/

def budget (W n len : ℕ) : ℕ := (itemBudget W len + 35) * n + 13

theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {W n : ℕ} (hn : n < 2 ^ W) {h : Heap} (hh : Valid h) {vp cp : Ptr}
    {seen : List (Bits (W + 2))} (X : Finset (Node (Fin n)))
    (hseen : seen.toFinset = X.image (nodeWord W))
    (hv : WordsAt h vp (rangeWords W n)) (hc : WordsAt h cp seen) :
    ∃ out zp, Extends h out ∧ Valid out ∧
      WordsAt out zp ((List.finRange n).map fun v =>
        classWord (DoubleCover.rounded (leftCover (MaxFlowPreprocessing.membership X))
          (rightCover (MaxFlowPreprocessing.membership X)) v)) ∧
      Within code h (initialRegisters [.pointer vp, .pointer cp]) (code d.self) [.pointer zp] out
        (budget W n seen.length) := by
  have hvl : ListRep (fun h p (v : Fin n) => BitsAt h p (word W v.val)) h vp (List.finRange n) :=
    RegisterNetworkNodes.listRep_map.mp hv
  obtain ⟨out, q, e, v, hq, run⟩ := RegisterListMap.compiled_const code d.self d.item hm.2.2.2
    (fun h p (v : Fin n) => BitsAt h p (word W v.val))
    (fun h p (s : List (Bits (W + 2))) => WordsAt h p s)
    (fun h p (x : Bits 2) => BitsAt h p x)
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    (fun _ hx => hx.allocated)
    (fun s v => classBits (RegisterMembership.found (nodeWord W (Sum.inr (false, v))) s)
      (RegisterMembership.found (nodeWord W (Sum.inr (true, v))) s))
    (itemBudget W seen.length) hh hvl hc
    (fun hv' _ _ _ hx hc' => item_compiled code d hm hv' hx hc')
  refine ⟨out, q, e, v, ?_, by simpa [budget] using run⟩
  have heq : (List.finRange n).map (fun v => classBits
      (RegisterMembership.found (nodeWord W (Sum.inr (false, v))) seen)
      (RegisterMembership.found (nodeWord W (Sum.inr (true, v))) seen)) =
      (List.finRange n).map fun v =>
        classWord (DoubleCover.rounded (leftCover (MaxFlowPreprocessing.membership X))
          (rightCover (MaxFlowPreprocessing.membership X)) v) := by
    apply List.map_congr_left
    intro v _
    rw [found_nodeWord hn hseen, found_nodeWord hn hseen]
    exact classBits_eq X v
  rw [← heq]
  exact hq

end WeightedMIS.RegisterCutReadback
