module

public import WeightedMIS.RegisterGraphArcs
public import WeightedMIS.RegisterAdjacencyScan
public import WeightedMIS.RegisterListMap

/-!
# Endpoint pairs of a stored ribbon table

A list map over the edge records reads the two shared endpoint words of each
record and allocates one `pair` cell referring to them. On the table of a
ribbon the result is the stored endpoint list `GraphReachEncoded.edgeWords`
in the representation `RegisterAdjacencyScan.EdgeWordsAt` used by the
compiled preprocessing.
-/

@[expose] public section

namespace WeightedMIS.RegisterEdgePairs

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable WeightedMIS.RegisterFlagKeys
open WeightedMIS.RegisterAdjacencyScan

variable {p : ℕ}

/-- Argument 0 = record; the result is `pair leftWord rightWord`. -/
def pairItemBody : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 3) 4 5 15 { CompiledTrie.failCases with
      pair := .load (.register 5) 6 7 15 { CompiledTrie.failCases with
        pair := .allocate 8 (.pair (.register 4) (.register 6)) (.ret [.register 8]) } } }

structure Procedures (p : ℕ) where
  pairs : Fin p
  item : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.pairs = RegisterListMap.body ids.pairs ids.item ∧ code ids.item = pairItemBody

def pairsBudget (t : ℕ) : ℕ := 95 * t + 13

theorem edgeAt_allocated {W : ℕ} {h : Heap} {ptr : Ptr} {e : Bits W × Bits W}
    (he : EdgeAt h ptr e) : ptr < h.length := by
  obtain ⟨lp, rp, c, -⟩ := he
  exact (List.getElem?_eq_some_iff.mp c).1

theorem item_compiled (code : Code p) (item : Fin p) (hitem : code item = pairItemBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {rp dp : Ptr} {r : EdgeRec W} (hr : EdgeRecAt h rp r) :
    ∃ out q, Extends h out ∧ Valid out ∧ EdgeAt out q (r.left, r.right) ∧
      Within code h (initialRegisters [.pointer rp, .pointer dp]) (code item) [.pointer q] out
        60 := by
  obtain ⟨kp, a, lp, b, rp', c, c0, ca, cb, hl, hrt⟩ := RegisterGraphArcs.edgeRec_fields hr
  obtain ⟨e1, v1, c1⟩ := alloc_pair hh hl.allocated hrt.allocated
  refine ⟨_, h.length, e1, v1, ⟨lp, rp', c1, hl.mono e1, hrt.mono e1⟩, ?_⟩
  rw [hitem]
  refine (Within.load (pointer := rp) (c := Cell.pair kp a) (by reg_simp) c0
    (Within.load (pointer := a) (c := Cell.pair lp b) (by reg_simp) ca
    (Within.load (pointer := b) (c := Cell.pair rp' c) (by reg_simp) cb
    (Within.allocate (c := Cell.pair lp rp') (by reg_simp)
    (ret_values (by reg_simp) le_rfl))))).mono ?_
  simp [CellExpr.args]

/-- The endpoint pairs of a stored record table. -/
theorem pairs_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp : Ptr} {T : List (EdgeRec W)}
    (hT : RecordsAt h tp T) :
    ∃ out q, Extends h out ∧ Valid out ∧ EdgeWordsAt out q (RegisterGraphArcs.edgePairs T) ∧
      Within code h (initialRegisters [.pointer tp, .pointer 0]) (code ids.pairs) [.pointer q]
        out (pairsBudget T.length) := by
  obtain ⟨out, q, he, ho, hq, hw⟩ := RegisterListMap.compiled_const code ids.pairs ids.item hm.1
    EdgeRecAt (fun _ _ (_ : Unit) => True) (fun h p (e : Bits W × Bits W) => EdgeAt h p e)
    (fun he _ _ hr => hr.mono he) (fun _ _ _ _ => trivial) (fun he _ _ hx => hx.mono he)
    (fun _ hx => edgeAt_allocated hx) (fun _ r => (r.left, r.right)) 60 (data := ())
    (dataPtr := 0) hh hT trivial
    (fun hv _ _ _ hx _ => item_compiled code ids.item hm.2 hv hx)
  exact ⟨out, q, he, ho, hq, hw.mono (by simp [pairsBudget])⟩

/-- On the table of a ribbon: the stored endpoint words of its edges. -/
theorem edgeWords_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right)
    {h : Heap} (hh : Valid h) {tp : Ptr} (hT : RecordsAt h tp (encodeRibbon W R)) :
    ∃ out q, Extends h out ∧ Valid out ∧
      EdgeWordsAt out q (GraphReachEncoded.edgeWords W left right) ∧
      Within code h (initialRegisters [.pointer tp, .pointer 0]) (code ids.pairs) [.pointer q]
        out (pairsBudget m) := by
  obtain ⟨out, q, he, ho, hq, hw⟩ := pairs_compiled ids code hm hh hT
  rw [RegisterGraphArcs.edgePairs_encode] at hq
  refine ⟨out, q, he, ho, hq, ?_⟩
  simpa [encodeRibbon] using hw

end WeightedMIS.RegisterEdgePairs
