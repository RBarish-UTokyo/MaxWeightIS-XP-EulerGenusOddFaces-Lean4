module

public import WeightedMIS.PointerInsert
public import WeightedMIS.PointerPop

/-!
# Data-directed evaluation, with no runtime natural-number fuel

The evaluation rules inspect stored tags. Widths in the total Lean wrappers
are ghost termination arguments: these judgments have no width or fuel input.
Each successful wrapper execution has such a derivation. They provide the
call structure needed for an explicit stack implementation.
-/

@[expose] public section

namespace WeightedMIS.PointerMemory

open WeightedMIS.EfficientSearch

def readBefore (h : Heap) (p : Ptr) : List Event :=
  .control :: (Program.load p h).trace

def readTwoBefore (h : Heap) (p q : Ptr) : List Event :=
  .control :: ((Program.load p h).trace ++ (Program.load q h).trace)

inductive LookupEval : Heap → Ptr → Ptr → Run (Option Ptr) → Prop
  | empty {h : Heap} {key tree : Ptr} (root : h[tree]? = some .nil) :
      LookupEval h key tree ⟨some 0, h, readBefore h tree⟩
  | bucket {h : Heap} {key tree items : Ptr} (root : h[tree]? = some (.bucket items)) :
      LookupEval h key tree ⟨some items, h, readBefore h tree⟩
  | fork {h : Heap} {key tree left right tail : Ptr} {b : Bool} {r : Run (Option Ptr)}
      (root : h[tree]? = some (.fork left right))
      (keyCell : h[key]? = some (.bit b tail))
      (child : LookupEval h tail (if b then right else left) r) :
      LookupEval h key tree (withEvents (readTwoBefore h tree key) r)

inductive InsertEval : Heap → Ptr → Ptr → Ptr → Run (Option Ptr) → Prop
  | emptyLeaf {h : Heap} {key a tree : Ptr}
      (root : h[tree]? = some .nil) (keyCell : h[key]? = some .nil) :
      InsertEval h key a tree (withEvents (readTwoBefore h tree key) (leafInsert a 0 h))
  | bucketLeaf {h : Heap} {key a tree items : Ptr}
      (root : h[tree]? = some (.bucket items)) (keyCell : h[key]? = some .nil) :
      InsertEval h key a tree (withEvents (readTwoBefore h tree key) (leafInsert a items h))
  | emptyBranch {h : Heap} {key a tree tail : Ptr} {b : Bool} {r : Run (Option Ptr)}
      (root : h[tree]? = some .nil) (keyCell : h[key]? = some (.bit b tail))
      (child : InsertEval h tail a 0 r) :
      InsertEval h key a tree (withEvents (readTwoBefore h tree key) (forkAfter b 0 r))
  | fork {h : Heap} {key a tree tail left right : Ptr} {b : Bool} {r : Run (Option Ptr)}
      (root : h[tree]? = some (.fork left right)) (keyCell : h[key]? = some (.bit b tail))
      (child : InsertEval h tail a (if b then right else left) r) :
      InsertEval h key a tree (withEvents (readTwoBefore h tree key)
        (forkAfter b (if b then left else right) r))

inductive PopEval : Heap → Ptr → Run PopValue → Prop
  | empty {h : Heap} {tree : Ptr} (root : h[tree]? = some .nil) :
      PopEval h tree ⟨none, h, readBefore h tree⟩
  | emptyBucket {h : Heap} {tree items : Ptr}
      (root : h[tree]? = some (.bucket items)) (item : h[items]? = some .nil) :
      PopEval h tree ⟨none, h, readTwoBefore h tree items⟩
  | bucket {h : Heap} {tree items a tail : Ptr}
      (root : h[tree]? = some (.bucket items)) (item : h[items]? = some (.cons a tail)) :
      PopEval h tree (withEvents (readTwoBefore h tree items)
        ⟨some (0, a, (leafPointer tail h).value), (leafPointer tail h).heap,
          (leafPointer tail h).trace⟩)
  | left {h : Heap} {tree left right key a left' : Ptr} {lp : Run PopValue}
      (root : h[tree]? = some (.fork left right)) (child : PopEval h left lp)
      (found : lp.value = some (key, a, left')) :
      PopEval h tree (withEvents (readBefore h tree)
        (sequenceRuns lp (extendPop false right key a left' lp.heap)))
  | right {h : Heap} {tree left right key a right' : Ptr} {lp rp : Run PopValue}
      (root : h[tree]? = some (.fork left right)) (leftChild : PopEval h left lp)
      (noLeft : lp.value = none) (rightChild : PopEval lp.heap right rp)
      (found : rp.value = some (key, a, right')) :
      PopEval h tree (withEvents (readBefore h tree)
        (sequenceRuns (sequenceRuns lp rp) (extendPop true left key a right' rp.heap)))
  | noChildren {h : Heap} {tree left right : Ptr} {lp rp : Run PopValue}
      (root : h[tree]? = some (.fork left right)) (leftChild : PopEval h left lp)
      (noLeft : lp.value = none) (rightChild : PopEval lp.heap right rp)
      (noRight : rp.value = none) :
      PopEval h tree (withEvents (readBefore h tree)
        (sequenceRuns (sequenceRuns lp rp) (Program.pure none rp.heap)))

theorem lookupPointer_eval {n : ℕ} {h : Heap} {kp tp : Ptr}
    {key : Bits n} {tree : Radix Ptr n} (hk : BitsAt h kp key) (ht : TrieAt h tp tree) :
    LookupEval h kp tp (lookupPointer n kp tp h) := by
  induction key generalizing kp tp with
  | nil =>
    cases ht with
    | empty hc => simpa [lookupPointer, Program.load, hc, readBefore] using LookupEval.empty (key := kp) hc
    | bucket hc hl => simpa [lookupPointer, Program.load, hc, readBefore] using LookupEval.bucket (key := kp) hc
  | @cons n b key ih =>
    cases ht with
    | empty hc => simpa [lookupPointer, Program.load, hc, readBefore] using LookupEval.empty (key := kp) hc
    | @fork _ left right _ l r hc hl hr =>
      cases hk with
      | cons hkey htail =>
        have selected : TrieAt h (if b then right else left) (if b then r else l) := by
          cases b <;> assumption
        simpa [lookupPointer, Program.load, hc, hkey, withEvents, readTwoBefore, List.append_assoc] using
          LookupEval.fork hc hkey (ih htail selected)

theorem insertPointer_eval {n : ℕ} {h : Heap} (hh : Valid h) {kp a tp : Ptr}
    {key : Bits n} {tree : Radix Ptr n} (hk : BitsAt h kp key) (ht : TrieAt h tp tree) :
    InsertEval h kp a tp (insertPointer n kp a tp h) := by
  induction key generalizing kp tp with
  | nil =>
    cases hk with
    | nil hkey =>
      cases ht with
      | empty hc =>
        simpa [insertPointer, Program.load, hc, hkey, readTwoBefore, withEvents, List.append_assoc] using
          InsertEval.emptyLeaf (a := a) hc hkey
      | bucket hc hl =>
        simpa [insertPointer, Program.load, hc, hkey, readTwoBefore, withEvents, List.append_assoc] using
          InsertEval.bucketLeaf (a := a) hc hkey
  | @cons n b key ih =>
    cases hk with
    | cons hkey htail =>
      cases ht with
      | empty hc =>
        simpa [insertPointer, Program.load, hc, hkey, readTwoBefore, withEvents, List.append_assoc] using
          InsertEval.emptyBranch hc hkey (ih htail (TrieAt.empty (n := n) hh.1))
      | @fork _ left right _ l r hc hl hr =>
        have selected : TrieAt h (if b then right else left) (if b then r else l) := by
          cases b <;> assumption
        simpa [insertPointer, Program.load, hc, hkey, readTwoBefore, withEvents, List.append_assoc] using
          InsertEval.fork hc hkey (ih htail selected)

theorem popPointer_eval {n : ℕ} {h : Heap} (hh : Valid h) {tp : Ptr}
    {tree : Radix Ptr n} (ht : TrieAt h tp tree) : PopEval h tp (popPointer n tp h) := by
  induction tree generalizing h tp with
  | @empty n =>
    cases ht with
    | empty hc =>
      cases n <;> simpa [popPointer, Program.load, hc, readBefore] using PopEval.empty hc
  | bucket xs =>
    cases ht with
    | bucket hc hx =>
      cases hx with
      | nil hi => simpa [popPointer, Program.load, hc, hi, readTwoBefore] using PopEval.emptyBucket hc hi
      | cons hi htail =>
        simpa [popPointer, Program.load, hc, hi, readTwoBefore, withEvents, List.append_assoc] using
          PopEval.bucket hc hi
  | @fork n l r ihl ihr =>
    cases ht with
    | @fork _ left right _ _ _ hc hl hr =>
      have el := ihl hh hl
      have hls := (popPointer_refines hh hl).1
      cases hvl : (popPointer n left h).value with
      | some v =>
        obtain ⟨key, a, left'⟩ := v
        simpa [popPointer, Program.load, hc, hvl, readBefore, withEvents, sequenceRuns, List.append_assoc] using
          PopEval.left hc el hvl
      | none =>
        have er := ihr hls.2.1 (hr.mono hls.1)
        cases hvr : (popPointer n right (popPointer n left h).heap).value with
        | some v =>
          obtain ⟨key, a, right'⟩ := v
          simpa [popPointer, Program.load, hc, hvl, hvr, readBefore, withEvents, sequenceRuns, List.append_assoc] using
            PopEval.right hc el hvl er hvr
        | none =>
          simpa [popPointer, Program.load, Program.pure, hc, hvl, hvr, readBefore, withEvents,
              sequenceRuns, List.append_assoc] using PopEval.noChildren hc el hvl er hvr

end WeightedMIS.PointerMemory
