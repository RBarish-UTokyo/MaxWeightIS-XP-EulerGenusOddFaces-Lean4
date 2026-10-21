module

public import WeightedMIS.RegisterMachine

/-!
# Closed register programs for trie operations

The only parameters are constant procedure identifiers. None of these finite
bodies accepts a host-language function. Lookup and insertion return their
result pointer; extraction returns found/key/payload/new-root, with the old
root retained on an empty result.
-/

@[expose] public section

namespace WeightedMIS.CompiledTrie

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

def failCases {p : ℕ} : Cases (Command p) := ⟨.fail, .fail, .fail, .fail, .fail, .fail⟩

/-- Arguments 0=key, 1=root; result is the item-list pointer. -/
def lookupBody {p : ℕ} (self : Fin p) : Command p :=
  .load (.register 1) 2 3 4 {
    failCases with
    nil := .ret [.null]
    bucket := .ret [.register 2]
    fork := .load (.register 0) 5 6 7 {
      failCases with
      bit := .branch (.register 7)
        (.call self [.register 5, .register 3] [8] (.ret [.register 8]))
        (.call self [.register 5, .register 2] [8] (.ret [.register 8]))
    }
  }

def insertLeaf {p : ℕ} (items : Atom) : Command p :=
  .allocate 9 (.cons (.register 1) items)
    (.allocate 10 (.bucket (.register 9)) (.ret [.register 10]))

def insertBranch {p : ℕ} (self : Fin p) (left right : Atom) : Command p :=
  .branch (.register 7)
    (.call self [.register 6, .register 1, right] [9]
      (.allocate 10 (.fork left (.register 9)) (.ret [.register 10])))
    (.call self [.register 6, .register 1, left] [9]
      (.allocate 10 (.fork (.register 9) right) (.ret [.register 10])))

/-- Arguments 0=key, 1=payload, 2=root; result is the inserted root. -/
def insertBody {p : ℕ} (self : Fin p) : Command p :=
  .load (.register 2) 3 4 5 {
    failCases with
    nil := .load (.register 0) 6 8 7 {
      failCases with
      nil := insertLeaf .null
      bit := insertBranch self .null .null
    }
    bucket := .load (.register 0) 6 8 7 {
      failCases with
      nil := insertLeaf (.register 3)
    }
    fork := .load (.register 0) 6 8 7 {
      failCases with
      bit := insertBranch self (.register 3) (.register 4)
    }
  }

/-- Construct the canonical join in register 11. Scratch registers 8,9,10
must not occur in the two root atoms or in continuation inputs. -/
def joinBody {p : ℕ} (left right : Atom) (next : Command p) : Command p :=
  let nonempty := Command.allocate 11 (.fork left right) next
  let rightCases : Cases (Command p) := {
    nil := .copy 11 .null next
    bit := nonempty
    cons := nonempty
    fork := nonempty
    bucket := nonempty
    pair := nonempty
  }
  .load left 8 9 10 {
    nil := .load right 8 9 10 rightCases
    bit := nonempty
    cons := nonempty
    fork := nonempty
    bucket := nonempty
    pair := nonempty
  }

def finishPop {p : ℕ} (b : Bool) (left right : Atom) : Command p :=
  joinBody left right
    (.allocate 14 (.bit (.flag b) (.register 5))
      (.ret [.flag true, .register 14, .register 6, .register 11]))

def emptyPop {p : ℕ} : Command p :=
  .ret [.flag false, .null, .null, .register 0]

/-- Test the shared list tail, returning a canonical bucket or the empty root. -/
def bucketTailBody {p : ℕ} : Command p :=
  let allocated := Command.allocate 10 (.bucket (.register 5))
    (.ret [.flag true, .null, .register 4, .register 10])
  .load (.register 5) 7 8 9 {
    nil := .ret [.flag true, .null, .register 4, .null]
    bit := allocated
    cons := allocated
    fork := allocated
    bucket := allocated
    pair := allocated
  }

/-- Argument 0=root. Empty result returns false,0,0,old-root. Successful
result returns true,new-key,payload,new-root. -/
def popBody {p : ℕ} (self : Fin p) : Command p :=
  .load (.register 0) 1 2 3 {
    failCases with
    nil := emptyPop
    bucket := .load (.register 1) 4 5 6 {
      failCases with
      nil := emptyPop
      cons := bucketTailBody
    }
    fork := .call self [.register 1] [4, 5, 6, 7]
      (.branch (.register 4)
        (finishPop false (.register 7) (.register 2))
        (.call self [.register 2] [4, 5, 6, 7]
          (.branch (.register 4) (finishPop true (.register 1) (.register 7)) emptyPop)))
  }

end WeightedMIS.CompiledTrie
