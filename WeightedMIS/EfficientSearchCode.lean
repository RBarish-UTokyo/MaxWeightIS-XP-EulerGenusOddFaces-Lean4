module

public import WeightedMIS.RegisterMachine

/-!
# Closed finite register code for sparse search

This file contains command syntax only: no host-language graph operation,
natural-number cost arithmetic, or unbounded register index occurs in any
procedure body. The procedure indices are linked by a finite code table.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.RegisterCode

open WeightedMIS.RegisterMachine

def r (n : Fin 16) : Atom := .register n

def onlyPair {p : ℕ} (body : Command p) : Cases (Command p) :=
  ⟨.fail, .fail, .fail, .fail, .fail, body⟩

def listCases {p : ℕ} (empty nonempty : Command p) : Cases (Command p) :=
  ⟨empty, .fail, nonempty, .fail, .fail, .fail⟩

/-- Args: source, old reverse path, arc, target. Returns new candidate. -/
def extendBody {p : ℕ} : Command p :=
  .allocate 4 (.pair (r 0) (r 2))
    (.allocate 5 (.cons (r 4) (r 1))
      (.allocate 6 (.pair (r 3) (r 5)) (.ret [r 6])))

/-- Args: pair pointer. Returns its two fields. -/
def readPairBody {p : ℕ} : Command p :=
  .load (r 0) 1 2 3 (onlyPair (.ret [r 1, r 2]))

/-- Args: key, dictionary. Returns the empty-list flag. -/
def lookupEmptyBody {p : ℕ} (lookup : Fin p) : Command p :=
  .call lookup [r 0, r 1] [2]
    (.load (r 2) 3 4 5 (listCases (.ret [.flag true]) (.ret [.flag false])))

/-- Args: vertex, path, distance, arc, queue. Returns queue and carry. -/
def pushBody {p : ℕ} (add extend insert : Fin p) : Command p :=
  .load (r 3) 5 6 7 (onlyPair
    (.load (r 6) 8 9 7 (onlyPair
      (.call add [r 2, r 8, .flag false] [10, 11]
        (.call extend [r 0, r 1, r 3, r 5] [12]
          (.call insert [r 10, r 12, r 4] [13] (.ret [r 13, r 11])))))))

/-- Args: vertex, path, distance, outgoing-list, queue. Returns queue and carry. -/
def relaxBody {p : ℕ} (push self : Fin p) : Command p :=
  .load (r 3) 5 6 7 (listCases (.ret [r 4, .flag false])
    (.call push [r 0, r 1, r 2, r 5, r 4] [8, 9]
      (.call self [r 0, r 1, r 2, r 6, r 8] [10, 11]
        (.branch (r 9) (.ret [r 10, .flag true]) (.ret [r 10, r 11])))))

/-- Args: graph, vertex, path, distance, queue, settled. Returns both maps and carry. -/
def freshBody {p : ℕ} (insert lookup relax : Fin p) : Command p :=
  .allocate 6 (.pair (r 3) (r 2))
    (.call insert [r 1, r 6, r 5] [7]
      (.call lookup [r 1, r 0] [8]
        (.call relax [r 1, r 2, r 3, r 8, r 4] [9, 10]
          (.ret [r 9, r 7, r 10]))))

def searchTail {p : ℕ} (self : Fin p) (queue settled : Atom) : Command p :=
  .call self [r 0, queue, settled] [13, 14, 15] (.ret [r 13, r 14, r 15])

def freshSearchBody {p : ℕ} (fresh self : Fin p) : Command p :=
  .call fresh [r 0, r 7, r 8, r 4, r 6, r 2] [10, 11, 12]
    (.branch (r 12) (.ret [.flag true, r 10, r 11]) (searchTail self (r 10) (r 11)))

def foundSearchBody {p : ℕ} (read lookupEmpty fresh self : Fin p) : Command p :=
  .call read [r 5] [7, 8]
    (.call lookupEmpty [r 7, r 2] [9]
      (.branch (r 9) (freshSearchBody fresh self) (searchTail self (r 6) (r 2))))

/-- Args: graph, queue, settled. Returns overflow flag, queue, settled. -/
def searchBody {p : ℕ} (pop read lookupEmpty fresh self : Fin p) : Command p :=
  .call pop [r 1] [3, 4, 5, 6]
    (.branch (r 3) (foundSearchBody read lookupEmpty fresh self)
      (.ret [.flag false, r 1, r 2]))

/-- Args: graph, source word, zero cost word. Returns overflow, queue, settled. -/
def solveBody {p : ℕ} (insert search : Fin p) : Command p :=
  .allocate 3 (.pair (r 1) .null)
    (.call insert [r 2, r 3, .null] [4]
      (.call search [r 0, r 4, .null] [5, 6, 7] (.ret [r 5, r 6, r 7])))

end WeightedMIS.EfficientSearch.RegisterCode
