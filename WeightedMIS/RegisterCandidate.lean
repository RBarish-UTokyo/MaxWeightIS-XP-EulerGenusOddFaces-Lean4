module

public import WeightedMIS.ExpandedContext
public import WeightedMIS.RegisterCoordinates
public import WeightedMIS.RegisterPairReads
public import WeightedMIS.RegisterArcEmitter

/-! # Finite code for one local expanded-graph move candidate -/

@[expose] public section

namespace WeightedMIS.RegisterCandidate

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.RegisterPairReads

structure Procedures (p : ℕ) where
  compare : Fin p
  coordinates : Fin p
  horner : Fin p
  subtract : Fin p
  encode : Fin p
  emit : Fin p

def skip {p : ℕ} : Command p := .ret [.register 2]

def initialReads : List Fields := [(1,3,4),(0,5,6),(6,7,8),(3,9,10),(10,11,12),(12,13,14)]

def matchedReads : List Fields := [(14,13,14),(8,5,6),(4,0,3),(3,1,3),(3,4,3),(3,8,3),(3,10,12)]

/-- Ready registers are 9=source,11=anchor,7=target,14=box,13=parity,
1=state-count,4=block-size,8=one,10=two,3=shared cost/label,2=tail. -/
def encodeAndEmit {p : ℕ} (ids : Procedures p) : Command p :=
  .call ids.encode [.flag false,.register 11,.register 7,.register 14,.register 13,
      .register 1,.register 4,.register 8,.register 10] [0]
    (.call ids.emit [.register 9,.register 0,.register 3,.register 2] [1] (.ret [.register 1]))

def updateParity {p : ℕ} (ids : Procedures p) : Command p :=
  .load (.register 6) 3 5 15 {CompiledTrie.failCases with
    bit := .branch (.register 15)
      (.call ids.subtract [.register 8,.register 13] [13,5] (encodeAndEmit ids))
      (encodeAndEmit ids)}

def afterCoordinates {p : ℕ} (ids : Procedures p) : Command p :=
  .branch (.register 5)
    (.call ids.horner [.register 14,.register 0,.register 12] [14] (updateParity ids)) skip

def matched {p : ℕ} (ids : Procedures p) : Command p :=
  readPairs matchedReads
    (.call ids.coordinates [.register 0,.register 14,.register 5] [5,14] (afterCoordinates ids))

/-- Arguments: stored template, stored working context, raw-arc accumulator. -/
def candidateBody {p : ℕ} (ids : Procedures p) : Command p :=
  readPairs initialReads
    (.call ids.compare [.register 5,.register 13] [15,6]
      (.branch (.register 6) (matched ids) skip))

end WeightedMIS.RegisterCandidate
