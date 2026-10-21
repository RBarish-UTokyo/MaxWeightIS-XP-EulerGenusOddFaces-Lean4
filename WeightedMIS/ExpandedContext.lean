module

public import WeightedMIS.ExpandedRecords
public import WeightedMIS.RegisterHorner
public import WeightedMIS.ScalarNodeCodec

/-! # Stored working-node context and the executable candidate calculation -/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.PointerMemory WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer

structure ArithmeticWords (n : ℕ) where
  base : Bits n
  states : Bits n
  block : Bits n
  one : Bits n
  two : Bits n

def ArithmeticAt {n : ℕ} (h : Heap) (p : Ptr) (a : ArithmeticWords n) : Prop :=
  ∃ base t1 states t2 block t3 one t4 two zero,
    h[p]? = some (.pair base t1) ∧ h[t1]? = some (.pair states t2) ∧
    h[t2]? = some (.pair block t3) ∧ h[t3]? = some (.pair one t4) ∧
    h[t4]? = some (.pair two zero) ∧ BitsAt h base a.base ∧ BitsAt h states a.states ∧
    BitsAt h block a.block ∧ BitsAt h one a.one ∧ BitsAt h two a.two ∧ BitsAt h zero (Bits.zero n)

structure WorkContext (n : ℕ) where
  source : Bits n
  anchor : Bits n
  current : Bits n
  parity : Bits n
  digits : List (Bits n)
  arithmetic : ArithmeticWords n

def ContextAt {n : ℕ} (h : Heap) (p : Ptr) (c : WorkContext n) : Prop :=
  ∃ work arithmetic source t1 anchor t2 current t3 parity digits,
    h[p]? = some (.pair work arithmetic) ∧ h[work]? = some (.pair source t1) ∧
    h[t1]? = some (.pair anchor t2) ∧ h[t2]? = some (.pair current t3) ∧
    h[t3]? = some (.pair parity digits) ∧ BitsAt h source c.source ∧
    BitsAt h anchor c.anchor ∧ BitsAt h current c.current ∧ BitsAt h parity c.parity ∧
    WordsAt h digits c.digits ∧ ArithmeticAt h arithmetic c.arithmetic

theorem ArithmeticAt.mono {n : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr}
    {a : ArithmeticWords n} (ha : ArithmeticAt h p a) : ArithmeticAt h' p a := by
  obtain ⟨b,t1,s,t2,k,t3,o,t4,t,z,h0,h1,h2,h3,h4,hb,hs,hk,ho,ht,hz⟩ := ha
  exact ⟨b,t1,s,t2,k,t3,o,t4,t,z,he.lookup h0,he.lookup h1,he.lookup h2,he.lookup h3,he.lookup h4,
    hb.mono he,hs.mono he,hk.mono he,ho.mono he,ht.mono he,hz.mono he⟩

theorem ContextAt.mono {n : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr}
    {c : WorkContext n} (hc : ContextAt h p c) : ContextAt h' p c := by
  obtain ⟨w,ar,s,t1,a,t2,v,t3,pb,ds,h0,h1,h2,h3,h4,hs,ha,hv,hp,hd,har⟩ := hc
  exact ⟨w,ar,s,t1,a,t2,v,t3,pb,ds,he.lookup h0,he.lookup h1,he.lookup h2,he.lookup h3,he.lookup h4,
    hs.mono he,ha.mono he,hv.mono he,hp.mono he,hd.mono he,har.mono he⟩

/-- The local word algorithm emits either one actual arc or none. -/
def candidate {Row : Type*} {n cbits : ℕ} (key : Walks.State Row → Bits n)
    (ctx : WorkContext n) (a : CompiledTemplates.Template Row (ArcMetadata n cbits)) :
    List (RawArc Ptr n cbits) :=
  if (Bits.compare (key a.source) ctx.current).1 = .eq then
    match updateWords ctx.arithmetic.base ctx.digits a.metadata.deltas with
    | none => []
    | some updated =>
        let box := RegisterHorner.encodeWords ctx.arithmetic.base updated
        let parity := if a.metadata.parity then (Bits.subtract ctx.arithmetic.one ctx.parity).1 else ctx.parity
        let node : ScalarNodeCodec.Words n := ⟨false, ctx.anchor, key a.target, box, parity⟩
        [(ctx.source, ⟨ScalarNodeCodec.encodeWords ctx.arithmetic.states ctx.arithmetic.block
          ctx.arithmetic.one ctx.arithmetic.two node, a.metadata.weight, a.metadata.label⟩)]
  else []

end WeightedMIS.ExpandedWords
