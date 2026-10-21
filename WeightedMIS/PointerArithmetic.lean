module

public import WeightedMIS.PointerRepresentations
public import WeightedMIS.EfficientSearchArithmetic
public import WeightedMIS.PointerLookup

/-!
# Binary addition in the pointer machine

The program loads the two input cells, recursively adds the tails, executes
seven Boolean gates for the full adder, and allocates one output bit. The
returned word is related to the binary arithmetic specification by its actual
heap representation. No unbounded integer addition is a machine primitive.
-/

@[expose] public section

namespace WeightedMIS.PointerMemory

open WeightedMIS.EfficientSearch

/-- One full adder uses two XOR, three AND, and two OR gates. -/
def addCarryPointer : ℕ → Ptr → Ptr → Bool → Program (Ptr × Bool)
  | 0, ap, bp, carry, h =>
    let a := Program.load ap h
    let b := Program.load bp h
    ⟨(0, carry), h, .control :: (a.trace ++ b.trace)⟩
  | n + 1, ap, bp, carry, h =>
    let a := Program.load ap h
    let b := Program.load bp h
    let before := .control :: (a.trace ++ b.trace)
    match a.value, b.value with
    | some (.bit av atail), some (.bit bv btail) =>
      let tail := addCarryPointer n atail btail carry h
      let head := Bits.fullAdd av bv tail.value.2
      let out := Program.allocate (.bit head.1 tail.value.1) tail.heap
      ⟨(out.value, head.2), out.heap,
        before ++ tail.trace ++ List.replicate 7 .control ++ out.trace⟩
    | _, _ => ⟨(0, carry), h, before⟩

theorem controls_bound (n bound : ℕ) :
    TraceBound (List.replicate n .control) bound := by
  intro e he p hp
  have : e = .control := List.eq_of_mem_replicate he
  subst e
  simp [Event.references] at hp

theorem addCarryPointer_refines {n : ℕ} {h : Heap} (hh : Valid h)
    {ap bp : Ptr} {a b : Bits n} (ha : BitsAt h ap a) (hb : BitsAt h bp b)
    (carry : Bool) :
    SafeRun h (addCarryPointer n ap bp carry h) ∧
      BitsAt (addCarryPointer n ap bp carry h).heap
        (addCarryPointer n ap bp carry h).value.1 (Bits.addCarry a b carry).1 ∧
      (addCarryPointer n ap bp carry h).value.2 = (Bits.addCarry a b carry).2.1 ∧
      (addCarryPointer n ap bp carry h).trace.length = 11 * n + 3 := by
  induction a generalizing h ap bp with
  | nil =>
    cases b
    have hbnd : TraceBound (.control ::
        ((Program.load ap h).trace ++ (Program.load bp h).trace)) h.length := by
      intro e he p hp
      rcases List.mem_cons.mp he with rfl | he
      · simp [Event.references] at hp
      · exact traceBound_append (safe_load h hh ap ha.allocated).2.2.1
          (safe_load h hh bp hb.allocated).2.2.1 e he p hp
    refine ⟨?_, .nil hh.1, rfl, rfl⟩
    exact safe_prefix (safe_pure h hh (0, carry)) _ hbnd
  | @cons n av as ih =>
    cases b with
    | cons bv bs =>
      cases ha with
      | @cons _ atail _ _ _ hac hat =>
        cases hb with
        | @cons _ btail _ _ _ hbc hbt =>
          obtain ⟨hs, ht, hv, hl⟩ := ih hh hat hbt
          let tail := addCarryPointer n atail btail carry h
          let head := Bits.fullAdd av bv tail.value.2
          have ho := allocate_bit hs.2.1 head.1 ht
          have hsout := safe_prefix ho.1 (List.replicate 7 .control)
            (controls_bound 7 tail.heap.length)
          have hjoin := safe_join hs (safe_change_value hsout
            ((Program.allocate (.bit head.1 tail.value.1) tail.heap).value, head.2))
          have hbefore : TraceBound (.control ::
              ((Program.load ap h).trace ++ (Program.load bp h).trace)) h.length := by
            intro e he p hp
            rcases List.mem_cons.mp he with rfl | he
            · simp [Event.references] at hp
            · exact traceBound_append (safe_load h hh ap (BitsAt.allocated (.cons hac hat))).2.2.1
                (safe_load h hh bp (BitsAt.allocated (.cons hbc hbt))).2.2.1 e he p hp
          have hall := safe_prefix hjoin _ hbefore
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [addCarryPointer, Program.load, hac, hbc, tail, head,
              List.append_assoc] using hall
          · simpa [addCarryPointer, Program.load, hac, hbc, tail, head,
              Bits.addCarry, hv] using ho.2
          · simp [addCarryPointer, Program.load, hac, hbc, Bits.addCarry, hv]
          · simp only [addCarryPointer, Program.load, hac, hbc, Program.allocate,
              List.length_append, List.length_cons, List.length_nil, List.length_replicate]
            omega

def addPointer (n : ℕ) (ap bp : Ptr) : Program (Ptr × Bool) :=
  addCarryPointer n ap bp false

theorem addPointer_refines {n : ℕ} {h : Heap} (hh : Valid h)
    {ap bp : Ptr} {a b : Bits n} (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    SafeRun h (addPointer n ap bp h) ∧
      BitsAt (addPointer n ap bp h).heap
        (addPointer n ap bp h).value.1 (Bits.add a b).1 ∧
      (addPointer n ap bp h).value.2 = (Bits.add a b).2.1 ∧
      (addPointer n ap bp h).trace.length = 11 * n + 3 :=
  addCarryPointer_refines hh ha hb false

theorem addPointer_bitCost {n : ℕ} {h : Heap} (hh : Valid h)
    {ap bp : Ptr} {a b : Bits n} (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    bitCost (addPointer n ap bp h).trace ≤
      (11 * n + 3) * (4 + 3 * (h.length + (11 * n + 3)).size) := by
  obtain ⟨hs, _, _, hl⟩ := addPointer_refines hh ha hb
  simpa only [hl] using safe_bitCost_le hs

end WeightedMIS.PointerMemory
