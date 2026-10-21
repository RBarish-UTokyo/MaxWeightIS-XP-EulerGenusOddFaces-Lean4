module

public import WeightedMIS.RegisterIncidenceRows

/-!
# Compiled rational incidence-kernel generators

The fixed entry procedure builds the stored incidence equations from vertex
and edge-endpoint words, builds the coordinate vectors, and runs the compiled
constraint-elimination loop. Its output rows are exactly the word-level
elimination result; under the uniform width `kernelWidth n m ≤ N` they denote,
in order, the rational generators `DeterministicKernel.initial left right`.
-/

@[expose] public section

namespace WeightedMIS.RegisterKernelGenerators

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open RegisterRationalCut (RowsAt)
open RegisterIncidenceRows (EdgeAt)

variable {p N W : ℕ}

/-- Arguments 0=vertex words, 1=edges, 2=zero, 3=one, 4=two; result is the generator list. -/
def body (incidence coords fold : Fin p) : Command p :=
  .call incidence [.register 0, .register 1, .register 2, .register 3, .register 4] [5]
    (.call coords [.register 1, .register 2, .register 3] [6]
      (.call fold [.register 5, .register 2, .register 6] [7] (.ret [.register 7])))

structure Procedures (p : ℕ) where
  elim : RegisterEliminateRows.Procedures p
  inc : RegisterIncidenceRows.Procedures p
  self : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p)
    (d : RegisterRationalProducts.Procedures p) : Prop where
  elim : ids.elim.Matches code d
  inc : ids.inc.Matches code
  self : code ids.self = body ids.inc.incidence ids.inc.coords ids.elim.fold

/-- Event bound for `n` vertices and `m` edges at word width `W` and rational width `N`. -/
def budget (W N n m : ℕ) : ℕ :=
  RegisterIncidenceRows.incidenceBudget W m n + RegisterIncidenceRows.coordsBudget m +
    RegisterEliminateRows.budget N m m n + 40

/-- The word-level reference result of the generator procedure. -/
def generatorsW (zero one two : BinaryRational.Word N) (verts : List (Bits W))
    (edges : List (Bits W × Bits W)) : List (List (BinaryRational.Word N)) :=
  RationalWordRows.eliminateRowsW zero
    (RegisterIncidenceRows.incidenceRowsW (zero, one, two) verts edges)
    (RationalWordRows.coordinateVectorsW zero one edges.length)

theorem compiled_words (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {vlp ep zp op tp : Ptr} {verts : List (Bits W)}
    {edges : List (Bits W × Bits W)} {zero one two : BinaryRational.Word N}
    (hvs : ListRep (fun heap ptr (w : Bits W) => BitsAt heap ptr w) h vlp verts)
    (hes : ListRep EdgeAt h ep edges) (hz : At h zp zero) (ho : At h op one) (ht : At h tp two) :
    ∃ out q, Extends h out ∧ Valid out ∧ RowsAt out q (generatorsW zero one two verts edges) ∧
      Within code h (initialRegisters [.pointer vlp, .pointer ep, .pointer zp, .pointer op,
        .pointer tp]) (code ids.self) [.pointer q] out
        (budget W N verts.length edges.length) := by
  obtain ⟨m1, rows, e1, v1, hrows, built⟩ :=
    RegisterIncidenceRows.incidence_compiled code ids.inc hcode.inc hh hvs hes hz ho ht
  obtain ⟨m2, coords, e2, v2, hcoords, coorded⟩ :=
    RegisterIncidenceRows.coords_compiled code ids.inc hcode.inc EdgeAt
      (fun ext _ _ hx => hx.mono ext) v1 (hes.mono e1 (fun _ _ h => h.mono e1))
      (hz.mono e1) (ho.mono e1)
  have e12 := e1.trans e2
  obtain ⟨out, q, e3, v3, hq, eliminated⟩ := RegisterEliminateRows.compiled code ids.elim d
    hcode.elim v2 (hrows.mono e2) (hz.mono e12) hcoords (m := edges.length)
    (by
      intro c hc
      obtain ⟨vw, _, rfl⟩ := List.mem_map.mp hc
      simp)
    (RationalWordRows.coordinateVectorsW_lengths _ _ _)
  refine ⟨out, q, e12.trans e3, v3, hq, ?_⟩
  let r0 := initialRegisters [Value.pointer vlp, .pointer ep, .pointer zp, .pointer op,
    .pointer tp]
  let r1 := bindResults r0 [5] [Value.pointer rows]
  let r2 := bindResults r1 [6] [Value.pointer coords]
  let r3 := bindResults r2 [7] [Value.pointer q]
  have last : Within code out r3 (.ret [.register 7]) [.pointer q] out 3 := by
    simpa [r3, bindResults, values, Atom.eval] using Within.ret code out r3 [.register 7]
  have fArgs : values r2 [.register 5, .register 2, .register 6] =
      [.pointer rows, .pointer zp, .pointer coords] := by
    simp [r2, r1, r0, bindResults, initialRegisters, values, Atom.eval]
  have fCall := Within.call (procedure := ids.elim.fold)
    (arguments := [.register 5, .register 2, .register 6]) (results := [7]) (regs := r2)
    (by simpa only [fArgs] using eliminated) last
  have cArgs : values r1 [.register 1, .register 2, .register 3] =
      [.pointer ep, .pointer zp, .pointer op] := by
    simp [r1, r0, bindResults, initialRegisters, values, Atom.eval]
  have cCall := Within.call (procedure := ids.inc.coords)
    (arguments := [.register 1, .register 2, .register 3]) (results := [6]) (regs := r1)
    (by simpa only [cArgs] using coorded) fCall
  have iArgs : values r0 [.register 0, .register 1, .register 2, .register 3, .register 4] =
      [.pointer vlp, .pointer ep, .pointer zp, .pointer op, .pointer tp] := by
    simp [r0, initialRegisters, values, Atom.eval]
  have iCall := Within.call (procedure := ids.inc.incidence)
    (arguments := [.register 0, .register 1, .register 2, .register 3, .register 4])
    (results := [5]) (regs := r0) (by simpa only [iArgs] using built) cCall
  rw [hcode.self]
  refine iCall.mono ?_
  simp only [budget, RegisterIncidenceRows.incidenceRowsW, List.length_map,
    RationalWordRows.coordinateVectorsW_length, List.length_cons, List.length_nil]
  omega

/-- The compiled generator procedure computes `DeterministicKernel.initial`
exactly, from the vertex words and edge-endpoint words of the graph. -/
theorem compiled {n m : ℕ} (left right : Fin m → Fin n) (hn : n < 2 ^ W)
    (hN : RationalWordRows.kernelWidth n m ≤ N)
    (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {vlp ep zp op tp : Ptr} {zero one two : BinaryRational.Word N}
    (hzr : RationalWordRows.Rep zero 0) (hor : RationalWordRows.Rep one 1)
    (htr : RationalWordRows.Rep two 2)
    (hvs : ListRep (fun heap ptr (w : Bits W) => BitsAt heap ptr w) h vlp
      (GraphReachEncoded.rangeWords W n))
    (hes : ListRep EdgeAt h ep (GraphReachEncoded.edgeWords W left right))
    (hz : At h zp zero) (ho : At h op one) (ht : At h tp two) :
    ∃ out q, ∃ rows : List (List (BinaryRational.Word N)),
      Extends h out ∧ Valid out ∧ RowsAt out q rows ∧
      List.Forall₂ RationalWordRows.RowRep rows (DeterministicKernel.initial left right) ∧
      Within code h (initialRegisters [.pointer vlp, .pointer ep, .pointer zp, .pointer op,
        .pointer tp]) (code ids.self) [.pointer q] out (budget W N n m) := by
  obtain ⟨out, q, e, v, hq, w⟩ := compiled_words code ids d hcode hh hvs hes hz ho ht
  have hlenE : (GraphReachEncoded.edgeWords W left right).length = m := by
    simp [GraphReachEncoded.edgeWords]
  have hlenV : (GraphReachEncoded.rangeWords W n).length = n := by
    simp [GraphReachEncoded.rangeWords]
  refine ⟨out, q, _, e, v, hq, ?_, by simpa only [hlenE, hlenV] using w⟩
  unfold generatorsW
  rw [hlenE]
  exact RationalWordRows.initialW_correct left right zero one hzr hor hN _
    (RegisterIncidenceRows.incidenceRowsW_correct left right hn (zero, one, two) hzr hor htr)

/-- The event bound is an explicit polynomial: degree six in the combined size. -/
theorem budget_le (W N n m : ℕ) :
    budget W N n m ≤ 40000 * (W + N + n + m + 1) ^ 6 := by
  unfold budget RegisterIncidenceRows.incidenceBudget RegisterIncidenceRows.rowBudget
    RegisterIncidenceRows.entryBudget RegisterIncidenceRows.coordsBudget
    RegisterEliminateRows.budget RegisterRationalCut.cutBudget RegisterRationalCut.nonzeroBudget
    RegisterRationalProject.projectBudget RegisterRationalProject.scaleSubBudget
    RegisterRationalRow.budget RegisterStoredRational.scalarBudget
  set s := W + N + n + m + 1 with hs
  have hW : W ≤ s := by omega
  have hN1 : N + 1 ≤ s := by omega
  have hN : N ≤ s := by omega
  have hn : n ≤ s := by omega
  have hm : m ≤ s := by omega
  have h1 : 1 ≤ s := by omega
  calc _ ≤ ((72 * s + 120 + 35) * s + 50 + 35) * s + 60 + ((84 * s + 80) * s + 13) +
        ((((2 * (3300 * s ^ 3) + 50) * s + 23 + 60 * s + 110 + 30) * s +
          ((2 * (3300 * s ^ 3) + 50) * s + 23 + 3300 * s ^ 3 +
            ((2 * (3300 * s ^ 3) + 50) * s + 23) + 70 + 35) * s +
          ((2 * (3300 * s ^ 3) + 50) * s + 23) + 120 + 30) * s + 15) + 40 := by
        gcongr
    _ ≤ 40000 * s ^ 6 := by
        have p2 : s ≤ s ^ 2 := by nlinarith
        have p3 : s ^ 2 ≤ s ^ 3 := by nlinarith
        have p4 : s ^ 3 ≤ s ^ 4 := by nlinarith
        have p5 : s ^ 4 ≤ s ^ 5 := by nlinarith
        have p6 : s ^ 5 ≤ s ^ 6 := by nlinarith
        ring_nf
        nlinarith

end WeightedMIS.RegisterKernelGenerators
