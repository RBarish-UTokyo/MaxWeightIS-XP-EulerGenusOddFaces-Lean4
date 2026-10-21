module

public import WeightedMIS.RegisterFaceEnumeration
public import WeightedMIS.EnumeratedEmbedding

/-!
# A fixed register program enumerating actual ribbon faces

The same deterministic root list used by the actual facial matrix is now the
output of a six-procedure finite register program. Input pointer fields encode
only the supplied ribbon's actual rotation, endpoint reversal, and injective
binary flag keys. The explicit interpreter bound is polynomial in the number
of input flags and their key width.
-/

@[expose] public section

namespace WeightedMIS.RegisterFaceEnumeration

/-- Fixed finite comparator, record scan, two tracers, block, and root scan. -/
def program : RegisterMachine.Code 6 :=
  ![RegisterComparator.comparatorBody 0, RegisterFlagMembership.membershipBody 1 0,
    RegisterPermutationTrace.traceBody 2, RegisterPermutationMirror.traceBody 3,
    RegisterFaceBlock.blockBody 2 3, enumerationBody 5 1 4]

end WeightedMIS.RegisterFaceEnumeration

namespace WeightedMIS.EmbeddingFaces.Ribbon

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.FiniteCycleEnumeration WeightedMIS.RegisterFlagMembership

/-- The fixed finite program returns precisely the computed actual facial roots. -/
theorem compiled_enumerated_roots {V E : Type*} [Fintype E] [DecidableEq E]
    {left right : E → V} (R : Ribbon left right) {width : ℕ}
    (pointer : Flag E → Ptr) (key : Flag E → Bits width)
    (hinj : Function.Injective (fun x => (key x).value)) (order : List (Flag E))
    {h : Heap} (hh : Valid h) (graph : R.FlagLinksAt pointer h)
    (keys : ∀ x, KeyAt h (pointer x) (key x))
    {orderPtr fuel : Ptr} {fuelItems : List Ptr}
    (orderAt : ListAt h orderPtr (order.map pointer)) (fuelAt : ListAt h fuel fuelItems)
    (hlen : fuelItems.length = Fintype.card (Flag E)) :
    ∃ out final, Within RegisterFaceEnumeration.program h
      (initialRegisters [.pointer orderPtr, .pointer 0, .pointer fuel, .pointer 0])
      (RegisterFaceEnumeration.program 5) [.pointer out] final
      (order.length * ((36 * width + 80) * (2 * Fintype.card (Flag E) * order.length) +
        86 * Fintype.card (Flag E) + 130) + 13) ∧
      Valid final ∧ Extends h final ∧ ListAt final out ((R.enumeratedRoots order).map pointer) := by
  obtain ⟨out, final, run, valid, ext, result⟩ := RegisterFaceEnumeration.compiled
    RegisterFaceEnumeration.program 5 1 0 4 2 3 rfl rfl rfl rfl rfl rfl
    R.rotation SidePairing.along pointer key hinj order hh graph keys
    (seen := []) (tailItems := []) orderAt (.nil hh.1) fuelAt (.nil hh.1) (2 * fuelItems.length * order.length) (by simp)
  refine ⟨out, final, ?_, valid, ext, ?_⟩
  · simpa [RegisterFaceEnumeration.budget, hlen] using run
  · simpa [frontRepresentatives_self, hlen, enumeratedRoots] using result

/-- The original-edge canonical flag order gives an explicit cubic arithmetic
bound, with actual interpreter events rather than abstract scan operations. -/
theorem compiled_canonical_roots {V : Type*} {m width : ℕ}
    {left right : Fin m → V} (R : Ribbon left right)
    (pointer : Flag (Fin m) → Ptr) (key : Flag (Fin m) → Bits width)
    (hinj : Function.Injective (fun x => (key x).value))
    {h : Heap} (hh : Valid h) (graph : R.FlagLinksAt pointer h)
    (keys : ∀ x, KeyAt h (pointer x) (key x))
    {orderPtr fuel : Ptr} {fuelItems : List Ptr}
    (orderAt : ListAt h orderPtr ((Flag.canonicalOrder m).map pointer))
    (fuelAt : ListAt h fuel fuelItems) (hlen : fuelItems.length = 4 * m) :
    ∃ out final, Within RegisterFaceEnumeration.program h
      (initialRegisters [.pointer orderPtr, .pointer 0, .pointer fuel, .pointer 0])
      (RegisterFaceEnumeration.program 5) [.pointer out] final
      ((4 * m) * ((36 * width + 80) * (32 * m * m) + 344 * m + 130) + 13) ∧
      Valid final ∧ Extends h final ∧
      ListAt final out ((R.enumeratedRoots (Flag.canonicalOrder m)).map pointer) := by
  have hl : fuelItems.length = Fintype.card (Flag (Fin m)) := by simpa using hlen
  obtain ⟨out, final, run, valid, ext, result⟩ :=
    R.compiled_enumerated_roots pointer key hinj (Flag.canonicalOrder m) hh graph keys orderAt fuelAt hl
  refine ⟨out, final, ?_, valid, ext, result⟩
  convert run using 1 <;> simp only [Flag.canonicalOrder_length, Flag.card, Fintype.card_fin] <;> ring

end WeightedMIS.EmbeddingFaces.Ribbon
