module

public import WeightedMIS.RibbonTable
public import WeightedMIS.FrontCycleEnumeration

/-!
# Face enumeration on flag keys

The first-unseen scan of `RibbonEnumeration` is restated so that each fresh
root emits its full first-return cycle, and the seen list is extended at the
front by every cycle flag followed by its mirror image. Only cycles of even
length are emitted. Cycles are computed by following a successor function
until the first return to the root, with a fuel bound used only in the
reference function.

On flag keys the successor is `cornerKey T ∘ alongKey`. For the table of a
ribbon this is exactly the key of the actual rotation, so the key-level scan
of the canonical key list returns the key images of the even facial cycles of
the canonical enumeration.
-/

@[expose] public section

namespace WeightedMIS.FlagKeyFaces

open WeightedMIS.FiniteCycleEnumeration WeightedMIS.EmbeddingFaces WeightedMIS.RibbonTable
open WeightedMIS.EfficientSearch

/-! ## Generic first-return cycles -/

section Generic

variable {α β : Type*}

/-- Successive positions until the first return to `root`; fuel only bounds
the reference recursion. -/
def returnTrace [DecidableEq α] (f : α → α) (root : α) : ℕ → α → List α
  | 0, _ => []
  | k + 1, y => if y = root then [] else y :: returnTrace f root k (f y)

/-- The cycle through `x`: the root followed by its first-return trace. -/
def returnCycle [DecidableEq α] (f : α → α) (fuel : ℕ) (x : α) : List α :=
  x :: returnTrace f x fuel (f x)

/-- The parity bit of a list length, computed by alternation. -/
def parity : List α → Bool
  | [] => false
  | _ :: l => !parity l

theorem parity_eq_false_iff (l : List α) : parity l = false ↔ Even l.length := by
  induction l with
  | nil => simp [parity]
  | cons x l ih =>
    simp only [parity, Bool.not_eq_false', List.length_cons, Nat.even_add_one]
    rw [← ih]
    simp

@[simp] theorem parity_map (f : α → β) (l : List α) : parity (l.map f) = parity l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [parity, ih]

theorem returnTrace_map [DecidableEq α] [DecidableEq β] (f : α → α) (g : β → β) (enc : α → β)
    (hinj : Function.Injective enc) (hcomm : ∀ x, g (enc x) = enc (f x)) (root : α) :
    ∀ (k : ℕ) (y : α), returnTrace g (enc root) k (enc y) = (returnTrace f root k y).map enc := by
  intro k
  induction k with
  | zero => intro y; rfl
  | succ k ih =>
    intro y
    by_cases hy : y = root
    · simp [returnTrace, hy]
    · have hy' : enc y ≠ enc root := fun h => hy (hinj h)
      simp only [returnTrace, hy, hy', ite_false, List.map_cons, hcomm, ih]

theorem returnCycle_map [DecidableEq α] [DecidableEq β] (f : α → α) (g : β → β) (enc : α → β)
    (hinj : Function.Injective enc) (hcomm : ∀ x, g (enc x) = enc (f x)) (fuel : ℕ) (x : α) :
    returnCycle g fuel (enc x) = (returnCycle f fuel x).map enc := by
  simp [returnCycle, hcomm, returnTrace_map f g enc hinj hcomm]

/-- Some iterate below the fuel bound returns to the root. -/
def Returns (f : α → α) (root : α) (k : ℕ) (y : α) : Prop := ∃ j < k, f^[j] y = root

theorem Returns.step {f : α → α} {root : α} {k : ℕ} {y : α} (h : Returns f root (k + 1) y)
    (hy : y ≠ root) : Returns f root k (f y) := by
  obtain ⟨j, hj, he⟩ := h
  cases j with
  | zero => exact absurd he hy
  | succ j => exact ⟨j, by omega, by simpa only [Function.iterate_succ_apply] using he⟩

theorem Returns.pos {f : α → α} {root : α} {k : ℕ} {y : α} (h : Returns f root k y) : 0 < k := by
  obtain ⟨j, hj, -⟩ := h
  omega

/-- For a permutation the first-return cycle is the least-period trace. -/
theorem returnTrace_perm [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (x : α) :
    ∀ (i k : ℕ), i + 1 ≤ Function.minimalPeriod σ x →
      Function.minimalPeriod σ x ≤ i + 1 + k →
      returnTrace σ x k ((σ : α → α)^[i + 1] x) =
        trace σ (Function.minimalPeriod σ x - (i + 1)) ((σ : α → α)^[i + 1] x) := by
  intro i k
  induction k generalizing i with
  | zero =>
    intro h1 h2
    have he : Function.minimalPeriod σ x - (i + 1) = 0 := by omega
    rw [he]
    rfl
  | succ k ih =>
    intro h1 h2
    by_cases hlast : i + 1 = Function.minimalPeriod σ x
    · have hret : (σ : α → α)^[i + 1] x = x := by rw [hlast]; exact Function.iterate_minimalPeriod
      have he : Function.minimalPeriod σ x - (i + 1) = 0 := by omega
      rw [he, hret]
      simp [returnTrace, trace]
    · have hne : (σ : α → α)^[i + 1] x ≠ x := by
        intro heq
        have hper : Function.IsPeriodicPt σ (i + 1) x := heq
        have := hper.minimalPeriod_le (by omega)
        omega
      have hrec := ih (i + 1) (by omega) (by omega)
      have hsucc : σ ((σ : α → α)^[i + 1] x) = (σ : α → α)^[i + 1 + 1] x :=
        (Function.iterate_succ_apply' σ (i + 1) x).symm
      have hlen : Function.minimalPeriod σ x - (i + 1) =
          (Function.minimalPeriod σ x - (i + 1 + 1)) + 1 := by omega
      rw [hlen]
      simp only [returnTrace, hne, ite_false, trace, hsucc, hrec]

theorem returnCycle_perm [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (fuel : ℕ) (x : α)
    (hfuel : Fintype.card α ≤ fuel) : returnCycle σ fuel x = cycleList σ x := by
  have hp : 0 < Function.minimalPeriod σ x :=
    Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)
  have hc : Function.minimalPeriod σ x ≤ Fintype.card α := Function.minimalPeriod_le_card
  have h := returnTrace_perm σ x 0 fuel (by omega) (by omega)
  simp only [Nat.zero_add, Function.iterate_one] at h
  rw [returnCycle, h, cycleList, periodLength_eq]
  have he : Function.minimalPeriod σ x = (Function.minimalPeriod σ x - (0 + 1)) + 1 := by omega
  conv_rhs => rw [he]
  rfl

theorem mem_cycleList_iff [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (x y : α) :
    y ∈ cycleList σ x ↔ σ.SameCycle x y := by
  rw [cycleList, mem_trace_iff, periodLength_eq]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨(i : ℤ), by simpa only [zpow_natCast, Equiv.Perm.coe_pow] using hi⟩
  · intro h
    obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
    have hp := Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)
    refine ⟨i % Function.minimalPeriod σ x, Nat.mod_lt _ hp, ?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq]
    simpa only [Equiv.Perm.coe_pow] using hi

/-- The cycle lists start at their root. -/
theorem cycleList_head [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (x : α) :
    ∃ rest, cycleList σ x = x :: rest := by
  have hp := periodLength_pos σ x
  obtain ⟨k, hk⟩ : ∃ k, periodLength σ x = k + 1 := ⟨periodLength σ x - 1, by omega⟩
  exact ⟨trace σ k (σ x), by rw [cycleList, hk]; rfl⟩

end Generic

/-! ## The cycle-emitting scan -/

section Scan

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Each cycle position followed by its mirror image. -/
def mirrorBlock (mirror : α → α) (c : List α) : List α := c.flatMap (fun y => [y, mirror y])

omit [DecidableEq α] in
theorem mem_mirrorBlock (mirror : α → α) (c : List α) (y : α) :
    y ∈ mirrorBlock mirror c ↔ y ∈ c ∨ ∃ z ∈ c, mirror z = y := by
  simp only [mirrorBlock, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨z, hz, rfl | rfl⟩
    · exact Or.inl hz
    · exact Or.inr ⟨z, hz, rfl⟩
  · rintro (h | ⟨z, hz, rfl⟩)
    · exact ⟨y, h, Or.inl rfl⟩
    · exact ⟨z, hz, Or.inr rfl⟩

/-- First-unseen scan emitting the even cycles of fresh roots. -/
def scanEven (cyc : α → List α) (mirror : α → α) : List α → List α → List (List α)
  | _, [] => []
  | seen, x :: xs =>
      if x ∈ seen then scanEven cyc mirror seen xs
      else if parity (cyc x) then scanEven cyc mirror (mirrorBlock mirror (cyc x) ++ seen) xs
      else cyc x :: scanEven cyc mirror (mirrorBlock mirror (cyc x) ++ seen) xs

/-- With blocks of the same membership the scan selects the reference roots. -/
theorem scanEven_eq (cyc : α → List α) (mirror : α → α) (block : α → List α)
    (hblock : ∀ x y, y ∈ block x ↔ y ∈ mirrorBlock mirror (cyc x))
    (order seen seen' : List α) (hs : ∀ y, y ∈ seen ↔ y ∈ seen') :
    scanEven cyc mirror seen order =
      ((representatives block seen' order).filter (fun x => !parity (cyc x))).map cyc := by
  induction order generalizing seen seen' with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ∈ seen
    · have hx' : x ∈ seen' := (hs x).mp hx
      simp only [scanEven, hx, ite_true, representatives, hx']
      exact ih seen seen' hs
    · have hx' : x ∉ seen' := fun h => hx ((hs x).mpr h)
      have hs' : ∀ y, y ∈ mirrorBlock mirror (cyc x) ++ seen ↔ y ∈ seen' ++ block x := by
        intro y
        simp only [List.mem_append, hblock x y, hs y]
        exact or_comm
      have hrest := ih (mirrorBlock mirror (cyc x) ++ seen) (seen' ++ block x) hs'
      cases hp : parity (cyc x)
      · simp [scanEven, hx, hx', representatives, hp, hrest]
      · simp [scanEven, hx, hx', representatives, hp, hrest]

/-- Injective encodings commute with the scan. -/
theorem scanEven_map (cyc : α → List α) (mirror : α → α) (cycK : β → List β) (mirrorK : β → β)
    (enc : α → β) (hinj : Function.Injective enc)
    (hcyc : ∀ x, cycK (enc x) = (cyc x).map enc) (hmirror : ∀ x, mirrorK (enc x) = enc (mirror x))
    (order seen : List α) :
    scanEven cycK mirrorK (seen.map enc) (order.map enc) =
      (scanEven cyc mirror seen order).map (List.map enc) := by
  induction order generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    have hmem : enc x ∈ seen.map enc ↔ x ∈ seen := List.mem_map_of_injective hinj
    have hblock : mirrorBlock mirrorK (cycK (enc x)) ++ seen.map enc =
        (mirrorBlock mirror (cyc x) ++ seen).map enc := by
      simp [mirrorBlock, hcyc, List.map_flatMap, List.flatMap_map, hmirror]
    by_cases hx : x ∈ seen
    · simp only [List.map_cons, scanEven, hmem, hx, ite_true]
      exact ih seen
    · simp only [List.map_cons, scanEven, hmem, hx, ite_false]
      rw [hblock, hcyc, parity_map, ih]
      cases parity (cyc x) <;> simp

end Scan

/-! ## Ribbon instantiation -/

section Ribbon

variable {V E : Type*} [Fintype E] [DecidableEq E] {left right : E → V}

theorem bothTrace_block (R : Ribbon left right) (x y : Flag E) :
    y ∈ bothTrace R.rotation SidePairing.along (Fintype.card (Flag E)) x ↔
      y ∈ mirrorBlock SidePairing.along (cycleList R.rotation x) := by
  rw [mem_bothTrace_iff R.rotation SidePairing.along SidePairing.along_along, mem_mirrorBlock]
  simp only [mem_cycleList_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨SidePairing.along y, h, SidePairing.along_along y⟩
  · rintro (h | ⟨z, hz, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by rw [SidePairing.along_along]; exact hz)

/-- The facial roots of even boundary length, in computed order. -/
def evenRoots (R : Ribbon left right) (order : List (Flag E)) : List (Flag E) :=
  (R.enumeratedRoots order).filter (fun x => !parity (cycleList R.rotation x))

/-- The cycle-emitting scan yields exactly the even facial cycles. -/
theorem scanEven_ribbon (R : Ribbon left right) (order : List (Flag E)) :
    scanEven (cycleList R.rotation) SidePairing.along [] order =
      (evenRoots R order).map (cycleList R.rotation) :=
  scanEven_eq _ _ _ (bothTrace_block R) order [] [] (fun _ => Iff.rfl)

end Ribbon

/-! ## Flag keys -/

section Keys

variable {W : ℕ}

/-- Rotation on keys: turn along the edge and then through the stored corner. -/
def rotK (T : List (EdgeRec W)) (x : Bits (W + 2)) : Bits (W + 2) := cornerKey T (alongKey x)

/-- The key-level scan of a key order with first-return cycles of bounded fuel. -/
def keyEvenCycles (T : List (EdgeRec W)) (fuel : ℕ) (keys : List (Bits (W + 2))) :
    List (List (Bits (W + 2))) :=
  scanEven (returnCycle (rotK T) fuel) alongKey [] keys

variable {n m : ℕ} {left right : Fin m → Fin n}

theorem rotK_encode (hm : m < 2 ^ W) (R : Ribbon left right) (x : EmbeddingFaces.Flag (Fin m)) :
    rotK (encodeRibbon W R) (flagKey W x) = flagKey W (R.rotation x) := by
  rw [rotK, alongKey_flagKey, cornerKey_encode W hm]
  rfl

theorem keyCycle_encode (hm : m < 2 ^ W) (R : Ribbon left right) (fuel : ℕ) (hfuel : 4 * m ≤ fuel)
    (x : EmbeddingFaces.Flag (Fin m)) :
    returnCycle (rotK (encodeRibbon W R)) fuel (flagKey W x) =
      (cycleList R.rotation x).map (flagKey W) := by
  rw [returnCycle_map R.rotation _ (flagKey W) (flagKey_injective hm) (rotK_encode hm R),
    returnCycle_perm]
  simpa [EmbeddingFaces.Flag.card] using hfuel

/-- The key scan of the canonical keys returns the key images of the even
facial cycles of the canonical enumeration. -/
theorem keyEvenCycles_encode (hm : m < 2 ^ W) (R : Ribbon left right) (fuel : ℕ)
    (hfuel : 4 * m ≤ fuel) :
    keyEvenCycles (encodeRibbon W R) fuel (canonicalKeys (encodeRibbon W R)) =
      (evenRoots R (EmbeddingFaces.Flag.canonicalOrder m)).map
        (fun x => (cycleList R.rotation x).map (flagKey W)) := by
  rw [keyEvenCycles, canonicalKeys_encode]
  have h := scanEven_map (cycleList R.rotation) SidePairing.along
    (returnCycle (rotK (encodeRibbon W R)) fuel) alongKey (flagKey W) (flagKey_injective hm)
    (keyCycle_encode hm R fuel hfuel) (fun x => alongKey_flagKey x) (EmbeddingFaces.Flag.canonicalOrder m) []
  simp only [List.map_nil] at h
  rw [h, scanEven_ribbon, List.map_map]
  rfl

/-- Successor iterates of keys are keys of rotation iterates. -/
theorem rotK_iterate (hm : m < 2 ^ W) (R : Ribbon left right) (j : ℕ) (x : EmbeddingFaces.Flag (Fin m)) :
    (rotK (encodeRibbon W R))^[j] (flagKey W x) = flagKey W ((R.rotation : _ → _)^[j] x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, rotK_encode hm, ih, ← Function.iterate_succ_apply]

/-- From the successor of a root, the root returns within the fuel. -/
theorem returns_encode (hm : m < 2 ^ W) (R : Ribbon left right) (fuel : ℕ) (hfuel : 4 * m ≤ fuel)
    (x : EmbeddingFaces.Flag (Fin m)) :
    Returns (rotK (encodeRibbon W R)) (flagKey W x) fuel
      (rotK (encodeRibbon W R) (flagKey W x)) := by
  have hp : 0 < Function.minimalPeriod R.rotation x :=
    Function.minimalPeriod_pos_of_mem_periodicPts (R.rotation.injective.mem_periodicPts x)
  have hc : Function.minimalPeriod R.rotation x ≤ Fintype.card (EmbeddingFaces.Flag (Fin m)) :=
    Function.minimalPeriod_le_card
  simp only [EmbeddingFaces.Flag.card, Fintype.card_fin] at hc
  refine ⟨Function.minimalPeriod R.rotation x - 1, by omega, ?_⟩
  rw [← Function.iterate_succ_apply, rotK_iterate hm]
  congr 1
  have he : (Function.minimalPeriod R.rotation x - 1).succ = Function.minimalPeriod R.rotation x := by
    omega
  rw [he]
  exact Function.iterate_minimalPeriod

end Keys

end WeightedMIS.FlagKeyFaces
