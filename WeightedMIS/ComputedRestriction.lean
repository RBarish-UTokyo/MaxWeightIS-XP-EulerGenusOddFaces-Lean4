module

public import WeightedMIS.RibbonRestriction

/-!
# Executable first-return splicing of retained edge bands

Each trace scans at most the finite flag count and stops at its first retained
successor. Its equality to the mathematical first-return permutation proves
all surface invariants without using a chosen representative in computation.
-/

@[expose] public section

namespace WeightedMIS.PermutationDeletion

variable {α : Type*}

/-- Bounded forward scan, carrying the current point instead of recomputing
powers. The zero-fuel case is unreachable for a valid retained start. -/
def scan (σ : α → α) (p : α → Prop) [DecidablePred p] : ℕ → α → α
  | 0, x => x
  | fuel + 1, x => let y := σ x; if p y then y else scan σ p fuel y

/-- The bounded scan stops at the first retained positive iterate. -/
theorem scan_eq_of_first (σ : α → α) (p : α → Prop) [DecidablePred p]
    (fuel : ℕ) (x : α) (n : ℕ) (hn : 0 < n) (hle : n ≤ fuel)
    (hmem : p (σ^[n] x))
    (hbefore : ∀ j, 0 < j → j < n → ¬p (σ^[j] x)) :
    scan σ p fuel x = σ^[n] x := by
  induction fuel generalizing x n with
  | zero => omega
  | succ fuel ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hn0 : n = 0
      · subst n
        have hm : p (σ x) := by simpa using hmem
        simp [scan, hm]
      · have hn' : 0 < n := by omega
        have hfirst : ¬p (σ x) := by simpa using hbefore 1 (by omega) (by omega)
        rw [scan, ite_eq_right hfirst]
        have hm : p (σ^[n] (σ x)) := by simpa only [Function.iterate_succ_apply] using hmem
        have hb : ∀ j, 0 < j → j < n → ¬p (σ^[j] (σ x)) := by
          intro j hj hjn
          simpa only [Function.iterate_succ_apply] using hbefore (j + 1) (by omega) (by omega)
        simpa only [Function.iterate_succ_apply] using ih (σ x) n hn' (by omega) hm hb

variable [Fintype α]

/-- The actual scan reaches exactly the certified mathematical first return. -/
theorem scan_eq_firstReturn (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (x : {a // p a}) : scan σ p (Fintype.card α) x.val = (firstReturn σ p x).val := by
  rw [firstReturn_apply]
  exact scan_eq_of_first σ p _ x.val _ (returnTime_pos σ p x)
    (returnTime_le_card σ p x) (returnTime_mem σ p x)
    (fun j hj hjn => before_return_deleted σ p x hj hjn)

/-- Retention membership of the actual scan, with no computational choice. -/
def computedReturnMap (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (x : {a // p a}) : {a // p a} :=
  ⟨scan σ p (Fintype.card α) x.val, by
    rw [scan_eq_firstReturn]
    exact (firstReturn σ p x).property⟩

theorem computedReturnMap_eq (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (x : {a // p a}) : computedReturnMap σ p x = firstReturn σ p x :=
  Subtype.ext (scan_eq_firstReturn σ p x)

/-- Both directions of the first-return permutation are computed by bounded
scans. The inverse identities are certified by the mathematical construction. -/
def computedFirstReturn (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p] :
    Equiv.Perm {a // p a} where
  toFun := computedReturnMap σ p
  invFun := computedReturnMap σ.symm p
  left_inv := by intro x; simp only [computedReturnMap_eq, firstReturn_symm_apply]
  right_inv := by
    intro x
    rw [computedReturnMap_eq, computedReturnMap_eq]
    simpa only [Equiv.symm_symm] using firstReturn_symm_apply σ.symm p x

theorem computedFirstReturn_eq (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p] :
    computedFirstReturn σ p = firstReturn σ p := by
  apply Equiv.ext
  exact computedReturnMap_eq σ p

end WeightedMIS.PermutationDeletion

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing

variable {V E : Type*} [Fintype E] {left right : E → V} (R : Ribbon left right)
    (keep : E → Prop) [DecidablePred keep]

/-- The actual executable corner permutation after retaining the selected bands. -/
def computedRestrictedCorner : Equiv.Perm (Flag {e : E // keep e}) :=
  (Flag.retainedEquiv keep).trans
    ((PermutationDeletion.computedFirstReturn (R.corner.trans across) (fun x => keep x.edge)).trans
      ((retainedAcross keep).trans (Flag.retainedEquiv keep).symm))

/-- Computed band splicing is exactly the inherited corner matching. -/
theorem computedRestrictedCorner_eq : R.computedRestrictedCorner keep = (R.restrict keep).corner := by
  unfold computedRestrictedCorner restrict
  rw [PermutationDeletion.computedFirstReturn_eq]
  have hc : R.sidePairing.corner = R.corner := Equiv.ext R.sidePairing_corner
  simp only [retainedCorner, PermutationDeletion.splicedCorner,
    vertexNext, retainedAcross, PermutationDeletion.retainedReflection, hc]
  rfl

/-- An executable ribbon restriction, with the original vertex labels. -/
def computedRestrict : Ribbon (fun e : {e : E // keep e} => left e.val) (fun e => right e.val) where
  corner := R.computedRestrictedCorner keep
  involutive := by rw [R.computedRestrictedCorner_eq keep]; exact (R.restrict keep).involutive
  ne_self := by rw [R.computedRestrictedCorner_eq keep]; exact (R.restrict keep).ne_self
  vertex := by rw [R.computedRestrictedCorner_eq keep]; exact (R.restrict keep).vertex

/-- All mathematical deletion and capping results apply to this computed output. -/
theorem computedRestrict_eq : R.computedRestrict keep = R.restrict keep := by
  cases hr : R.restrict keep with
  | mk corner inv nf hv =>
    unfold computedRestrict
    have hc := R.computedRestrictedCorner_eq keep
    rw [hr] at hc
    simp only [hc]

end WeightedMIS.EmbeddingFaces.Ribbon
