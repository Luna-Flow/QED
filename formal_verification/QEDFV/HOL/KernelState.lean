import QEDFV.HOL.HistoryDerivation

/-! An abstract model of the kernel's states, theorem objects and lineage.

The executable kernel threads a state through every extension and stamps each theorem with
the lineage of the state it was produced in. A theorem is admissible in a later state when its
lineage is a prefix of that state's lineage; the checked rules only combine admissible
premises. This file states what that design must guarantee and proves that it is enough.

* `KState` is a history together with allocation bounds for constant and type-constructor
  ids. The kernel allocates ids from counters, so every id mentioned by a theorem of a state is
  below the state's bounds and every id a later step introduces is at or above them.
* `KStep` is one kernel transition: an extension step, or the allocation of an opaque constant
  (`add_const`), which changes no history and only moves the bound.
* `KThm` is a theorem object: a sequent derived at the history of its origin state and scoped
  below the origin's bounds.
* `KThm.lift` transports a theorem to any state reachable from its origin. This is the
  soundness of the admissibility check: the extension steps in between never mention the
  sequent's ids, so `HistoryDerivation.weaken` applies at each of them.
* `LineageCode` is the refinement obligation on the kernel's lineage: comparing lineages must
  imply reachability. Lineage nodes interned from non-injective event strings broke it
  ([#70](https://github.com/Luna-Flow/QED/issues/70)): two sibling states with different
  definitions got one node, so a theorem was admissible in a state that does not extend its
  origin. -/
namespace QEDFV.HOL

variable {S : Signature}

/-- An abstract kernel state: a history, newest step first, and the next free constant and
type-constructor ids. -/
structure KState (S : Signature) where
  hist : List (ModelExtension S)
  nextC : Nat
  nextK : Nat

/-- A sequent is scoped below a state when every constant and type-constructor id it mentions
was allocated before the state's bounds. -/
def KState.Scoped (st : KState S) {Γ : List Ty} (s : Sequent S Γ) : Prop :=
  (∀ c, c ∈ s.constIds → c < st.nextC) ∧ (∀ k, k ∈ s.tyCons → k < st.nextK)

/-- One kernel transition. An extension step introduces only ids at or above the current
bounds and moves the bounds past them; an opaque allocation moves the constant bound only. -/
inductive KStep : KState S → KState S → Prop where
  | extend (st : KState S) (e : ModelExtension S) (nc nk : Nat)
      (hC : ∀ c, c ∈ e.constantIds → st.nextC ≤ c ∧ c < nc)
      (hK : ∀ k, k ∈ e.tyConIds → st.nextK ≤ k ∧ k < nk)
      (hnc : st.nextC ≤ nc) (hnk : st.nextK ≤ nk) :
      KStep st ⟨e :: st.hist, nc, nk⟩
  | alloc (st : KState S) (nc : Nat) (hnc : st.nextC ≤ nc) :
      KStep st ⟨st.hist, nc, st.nextK⟩

/-- Reachability between kernel states: the reflexive-transitive closure of `KStep`. -/
def KReach : KState S → KState S → Prop := Relation.ReflTransGen KStep

theorem KStep.bounds {st st' : KState S} (h : KStep st st') :
    st.nextC ≤ st'.nextC ∧ st.nextK ≤ st'.nextK := by
  cases h with
  | extend _ _ _ _ _ hnc hnk => exact ⟨hnc, hnk⟩
  | alloc _ hnc => exact ⟨hnc, le_refl _⟩

theorem KState.Scoped.mono {st st' : KState S} {Γ : List Ty} {s : Sequent S Γ}
    (h : st.Scoped s) (hC : st.nextC ≤ st'.nextC) (hK : st.nextK ≤ st'.nextK) :
    st'.Scoped s :=
  ⟨fun c hc ↦ lt_of_lt_of_le (h.1 c hc) hC, fun k hk ↦ lt_of_lt_of_le (h.2 k hk) hK⟩

/-- A sequent scoped below a state is in the old language of any step the state takes. -/
theorem KState.Scoped.oldLanguage {st : KState S} {Γ : List Ty} {s : Sequent S Γ}
    (h : st.Scoped s) (e : ModelExtension S)
    (hC : ∀ c, c ∈ e.constantIds → st.nextC ≤ c)
    (hK : ∀ k, k ∈ e.tyConIds → st.nextK ≤ k) : e.oldLanguage s := by
  have nC : ∀ c, c ∈ e.constantIds → c ∉ s.constIds :=
    fun c hc hs ↦ absurd (h.1 c hs) (not_lt.mpr (hC c hc))
  have nK : ∀ k, k ∈ e.tyConIds → k ∉ s.tyCons :=
    fun k hk hs ↦ absurd (h.2 k hs) (not_lt.mpr (hK k hk))
  cases e with
  | definition D => exact nC D.id (by simp [ModelExtension.constantIds])
  | specification E => exact nC E.gate.id (by simp [ModelExtension.constantIds])
  | typeDefinition G =>
      exact ⟨nK G.k (by simp [ModelExtension.tyConIds]),
        nC G.rep (by simp [ModelExtension.constantIds]),
        nC G.abs (by simp [ModelExtension.constantIds])⟩

/-- **One step preserves derivations of scoped sequents.** -/
theorem KStep.lift {st st' : KState S} (h : KStep st st') {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S st.hist s) (hs : st.Scoped s) :
    HistoryDerivation S st'.hist s ∧ st'.Scoped s := by
  have hb := h.bounds
  refine ⟨?_, hs.mono hb.1 hb.2⟩
  cases h with
  | extend e _ _ hC hK _ _ =>
      exact .weaken e d (hs.oldLanguage e (fun c hc ↦ (hC c hc).1) (fun k hk ↦ (hK k hk).1))
  | alloc => exact d

/-- **Admissibility is sound.** A derivation of a scoped sequent at a state transports to every
state reachable from it. -/
theorem KReach.lift {st st' : KState S} (h : KReach st st') {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S st.hist s) (hs : st.Scoped s) :
    HistoryDerivation S st'.hist s ∧ st'.Scoped s := by
  induction h with
  | refl => exact ⟨d, hs⟩
  | tail _ hstep ih => exact hstep.lift ih.1 ih.2

/-- A kernel theorem object: a sequent derived at the history of its origin state, mentioning
only ids allocated before the origin's bounds. -/
structure KThm (S : Signature) where
  origin : KState S
  ctx : List Ty
  seq : Sequent S ctx
  deriv : HistoryDerivation S origin.hist seq
  inScope : origin.Scoped seq

/-- A theorem is admissible in a state reachable from its origin. -/
def KThm.Admissible (t : KThm S) (st : KState S) : Prop := KReach t.origin st

/-- Re-stamp an admissible theorem in a later state. Rules of the kernel take premises
admissible in one state; after lifting, they are ordinary `HistoryDerivation` rules at that
state's history. -/
def KThm.lift (t : KThm S) {st : KState S} (h : t.Admissible st) : KThm S where
  origin := st
  ctx := t.ctx
  seq := t.seq
  deriv := (KReach.lift h t.deriv t.inScope).1
  inScope := (KReach.lift h t.deriv t.inScope).2

/-- Every kernel theorem is valid at its origin's model pair, and so is its lift to any state
where it is admissible. -/
theorem KThm.sound (t : KThm S) (M : Model S) (hM : M.IsLocal) :
    Valid (interpretModels t.origin.hist M).I t.seq :=
  history_derivation_sound M hM t.deriv

theorem KThm.sound_at (t : KThm S) {st : KState S} (h : t.Admissible st) (M : Model S)
    (hM : M.IsLocal) : Valid (interpretModels st.hist M).I t.seq :=
  (t.lift h).sound M hM

/-- The state invariant: every id the history introduces is below the bounds. The kernel keeps
it because ids come from its counters. -/
def KState.WF (st : KState S) : Prop :=
  (∀ c, c ∈ modelHistoryIds st.hist → c < st.nextC) ∧
    (∀ k, k ∈ modelHistoryTyCons st.hist → k < st.nextK)

theorem KState.wf_empty (nc nk : Nat) : (⟨[], nc, nk⟩ : KState S).WF :=
  ⟨fun c hc ↦ by simp [modelHistoryIds] at hc, fun k hk ↦ by simp [modelHistoryTyCons] at hk⟩

theorem KStep.wf {st st' : KState S} (h : KStep st st') (hw : st.WF) : st'.WF := by
  cases h with
  | extend e nc nk hC hK hnc hnk =>
      refine ⟨fun c hc ↦ ?_, fun k hk ↦ ?_⟩
      · simp only [modelHistoryIds, List.foldr_cons, Finset.mem_union] at hc
        rcases hc with hc | hc
        · exact (hC c hc).2
        · exact lt_of_lt_of_le (hw.1 c hc) hnc
      · rcases hk with ⟨e', he', hk⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact (hK k hk).2
        · exact lt_of_lt_of_le (hw.2 k ⟨e', he', hk⟩) hnk
  | alloc nc hnc => exact ⟨fun c hc ↦ lt_of_lt_of_le (hw.1 c hc) hnc, hw.2⟩

theorem KReach.wf {st st' : KState S} (h : KReach st st') (hw : st.WF) : st'.WF := by
  induction h with
  | refl => exact hw
  | tail _ hstep ih => exact hstep.wf ih

/-- Under the invariant, an id at or above the constant bound is fresh for the history. -/
theorem KState.WF.fresh {st : KState S} (hw : st.WF) {c : Nat} (hc : st.nextC ≤ c) :
    c ∉ modelHistoryIds st.hist := fun h ↦ absurd (hw.1 c h) (not_lt.mpr hc)

theorem KState.WF.freshK {st : KState S} (hw : st.WF) {k : Nat} (hk : st.nextK ≤ k) :
    k ∉ modelHistoryTyCons st.hist := fun h ↦ absurd (hw.2 k h) (not_lt.mpr hk)

/-- **The definition step.** The kernel allocates `D.id` at the bound and publishes the
defining equation in the new state. Scoping of that equation is the kernel's obligation: the
published theorem must be exactly `D.head = D.rhs` with the right-hand side checked in the old
state ([#69](https://github.com/Luna-Flow/QED/issues/69) published a different equation). -/
def KThm.ofDefinition (st : KState S) (hw : st.WF) (D : DefinitionGate S) (nc : Nat)
    (hid : st.nextC ≤ D.id ∧ D.id < nc)
    (hScoped : (⟨.definition D :: st.hist, nc, st.nextK⟩ : KState S).Scoped
      { hyps := [], concl := D.head.equal D.rhs }) : KThm S where
  origin := ⟨.definition D :: st.hist, nc, st.nextK⟩
  ctx := []
  seq := { hyps := [], concl := D.head.equal D.rhs }
  deriv := .definition D (hw.fresh hid.1)
  inScope := hScoped

theorem KThm.ofDefinition_step (st : KState S) (D : DefinitionGate S) (nc : Nat)
    (hid : st.nextC ≤ D.id ∧ D.id < nc) :
    KStep st ⟨.definition D :: st.hist, nc, st.nextK⟩ :=
  .extend st (.definition D) nc st.nextK
    (fun c hc ↦ by
      simp only [ModelExtension.constantIds, Finset.mem_singleton] at hc
      exact hc ▸ hid)
    (fun k hk ↦ by simp [ModelExtension.tyConIds] at hk)
    (le_of_lt (lt_of_le_of_lt hid.1 hid.2)) (le_refl _)

/-- The theorem a specification step publishes. -/
def specSequent (E : SpecificationExtension S) : Sequent S [] :=
  { hyps := [], concl := E.gate.predicate.substitute (Sub.single (E.gate.constant E.typeEq)) }

/-- **The specification step.** The witness theorem may come from any older state in which it
is admissible; it is lifted to the current state before the gate uses it. -/
def KThm.ofSpecification (st : KState S) (hw : st.WF) (E : SpecificationExtension S)
    (nc : Nat) (hid : st.nextC ≤ E.gate.id ∧ E.gate.id < nc) (w : KThm S)
    (hw' : w.Admissible st) (hctx : w.ctx = [])
    (hseq : HEq w.seq ({ hyps := [], concl := E.gate.body } : Sequent S []))
    (hScoped : (⟨.specification E :: st.hist, nc, st.nextK⟩ : KState S).Scoped
      (specSequent E)) : KThm S where
  origin := ⟨.specification E :: st.hist, nc, st.nextK⟩
  ctx := []
  seq := specSequent E
  deriv := by
    have d := (w.lift hw').deriv
    change HistoryDerivation S st.hist w.seq at d
    obtain ⟨o, c, s, dd, sc⟩ := w
    subst hctx
    cases hseq
    exact .specification E (hw.fresh hid.1) d
  inScope := hScoped

/-- **The type-definition step**, one law at a time, with a witness admissible in the old
state. -/
def KThm.ofTypeDef (st : KState S) (hw : st.WF) (G : TypeDefGate S) (l : TypeDefLaw)
    (nc nk : Nat) (hk : st.nextK ≤ G.k) (hrep : st.nextC ≤ G.rep) (habs : st.nextC ≤ G.abs)
    (wt : Term S [] G.repTy) (w : KThm S) (hw' : w.Admissible st) (hctx : w.ctx = [])
    (hseq : HEq w.seq ({ hyps := [], concl := G.pred.app wt } : Sequent S []))
    (hScoped : (⟨.typeDefinition G :: st.hist, nc, nk⟩ : KState S).Scoped (l.sequent G)) :
    KThm S where
  origin := ⟨.typeDefinition G :: st.hist, nc, nk⟩
  ctx := l.ctx G
  seq := l.sequent G
  deriv := by
    have d := (w.lift hw').deriv
    change HistoryDerivation S st.hist w.seq at d
    obtain ⟨o, c, s, dd, sc⟩ := w
    subst hctx
    cases hseq
    exact .typedef G l (hw.freshK hk) (hw.fresh hrep) (hw.fresh habs) wt d
  inScope := hScoped

/-- **The lineage obligation.** The kernel decides admissibility by comparing lineage values;
the comparison must imply reachability of the states that carry them. Equal lineages are a
special case: two states with the same lineage must be reachable from each other, which holds
for identical sibling histories but fails when distinct extensions share a lineage node. -/
structure LineageCode (S : Signature) (N : Type) where
  code : KState S → N
  le : N → N → Prop
  sound : ∀ st st', le (code st) (code st') → KReach st st'

/-- With a sound lineage code, the kernel's admissibility check implies admissibility. -/
theorem LineageCode.admissible {N : Type} (L : LineageCode S N) (t : KThm S) {st : KState S}
    (h : L.le (L.code t.origin) (L.code st)) : t.Admissible st :=
  L.sound _ _ h

/-- Histories as codes: the suffix order on histories with the allocation bounds is a sound
lineage code when the bounds are part of the code. This is the reference implementation the
kernel's interned lineage nodes refine. -/
def historyLineage (S : Signature) : LineageCode S (KState S) where
  code := id
  le := KReach
  sound := fun _ _ h ↦ h

end QEDFV.HOL
