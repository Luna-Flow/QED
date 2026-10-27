import QEDFV.HOL.KernelState
import QEDFV.HOL.TermLaws

/-! Comparing terms by constant names.

The kernel stamps every constant occurrence with an id, but several checked rules (`TRANS`,
`EQ_MP`, hypothesis union and removal) compare terms ignoring the stamps, that is, by constant
names. This is sound because a theorem is admissible in a state only when each constant name it
mentions resolves, in that state's scopes, to the id it carries (`resolve_thm_const_ids` in
`ensure_thm_admissible`). Within one state the name of a resolved id determines the id, so two
admissible terms with the same names are the same term.

Names are modelled by a code `nm : Nat → Nat` for the name of each id, and a state's scopes by
a resolution `r : Nat → Option Nat` from name codes to the id they currently denote. Shadowing
changes `r`; a theorem whose ids no longer resolve is not admissible, so it never meets a term
of the other identity in a name comparison. -/
namespace QEDFV.HOL

variable {S : Signature} {Γ : List Ty} {a : Ty}

/-- Replace every constant id by the code of its name. -/
def UTerm.named (nm : Nat → Nat) : UTerm → UTerm
  | .var n => .var n
  | .const c τ => .const (nm c) τ
  | .app a f x => .app a (f.named nm) (x.named nm)
  | .lam a b => .lam a (b.named nm)
  | .truth => .truth
  | .falsity => .falsity
  | .conj p q => .conj (p.named nm) (q.named nm)
  | .imp p q => .imp (p.named nm) (q.named nm)
  | .all a p => .all a (p.named nm)
  | .ex a p => .ex a (p.named nm)
  | .eq a => .eq a
  | .choice a => .choice a

/-- The constant ids of an erased term. -/
def UTerm.consts : UTerm → Set Nat
  | .var _ => ∅
  | .const c _ => {c}
  | .app _ f x => f.consts ∪ x.consts
  | .lam _ b => b.consts
  | .truth => ∅
  | .falsity => ∅
  | .conj p q => p.consts ∪ q.consts
  | .imp p q => p.consts ∪ q.consts
  | .all _ p => p.consts
  | .ex _ p => p.consts
  | .eq _ => ∅
  | .choice _ => ∅

/-- **Name comparison is injective on ids that names separate.** -/
theorem UTerm.named_inj (nm : Nat → Nat) (t u : UTerm)
    (hsep : ∀ c, c ∈ t.consts → ∀ d, d ∈ u.consts → nm c = nm d → c = d)
    (h : t.named nm = u.named nm) : t = u := by
  induction t generalizing u with
  | var n => cases u <;> simp_all [UTerm.named]
  | const c τ =>
      cases u <;> simp only [UTerm.named, UTerm.const.injEq, reduceCtorEq] at h
      obtain ⟨h1, rfl⟩ := h
      rw [hsep c (by simp [UTerm.consts]) _ (by simp [UTerm.consts]) h1]
  | app a f x ihf ihx =>
      cases u <;> simp only [UTerm.named, UTerm.app.injEq, reduceCtorEq] at h
      obtain ⟨rfl, h1, h2⟩ := h
      rw [ihf _ (fun c hc d hd ↦ hsep c (Or.inl hc) d (Or.inl hd)) h1,
        ihx _ (fun c hc d hd ↦ hsep c (Or.inr hc) d (Or.inr hd)) h2]
  | lam a b ih =>
      cases u <;> simp only [UTerm.named, UTerm.lam.injEq, reduceCtorEq] at h
      rename_i b'
      obtain ⟨rfl, h1⟩ := h
      rw [ih b' hsep h1]
  | truth => cases u <;> simp_all [UTerm.named]
  | falsity => cases u <;> simp_all [UTerm.named]
  | conj p q ihp ihq =>
      cases u <;> simp only [UTerm.named, UTerm.conj.injEq, reduceCtorEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [ihp _ (fun c hc d hd ↦ hsep c (Or.inl hc) d (Or.inl hd)) h1,
        ihq _ (fun c hc d hd ↦ hsep c (Or.inr hc) d (Or.inr hd)) h2]
  | imp p q ihp ihq =>
      cases u <;> simp only [UTerm.named, UTerm.imp.injEq, reduceCtorEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [ihp _ (fun c hc d hd ↦ hsep c (Or.inl hc) d (Or.inl hd)) h1,
        ihq _ (fun c hc d hd ↦ hsep c (Or.inr hc) d (Or.inr hd)) h2]
  | all a p ih =>
      cases u <;> simp only [UTerm.named, UTerm.all.injEq, reduceCtorEq] at h
      rename_i b'
      obtain ⟨rfl, h1⟩ := h
      rw [ih b' hsep h1]
  | ex a p ih =>
      cases u <;> simp only [UTerm.named, UTerm.ex.injEq, reduceCtorEq] at h
      rename_i b'
      obtain ⟨rfl, h1⟩ := h
      rw [ih b' hsep h1]
  | eq a => cases u <;> simp_all [UTerm.named]
  | choice a => cases u <;> simp_all [UTerm.named]

theorem Term.mem_erase_consts {t : Term S Γ a} {c : Nat} :
    c ∈ t.erase.consts ↔ c ∈ t.constIds := by
  induction t with
  | var v => simp [Term.erase, UTerm.consts, Term.constIds]
  | const d τ h => simp [Term.erase, UTerm.consts, Term.constIds]
  | app f x ihf ihx => simp [Term.erase, UTerm.consts, Term.constIds, ihf, ihx]
  | lam b ih => simp [Term.erase, UTerm.consts, Term.constIds, ih]
  | truth => simp [Term.erase, UTerm.consts, Term.constIds]
  | falsity => simp [Term.erase, UTerm.consts, Term.constIds]
  | conj p q ihp ihq => simp [Term.erase, UTerm.consts, Term.constIds, ihp, ihq]
  | imp p q ihp ihq => simp [Term.erase, UTerm.consts, Term.constIds, ihp, ihq]
  | all p ih => simp [Term.erase, UTerm.consts, Term.constIds, ih]
  | ex p ih => simp [Term.erase, UTerm.consts, Term.constIds, ih]
  | eq => simp [Term.erase, UTerm.consts, Term.constIds]
  | choice => simp [Term.erase, UTerm.consts, Term.constIds]

/-- A term is resolved under a naming and a resolution when every constant id it carries is
the id its name currently denotes. -/
def Term.Resolved (nm : Nat → Nat) (r : Nat → Option Nat) (t : Term S Γ a) : Prop :=
  ∀ c, c ∈ t.constIds → r (nm c) = some c

/-- **Comparing resolved terms by names is comparing them.** Two terms resolved in one state
with the same names (ids replaced by name codes) are equal. -/
theorem Term.eq_of_named_eq {nm : Nat → Nat} {r : Nat → Option Nat} {t u : Term S Γ a}
    (ht : t.Resolved nm r) (hu : u.Resolved nm r)
    (h : t.erase.named nm = u.erase.named nm) : t = u :=
  Term.erase_inj (UTerm.named_inj nm _ _ (fun c hc d hd hcd ↦ by
    have h1 := ht c (Term.mem_erase_consts.mp hc)
    have h2 := hu d (Term.mem_erase_consts.mp hd)
    rw [hcd, h2] at h1
    exact (Option.some.inj h1).symm) h)

/-- A sequent is resolved when its hypotheses and conclusion are. -/
def Sequent.Resolved (nm : Nat → Nat) (r : Nat → Option Nat) (s : Sequent S Γ) : Prop :=
  (∀ h, h ∈ s.hyps → h.Resolved nm r) ∧ s.concl.Resolved nm r

/-- Hypothesis membership by names agrees with membership, for resolved sequents. This is the
comparison used when theorems are combined and when `DEDUCT_ANTISYM_RULE` removes a hypothesis
(issue #2). -/
theorem Sequent.mem_hyps_of_named {nm : Nat → Nat} {r : Nat → Option Nat} {s : Sequent S Γ}
    (hs : s.Resolved nm r) {p : Term S Γ .bool} (hp : p.Resolved nm r)
    (h : ∃ q, q ∈ s.hyps ∧ q.erase.named nm = p.erase.named nm) : p ∈ s.hyps := by
  obtain ⟨q, hq, hqp⟩ := h
  rw [← Term.eq_of_named_eq (hs.1 q hq) hp hqp]
  exact hq

end QEDFV.HOL
