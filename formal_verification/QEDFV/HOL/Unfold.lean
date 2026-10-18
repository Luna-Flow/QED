import QEDFV.HOL.TermLaws
import QEDFV.HOL.HistoryDerivation

/-! Replacement of constants by closed terms, and its commutation with the term operations.
This is the syntactic side of erasing a declaration step from a derivation. -/
namespace QEDFV.HOL

variable {S : Signature} {Γ Δ Θ : List Ty} {a b : Ty}

/-- A closed replacement term for every instance of every constant. -/
abbrev ConstRepl (S : Signature) := ∀ (c : Nat) (σ : TypeSub), Term S [] ((S c).subst σ)

/-- A replacement is compatible with type instantiation when instantiating a replacement
instance gives the replacement of the composite instance. -/
def ConstRepl.Compatible (R : ConstRepl S) : Prop :=
  ∀ (c : Nat) (θ σ : TypeSub),
    (R c σ).instType θ = (Ty.subst_comp (S c) θ σ).symm ▸ R c (θ.comp σ)

/-- Replace every constant occurrence by its replacement. -/
def Term.replConst (R : ConstRepl S) : {Γ : List Ty} → {a : Ty} → Term S Γ a → Term S Γ a
  | _, _, .var v => .var v
  | _, _, .const c σ => (R c σ).closedLift
  | _, _, .app f x => .app (f.replConst R) (x.replConst R)
  | _, _, .lam b => .lam (b.replConst R)
  | _, _, .truth => .truth
  | _, _, .falsity => .falsity
  | _, _, .conj p q => .conj (p.replConst R) (q.replConst R)
  | _, _, .imp p q => .imp (p.replConst R) (q.replConst R)
  | _, _, .all p => .all (p.replConst R)
  | _, _, .ex p => .ex (p.replConst R)
  | _, _, .eq => .eq
  | _, _, .choice => .choice

theorem Term.replConst_cast (R : ConstRepl S) {h : a = b} (t : Term S Γ a) :
    (h ▸ t).replConst R = h ▸ t.replConst R := by
  cases h; rfl

theorem Term.closedLift_cast {h : a = b} (t : Term S [] a) :
    ((h ▸ t : Term S [] b).closedLift : Term S Γ b) = h ▸ (t.closedLift : Term S Γ a) := by
  cases h; rfl

theorem Term.replConst_rename (R : ConstRepl S) (t : Term S Γ a) (r : Ren Γ Δ) :
    (t.rename r).replConst R = (t.replConst R).rename r := by
  induction t generalizing Δ with
  | var v => rfl
  | const c σ => exact (Term.closedLift_rename _ r).symm
  | app f x ihf ihx => simp only [Term.rename, Term.replConst, ihf, ihx]
  | lam b ih => simp only [Term.rename, Term.replConst, ih]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.rename, Term.replConst, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.rename, Term.replConst, ihp, ihq]
  | all p ih => simp only [Term.rename, Term.replConst, ih]
  | ex p ih => simp only [Term.rename, Term.replConst, ih]
  | eq => rfl
  | choice => rfl

theorem Sub.lift_replConst (R : ConstRepl S) (σ : Sub S Γ Δ) :
    @Eq (Sub S (b :: Γ) (b :: Δ)) (fun v ↦ ((Sub.lift σ) v).replConst R)
      (Sub.lift (fun v ↦ (σ v).replConst R)) := by
  funext c v
  cases v with
  | zero => rfl
  | succ v => exact Term.replConst_rename R (σ v) Var.succ

theorem Term.replConst_substitute (R : ConstRepl S) (t : Term S Γ a) (σ : Sub S Γ Δ) :
    (t.substitute σ).replConst R = (t.replConst R).substitute (fun v ↦ (σ v).replConst R) := by
  induction t generalizing Δ with
  | var v => rfl
  | const c θ => exact (Term.closedLift_substitute _ _).symm
  | app f x ihf ihx => simp only [Term.substitute, Term.replConst, ihf, ihx]
  | lam b ih => simp only [Term.substitute, Term.replConst, ih, Sub.lift_replConst]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.substitute, Term.replConst, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.substitute, Term.replConst, ihp, ihq]
  | all p ih => simp only [Term.substitute, Term.replConst, ih, Sub.lift_replConst]
  | ex p ih => simp only [Term.substitute, Term.replConst, ih, Sub.lift_replConst]
  | eq => rfl
  | choice => rfl

theorem Term.replConst_instType (R : ConstRepl S) (hR : R.Compatible) (t : Term S Γ a)
    (θ : TypeSub) : (t.instType θ).replConst R = (t.replConst R).instType θ := by
  induction t with
  | var v => rfl
  | const c σ =>
      simp only [Term.instType, Term.replConst_cast, Term.replConst]
      rw [Term.closedLift_instType, hR c θ σ, Term.closedLift_cast]
  | app f x ihf ihx => simp only [Term.instType, Term.replConst, ihf, ihx]
  | lam b ih => simp only [Term.instType, Term.replConst, ih]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.instType, Term.replConst, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.instType, Term.replConst, ihp, ihq]
  | all p ih => simp only [Term.instType, Term.replConst, ih]
  | ex p ih => simp only [Term.instType, Term.replConst, ih]
  | eq => rfl
  | choice => rfl

/-! ### Replacement on sequents and the core rules -/

def Sequent.replConst (R : ConstRepl S) (s : Sequent S Γ) : Sequent S Γ :=
  { hyps := s.hyps.map (Term.replConst R), concl := s.concl.replConst R }

theorem Term.replConst_equal (R : ConstRepl S) (x y : Term S Γ a) :
    (x.equal y).replConst R = (x.replConst R).equal (y.replConst R) := rfl

theorem Sub.single_replConst (R : ConstRepl S) (x : Term S Γ a) :
    @Eq (Sub S (a :: Γ) Γ) (fun v ↦ ((Sub.single x) v).replConst R)
      (Sub.single (x.replConst R)) := by
  funext c v
  cases v <;> rfl

theorem Term.replConst_single (R : ConstRepl S) (p : Term S (a :: Γ) b) (w : Term S Γ a) :
    (p.substitute (Sub.single w)).replConst R
      = (p.replConst R).substitute (Sub.single (w.replConst R)) := by
  rw [Term.replConst_substitute, Sub.single_replConst]

theorem HistoryDerivation.of_eq {es : List (ModelExtension S)} {s s' : Sequent S Γ}
    (e : s = s') (d : HistoryDerivation S es s) : HistoryDerivation S es s' := e ▸ d

theorem Sequent.replConst_weaken (R : ConstRepl S) (A : Sequent S Γ) :
    (weakenSequent (b := b) (A.replConst R)).hyps
      = ((weakenSequent (b := b) A).replConst R).hyps := by
  simp only [weakenSequent, Sequent.replConst, List.map_map]
  apply List.map_congr_left
  intro h _
  exact (Term.replConst_rename R h Var.succ).symm

/-! Replacement steps for each rule: from derivations of the replaced premises to a
derivation of the replaced conclusion. -/
section Steps

variable (R : ConstRepl S) {es : List (ModelExtension S)}

theorem replConst_step_trans {A B : Sequent S Γ} {x y z : Term S Γ a}
    (hA : A.concl = x.equal y) (hB : B.concl = y.equal z)
    (dA : HistoryDerivation S es (A.replConst R)) (dB : HistoryDerivation S es (B.replConst R)) :
    HistoryDerivation S es
      (({ hyps := union A.hyps B.hyps, concl := x.equal z } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl = (x.replConst R).equal (y.replConst R) := by
    simp only [Sequent.replConst, hA]; rfl
  have hB' : (B.replConst R).concl = (y.replConst R).equal (z.replConst R) := by
    simp only [Sequent.replConst, hB]; rfl
  refine HistoryDerivation.of_eq ?_ (.trans hA' hB' dA dB)
  simp [Sequent.replConst, union, List.map_append]; rfl

theorem replConst_step_mkComb {A B : Sequent S Γ} {f g : Term S Γ (.arr a b)}
    {x y : Term S Γ a}
    (hA : A.concl = f.equal g) (hB : B.concl = x.equal y)
    (dA : HistoryDerivation S es (A.replConst R)) (dB : HistoryDerivation S es (B.replConst R)) :
    HistoryDerivation S es
      (({ hyps := union A.hyps B.hyps, concl := (f.app x).equal (g.app y) } :
        Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl = (f.replConst R).equal (g.replConst R) := by
    simp only [Sequent.replConst, hA]; rfl
  have hB' : (B.replConst R).concl = (x.replConst R).equal (y.replConst R) := by
    simp only [Sequent.replConst, hB]; rfl
  refine HistoryDerivation.of_eq ?_ (.mkComb hA' hB' dA dB)
  simp [Sequent.replConst, union, List.map_append]; rfl

theorem replConst_step_abs {A : Sequent S Γ} {s t : Term S (a :: Γ) b}
    (d : HistoryDerivation S es
      (({ hyps := (weakenSequent A).hyps, concl := s.equal t } : Sequent S (a :: Γ)).replConst R)) :
    HistoryDerivation S es
      (({ hyps := A.hyps, concl := (Term.lam s).equal (Term.lam t) } :
        Sequent S Γ).replConst R) := by
  have e : (weakenSequent (b := a) (A.replConst R)).hyps
      = ((weakenSequent (b := a) A).replConst R).hyps := Sequent.replConst_weaken R A
  have ih' : HistoryDerivation S es
      { hyps := (weakenSequent (b := a) (A.replConst R)).hyps
      , concl := (s.replConst R).equal (t.replConst R) } := by
    rw [e]; exact d
  exact .abs ih'

theorem replConst_step_eqMp {A B : Sequent S Γ} {p q : Term S Γ .bool}
    (hA : A.concl = p.equal q) (hB : B.concl = p)
    (dA : HistoryDerivation S es (A.replConst R)) (dB : HistoryDerivation S es (B.replConst R)) :
    HistoryDerivation S es
      (({ hyps := union A.hyps B.hyps, concl := q } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl = (p.replConst R).equal (q.replConst R) := by
    simp only [Sequent.replConst, hA]; rfl
  have hB' : (B.replConst R).concl = p.replConst R := by
    simp only [Sequent.replConst, hB]
  refine HistoryDerivation.of_eq ?_ (.eqMp hA' hB' dA dB)
  simp [Sequent.replConst, union, List.map_append]

theorem replConst_step_deduct {A B : Sequent S Γ}
    (dA : HistoryDerivation S es (A.replConst R)) (dB : HistoryDerivation S es (B.replConst R)) :
    HistoryDerivation S es
      (({ hyps := union (remove A.hyps B.concl) (remove B.hyps A.concl),
          concl := A.concl.equal B.concl } : Sequent S Γ).replConst R) := by
  have key : ∀ (xs : List (Term S Γ .bool)) (c h : Term S Γ .bool),
      h ∈ remove (xs.map (Term.replConst R)) (c.replConst R) →
      h ∈ (remove xs c).map (Term.replConst R) := by
    intro xs c h hh
    classical
    simp only [remove, List.mem_filter, List.mem_map] at hh ⊢
    obtain ⟨⟨h0, hh0, rfl⟩, hne⟩ := hh
    refine ⟨h0, ⟨hh0, ?_⟩, rfl⟩
    by_cases e : h0 = c
    · subst e; simp at hne
    · simp [e]
  refine HistoryDerivation.weakenHyps _ ?_ (.deduct dA dB)
  intro h hh
  simp only [union, List.mem_append, List.map_append] at hh ⊢
  rcases hh with hh | hh
  · exact Or.inl (key _ _ _ hh)
  · exact Or.inr (key _ _ _ hh)

theorem replConst_step_instType (hR : R.Compatible) {A : Sequent S Γ} (θ : TypeSub)
    (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es ((typeSubstSequent θ A).replConst R) := by
  refine HistoryDerivation.of_eq ?_ (.instType θ d)
  simp only [Sequent.replConst, typeSubstSequent, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro h _
    exact (Term.replConst_instType R hR h θ).symm
  · exact (Term.replConst_instType R hR _ θ).symm

theorem replConst_step_instTerm {A : Sequent S Γ} (σ : Sub S Γ Δ)
    (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es ((termSubstSequent σ A).replConst R) := by
  refine HistoryDerivation.of_eq ?_ (.instTerm (fun v ↦ (σ v).replConst R) d)
  simp only [Sequent.replConst, termSubstSequent, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro h _
    exact (Term.replConst_substitute R h σ).symm
  · exact (Term.replConst_substitute R _ σ).symm

theorem replConst_step_chooseWitness (p : Term S (a :: Γ) .bool) (w : Term S Γ a)
    (d : HistoryDerivation S es
      (({ hyps := [], concl := p.substitute (Sub.single w) } : Sequent S Γ).replConst R)) :
    HistoryDerivation S es
      (({ hyps := [],
          concl := p.substitute (Sub.single (Term.choice.app (Term.lam p))) } :
        Sequent S Γ).replConst R) := by
  have ih' : HistoryDerivation S es
      { hyps := [], concl := (p.replConst R).substitute (Sub.single (w.replConst R)) } := by
    have := d
    simp only [Sequent.replConst, List.map_nil] at this
    rw [Term.replConst_single] at this
    exact this
  refine HistoryDerivation.of_eq ?_ (.chooseWitness (p.replConst R) (w.replConst R) ih')
  simp only [Sequent.replConst, List.map_nil]
  rw [Term.replConst_single]; rfl

theorem replConst_step_addAssum {A : Sequent S Γ} (p : Term S Γ .bool)
    (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es
      (({ hyps := p :: A.hyps, concl := A.concl } : Sequent S Γ).replConst R) :=
  .addAssum (p.replConst R) d

theorem replConst_step_weakenHyps {A : Sequent S Γ} (L : List (Term S Γ .bool))
    (hL : ∀ h, h ∈ A.hyps → h ∈ L)
    (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es
      (({ hyps := L, concl := A.concl } : Sequent S Γ).replConst R) :=
  .weakenHyps (L.map (Term.replConst R))
    (fun h hh ↦ by
      obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
      exact List.mem_map.mpr ⟨h0, hL h0 hh0, rfl⟩) d

theorem replConst_step_falsityElim {A : Sequent S Γ} (q : Term S Γ .bool)
    (hA : A.concl = Term.falsity)
    (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es
      (({ hyps := A.hyps, concl := q } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl = Term.falsity := by
    simp only [Sequent.replConst, hA]; rfl
  exact .falsityElim (q.replConst R) hA' d

theorem replConst_step_conjIntro {A B : Sequent S Γ} {p q : Term S Γ .bool}
    (hA : A.concl = p) (hB : B.concl = q)
    (dA : HistoryDerivation S es (A.replConst R)) (dB : HistoryDerivation S es (B.replConst R)) :
    HistoryDerivation S es
      (({ hyps := union A.hyps B.hyps, concl := Term.conj p q } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl = p.replConst R := by simp only [Sequent.replConst, hA]
  have hB' : (B.replConst R).concl = q.replConst R := by simp only [Sequent.replConst, hB]
  refine HistoryDerivation.of_eq ?_ (.conjIntro hA' hB' dA dB)
  simp [Sequent.replConst, union, List.map_append]; rfl

theorem replConst_step_conjElimLeft {A : Sequent S Γ} {p q : Term S Γ .bool}
    (hA : A.concl = Term.conj p q) (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es
      (({ hyps := A.hyps, concl := p } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl = Term.conj (p.replConst R) (q.replConst R) := by
    simp only [Sequent.replConst, hA]; rfl
  exact .conjElimLeft hA' d

theorem replConst_step_conjElimRight {A : Sequent S Γ} {p q : Term S Γ .bool}
    (hA : A.concl = Term.conj p q) (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es
      (({ hyps := A.hyps, concl := q } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl = Term.conj (p.replConst R) (q.replConst R) := by
    simp only [Sequent.replConst, hA]; rfl
  exact .conjElimRight hA' d

theorem replConst_step_impIntro {A : Sequent S Γ} (p : Term S Γ .bool)
    (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es
      (({ hyps := remove A.hyps p, concl := Term.imp p A.concl } : Sequent S Γ).replConst R) := by
  have key : ∀ (xs : List (Term S Γ .bool)) (c h : Term S Γ .bool),
      h ∈ remove (xs.map (Term.replConst R)) (c.replConst R) →
      h ∈ (remove xs c).map (Term.replConst R) := by
    intro xs c h hh
    classical
    simp only [remove, List.mem_filter, List.mem_map] at hh ⊢
    obtain ⟨⟨h0, hh0, rfl⟩, hne⟩ := hh
    refine ⟨h0, ⟨hh0, ?_⟩, rfl⟩
    by_cases e : h0 = c
    · subst e; simp at hne
    · simp [e]
  exact HistoryDerivation.weakenHyps _ (fun h hh ↦ key _ _ _ hh) (.impIntro (p.replConst R) d)

theorem replConst_step_impElim {A B : Sequent S Γ} {p q : Term S Γ .bool}
    (hA : A.concl = Term.imp p q) (hB : B.concl = p)
    (dA : HistoryDerivation S es (A.replConst R)) (dB : HistoryDerivation S es (B.replConst R)) :
    HistoryDerivation S es
      (({ hyps := union A.hyps B.hyps, concl := q } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl = Term.imp (p.replConst R) (q.replConst R) := by
    simp only [Sequent.replConst, hA]; rfl
  have hB' : (B.replConst R).concl = p.replConst R := by simp only [Sequent.replConst, hB]
  refine HistoryDerivation.of_eq ?_ (.impElim hA' hB' dA dB)
  simp [Sequent.replConst, union, List.map_append]

theorem replConst_step_allIntro {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
    (d : HistoryDerivation S es
      (({ hyps := (weakenSequent A).hyps, concl := φ } : Sequent S (a :: Γ)).replConst R)) :
    HistoryDerivation S es
      (({ hyps := A.hyps, concl := Term.all φ } : Sequent S Γ).replConst R) := by
  have e : (weakenSequent (b := a) (A.replConst R)).hyps
      = ((weakenSequent (b := a) A).replConst R).hyps := Sequent.replConst_weaken R A
  have ih' : HistoryDerivation S es
      { hyps := (weakenSequent (b := a) (A.replConst R)).hyps, concl := φ.replConst R } := by
    rw [e]; exact d
  exact .allIntro ih'

theorem replConst_step_allElim {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
    (t : Term S Γ a) (hA : A.concl = Term.all φ)
    (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es
      (({ hyps := A.hyps, concl := φ.substitute (Sub.single t) } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl = Term.all (φ.replConst R) := by
    simp only [Sequent.replConst, hA]; rfl
  refine HistoryDerivation.of_eq ?_ (.allElim (t.replConst R) hA' d)
  simp only [Sequent.replConst]
  rw [Term.replConst_single]

theorem replConst_step_exIntro {A : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
    (t : Term S Γ a) (hA : A.concl = φ.substitute (Sub.single t))
    (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es
      (({ hyps := A.hyps, concl := Term.ex φ } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl
      = (φ.replConst R).substitute (Sub.single (t.replConst R)) := by
    simp only [Sequent.replConst, hA]
    rw [Term.replConst_single]
  exact .exIntro (t.replConst R) hA' d

theorem replConst_step_exElim {A B : Sequent S Γ} {φ : Term S (a :: Γ) .bool}
    (hA : A.concl = Term.ex φ) (dA : HistoryDerivation S es (A.replConst R))
    (dB : HistoryDerivation S es
      (({ hyps := φ :: (weakenSequent B).hyps, concl := weakenTerm B.concl } :
        Sequent S (a :: Γ)).replConst R)) :
    HistoryDerivation S es
      (({ hyps := union A.hyps B.hyps, concl := B.concl } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl = Term.ex (φ.replConst R) := by
    simp only [Sequent.replConst, hA]; rfl
  have e1 : (weakenSequent (b := a) (B.replConst R)).hyps
      = ((weakenSequent (b := a) B).replConst R).hyps := Sequent.replConst_weaken R B
  have e2 : weakenTerm (b := a) (B.replConst R).concl = (weakenTerm B.concl).replConst R :=
    (Term.replConst_rename R B.concl Var.succ).symm
  have dB' : HistoryDerivation S es
      { hyps := φ.replConst R :: (weakenSequent (b := a) (B.replConst R)).hyps
      , concl := weakenTerm (b := a) (B.replConst R).concl } := by
    rw [e1, e2]; exact dB
  refine HistoryDerivation.of_eq ?_ (.exElim hA' dA dB')
  simp [Sequent.replConst, union, List.map_append]

theorem replConst_step_classical {A : Sequent S Γ} {p : Term S Γ .bool}
    (hA : A.concl = Term.imp (Term.imp p Term.falsity) Term.falsity)
    (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es
      (({ hyps := A.hyps, concl := p } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl
      = Term.imp (Term.imp (p.replConst R) Term.falsity) Term.falsity := by
    simp only [Sequent.replConst, hA]; rfl
  exact .classical hA' d

theorem replConst_step_chooseHyp {A : Sequent S Γ} (p : Term S (a :: Γ) .bool) (w : Term S Γ a)
    (hA : A.concl = p.substitute (Sub.single w))
    (d : HistoryDerivation S es (A.replConst R)) :
    HistoryDerivation S es
      (({ hyps := A.hyps, concl := p.substitute
            (Sub.single (Term.choice.app (Term.lam p))) } : Sequent S Γ).replConst R) := by
  have hA' : (A.replConst R).concl
      = (p.replConst R).substitute (Sub.single (w.replConst R)) := by
    simp only [Sequent.replConst, hA]
    rw [Term.replConst_single]
  refine HistoryDerivation.of_eq ?_ (.chooseHyp (p.replConst R) (w.replConst R) hA' d)
  simp only [Sequent.replConst]
  rw [Term.replConst_single]; rfl

end Steps

/-- A compatible replacement maps core derivations to history derivations of the
replaced sequent, at every history. -/
theorem Derivation.replConst (R : ConstRepl S) (hR : R.Compatible)
    (es : List (ModelExtension S)) {Γ : List Ty} {s : Sequent S Γ} (d : Derivation S s) :
    HistoryDerivation S es (s.replConst R) := by
  induction d with
  | refl t => exact .core (.refl (t.replConst R))
  | assume p => exact .core (.assume (p.replConst R))
  | addAssum p d ih => exact replConst_step_addAssum R p ih
  | trans hA hB dA dB ihA ihB => exact replConst_step_trans R hA hB ihA ihB
  | mkComb hA hB dA dB ihA ihB => exact replConst_step_mkComb R hA hB ihA ihB
  | abs d ih => exact replConst_step_abs R ih
  | @beta Γ a b s x =>
      refine HistoryDerivation.of_eq ?_ (.core (.beta (s.replConst R) (x.replConst R)))
      simp only [Sequent.replConst, List.map_nil, Term.replConst_equal]
      rw [Term.replConst_single]; rfl
  | eqMp hA hB dA dB ihA ihB => exact replConst_step_eqMp R hA hB ihA ihB
  | deduct dA dB ihA ihB => exact replConst_step_deduct R ihA ihB
  | instType θ d ih => exact replConst_step_instType R hR θ ih
  | instTerm σ d ih => exact replConst_step_instTerm R σ ih
  | chooseWitness p w d ih => exact replConst_step_chooseWitness R p w ih
  | indInfinity => exact HistoryDerivation.of_eq rfl (.core .indInfinity)
  | truthIntro => exact HistoryDerivation.of_eq rfl .truthIntro
  | falsityElim q hA d ih => exact replConst_step_falsityElim R q hA ih
  | conjIntro hA hB dA dB ihA ihB => exact replConst_step_conjIntro R hA hB ihA ihB
  | conjElimLeft hA d ih => exact replConst_step_conjElimLeft R hA ih
  | conjElimRight hA d ih => exact replConst_step_conjElimRight R hA ih
  | impIntro p d ih => exact replConst_step_impIntro R p ih
  | impElim hA hB dA dB ihA ihB => exact replConst_step_impElim R hA hB ihA ihB
  | allIntro d ih => exact replConst_step_allIntro R ih
  | allElim t hA d ih => exact replConst_step_allElim R t hA ih
  | exIntro t hA d ih => exact replConst_step_exIntro R t hA ih
  | exElim hA dA dB ihA ihB => exact replConst_step_exElim R hA ihA ihB
  | classical hA d ih => exact replConst_step_classical R hA ih
  | chooseHyp p w hA d ih => exact replConst_step_chooseHyp R p w hA ih

/-! ### Unfolding a definition -/

theorem Term.cast_symm_cast {h : a = b} (t : Term S Γ a) : h.symm ▸ (h ▸ t) = t := by
  cases h; rfl

/-- The replacement that unfolds a definition: the defined constant at instance `σ` becomes
the right-hand side instantiated at `σ`; every other constant stays. -/
def DefinitionGate.repl (D : DefinitionGate S) : ConstRepl S := fun c σ ↦
  if h : c = D.id then h ▸ D.rhs.instType σ else Term.const c σ

theorem DefinitionGate.repl_compatible (D : DefinitionGate S) : D.repl.Compatible := by
  intro c θ σ
  by_cases h : c = D.id
  · subst h
    simp only [DefinitionGate.repl, dite_true]
    have := Term.instType_instType D.rhs σ θ
    rw [← this, Term.cast_symm_cast]
  · simp [DefinitionGate.repl, h, Term.instType]

theorem DefinitionGate.replConst_of_not_mem (D : DefinitionGate S) (t : Term S Γ a)
    (h : D.id ∉ t.constIds) : t.replConst D.repl = t := by
  induction t with
  | var v => rfl
  | const c σ =>
      have hne : c ≠ D.id := fun e ↦ h (by simp [Term.constIds, e])
      simp [Term.replConst, DefinitionGate.repl, hne, Term.closedLift, Term.rename]
  | app f x ihf ihx =>
      simp only [Term.constIds, Finset.mem_union, not_or] at h
      simp only [Term.replConst, ihf h.1, ihx h.2]
  | lam b ih => simp only [Term.replConst, ih (by simpa [Term.constIds] using h)]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq =>
      simp only [Term.constIds, Finset.mem_union, not_or] at h
      simp only [Term.replConst, ihp h.1, ihq h.2]
  | imp p q ihp ihq =>
      simp only [Term.constIds, Finset.mem_union, not_or] at h
      simp only [Term.replConst, ihp h.1, ihq h.2]
  | all p ih => simp only [Term.replConst, ih (by simpa [Term.constIds] using h)]
  | ex p ih => simp only [Term.replConst, ih (by simpa [Term.constIds] using h)]
  | eq => rfl
  | choice => rfl

theorem DefinitionGate.replConst_seq_of_not_mem (D : DefinitionGate S) (s : Sequent S Γ)
    (h : D.id ∉ s.constIds) : s.replConst D.repl = s := by
  cases s with
  | mk hyps concl =>
      have hh : ∀ x ∈ hyps, D.id ∉ x.constIds := fun x hx hm ↦
        h (Sequent.mem_constIds_hyp (s := { hyps := hyps, concl := concl }) hx hm)
      have hc : D.id ∉ concl.constIds := fun hm ↦
        h (Sequent.mem_constIds_concl (s := { hyps := hyps, concl := concl }) hm)
      simp only [Sequent.replConst]
      rw [DefinitionGate.replConst_of_not_mem D concl hc]
      congr 1
      rw [List.map_congr_left (fun x hx ↦ DefinitionGate.replConst_of_not_mem D x (hh x hx))]
      simp

theorem DefinitionGate.replConst_head (D : DefinitionGate S) :
    D.head.replConst D.repl = D.rhs := by
  unfold DefinitionGate.head
  rw [Term.replConst_cast]
  simp only [Term.replConst, DefinitionGate.repl, dite_true]
  rw [Term.closedLift_nil]
  exact Term.instType_var D.rhs

/-! ### Erasing a definition from a derivation -/

theorem ExtensionDerivation.erase_definition_aux (D : DefinitionGate S)
    {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S h s) :
    ∀ es, h = ModelExtension.definition D :: es →
      HistoryDerivation S es (s.replConst D.repl) := by
  induction d with
  | core d => exact fun es _ ↦ Derivation.replConst D.repl D.repl_compatible es d
  | weaken e d hOld ih =>
      intro es heq
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      have hOld' : D.id ∉ _ := hOld
      rw [D.replConst_seq_of_not_mem _ hOld']
      exact .extension d
  | definition D' hFresh =>
      intro es heq
      obtain ⟨hD, rfl⟩ := List.cons.inj heq
      cases hD
      refine HistoryDerivation.of_eq ?_ (.core (.refl D.rhs))
      simp only [Sequent.replConst, List.map_nil, Term.replConst_equal]
      rw [D.replConst_head, D.replConst_of_not_mem D.rhs D.fresh]
  | specification E hFresh d ih => intro es heq; cases heq
  | typedef G l hk hrep habs w d ih => intro es heq; cases heq

/-- **Definition erasure.** A derivation at the history `definition D :: es` yields a
derivation at `es` of the sequent in which every occurrence of the defined constant is
replaced by its (instantiated) definition. -/
theorem HistoryDerivation.erase_definition_aux (D : DefinitionGate S)
    {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S h s) :
    ∀ es, h = ModelExtension.definition D :: es →
      HistoryDerivation S es (s.replConst D.repl) := by
  induction d with
  | core d => exact fun es _ ↦ Derivation.replConst D.repl D.repl_compatible es d
  | extension d => exact fun es heq ↦ ExtensionDerivation.erase_definition_aux D d es heq
  | weaken e d hOld ih =>
      intro es heq
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      have hOld' : D.id ∉ _ := hOld
      rw [D.replConst_seq_of_not_mem _ hOld']
      exact d
  | definition D' hFresh =>
      intro es heq
      obtain ⟨hD, rfl⟩ := List.cons.inj heq
      cases hD
      refine HistoryDerivation.of_eq ?_ (.core (.refl D.rhs))
      simp only [Sequent.replConst, List.map_nil, Term.replConst_equal]
      rw [D.replConst_head, D.replConst_of_not_mem D.rhs D.fresh]
  | specification E hFresh d ih => intro es heq; cases heq
  | typedef G l hk hrep habs w d ih => intro es heq; cases heq
  | addAssum p d ih => exact fun es heq ↦ replConst_step_addAssum D.repl p (ih es heq)
  | weakenHyps L hL d ih => exact fun es heq ↦ replConst_step_weakenHyps D.repl L hL (ih es heq)
  | trans hA hB dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_trans D.repl hA hB (ihA es heq) (ihB es heq)
  | mkComb hA hB dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_mkComb D.repl hA hB (ihA es heq) (ihB es heq)
  | abs d ih => exact fun es heq ↦ replConst_step_abs D.repl (ih es heq)
  | eqMp hA hB dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_eqMp D.repl hA hB (ihA es heq) (ihB es heq)
  | deduct dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_deduct D.repl (ihA es heq) (ihB es heq)
  | instType θ d ih =>
      exact fun es heq ↦ replConst_step_instType D.repl D.repl_compatible θ (ih es heq)
  | instTerm σ d ih => exact fun es heq ↦ replConst_step_instTerm D.repl σ (ih es heq)
  | chooseWitness p w d ih =>
      exact fun es heq ↦ replConst_step_chooseWitness D.repl p w (ih es heq)
  | truthIntro => exact fun es heq ↦ HistoryDerivation.of_eq rfl .truthIntro
  | falsityElim q hA d ih => exact fun es heq ↦ replConst_step_falsityElim D.repl q hA (ih es heq)
  | conjIntro hA hB dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_conjIntro D.repl hA hB (ihA es heq) (ihB es heq)
  | conjElimLeft hA d ih => exact fun es heq ↦ replConst_step_conjElimLeft D.repl hA (ih es heq)
  | conjElimRight hA d ih => exact fun es heq ↦ replConst_step_conjElimRight D.repl hA (ih es heq)
  | impIntro p d ih => exact fun es heq ↦ replConst_step_impIntro D.repl p (ih es heq)
  | impElim hA hB dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_impElim D.repl hA hB (ihA es heq) (ihB es heq)
  | allIntro d ih => exact fun es heq ↦ replConst_step_allIntro D.repl (ih es heq)
  | allElim t hA d ih => exact fun es heq ↦ replConst_step_allElim D.repl t hA (ih es heq)
  | exIntro t hA d ih => exact fun es heq ↦ replConst_step_exIntro D.repl t hA (ih es heq)
  | exElim hA dA dB ihA ihB =>
      exact fun es heq ↦ replConst_step_exElim D.repl hA (ihA es heq) (ihB es heq)
  | classical hA d ih => exact fun es heq ↦ replConst_step_classical D.repl hA (ih es heq)
  | chooseHyp p w hA d ih => exact fun es heq ↦ replConst_step_chooseHyp D.repl p w hA (ih es heq)

theorem HistoryDerivation.erase_definition (D : DefinitionGate S) {es : List (ModelExtension S)}
    {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S (.definition D :: es) s) :
    HistoryDerivation S es (s.replConst D.repl) :=
  HistoryDerivation.erase_definition_aux D d es rfl

/-- **Syntactic conservativity of a definition.** A sequent that does not mention the defined
constant and is derivable after the definition is derivable before it, unchanged. -/
theorem HistoryDerivation.definition_conservative (D : DefinitionGate S)
    {es : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S (.definition D :: es) s) (hOld : D.id ∉ s.constIds) :
    HistoryDerivation S es s := by
  have := d.erase_definition D
  rwa [D.replConst_seq_of_not_mem s hOld] at this

end QEDFV.HOL
