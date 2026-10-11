import QEDFV.HOL.Evaluation

/-! Semantic rule certificates for the typed HOL core. Each theorem is a direct
validity-preservation result; no soundness law is stored as a model field. -/
namespace QEDFV.HOL

structure Sequent (S : Signature) (Γ : List Ty) where
  hyps : List (Term S Γ .bool)
  concl : Term S Γ .bool

def Valid (I : ConstVal S) (s : Sequent S Γ) : Prop :=
  ∀ (ρ : TypeVal) (hρ : Admissible ρ) (η : Env ρ Γ),
    (∀ h, h ∈ s.hyps → h.eval I ρ hρ η) → s.concl.eval I ρ hρ η

def union (xs ys : List α) : List α := xs ++ ys

noncomputable def remove (xs : List α) (x : α) : List α := by
  classical exact xs.filter (fun y ↦ if y = x then false else true)

theorem mem_remove_of_mem_ne {xs : List α} {x y : α}
    (hy : y ∈ xs) (hne : y ≠ x) : y ∈ remove xs x := by
  classical
  simp [remove, hy, hne]

private theorem valid_of_union_left
    (I : ConstVal S) (A B : Sequent S Γ)
    (hA : Valid I A) (ρ : TypeVal) (hρ : Admissible ρ) (η : Env ρ Γ)
    (hHyps : ∀ h, h ∈ union A.hyps B.hyps → h.eval I ρ hρ η) :
    A.concl.eval I ρ hρ η := by
  apply hA ρ hρ η
  intro h hh
  exact hHyps h (List.mem_append_left _ hh)

private theorem valid_of_union_right
    (I : ConstVal S) (A B : Sequent S Γ)
    (hB : Valid I B) (ρ : TypeVal) (hρ : Admissible ρ) (η : Env ρ Γ)
    (hHyps : ∀ h, h ∈ union A.hyps B.hyps → h.eval I ρ hρ η) :
    B.concl.eval I ρ hρ η := by
  apply hB ρ hρ η
  intro h hh
  exact hHyps h (List.mem_append_right _ hh)

theorem valid_refl (I : ConstVal S) (t : Term S Γ a) :
    Valid I { hyps := [], concl := t.equal t } := by
  intro ρ hρ η _
  rfl

theorem valid_assume (I : ConstVal S) (p : Term S Γ .bool) :
    Valid I { hyps := [p], concl := p } := by
  intro ρ hρ η hh
  exact hh p (by simp)

theorem valid_trans
    (I : ConstVal S) (A B : Sequent S Γ) (x y z : Term S Γ a)
    (hA : A.concl = x.equal y) (hB : B.concl = y.equal z)
    (hValidA : Valid I A) (hValidB : Valid I B) :
    Valid I { hyps := union A.hyps B.hyps, concl := x.equal z } := by
  intro ρ hρ η hh
  have hxy : (x.equal y).eval I ρ hρ η := by
    simpa [hA] using valid_of_union_left I A B hValidA ρ hρ η hh
  have hyz : (y.equal z).eval I ρ hρ η := by
    simpa [hB] using valid_of_union_right I A B hValidB ρ hρ η hh
  exact Eq.trans hxy hyz

theorem valid_mkComb
    (I : ConstVal S) (A B : Sequent S Γ)
    (f g : Term S Γ (.arr a b)) (x y : Term S Γ a)
    (hA : A.concl = f.equal g) (hB : B.concl = x.equal y)
    (hValidA : Valid I A) (hValidB : Valid I B) :
    Valid I { hyps := union A.hyps B.hyps, concl := (f.app x).equal (g.app y) } := by
  intro ρ hρ η hh
  have hfg : (f.equal g).eval I ρ hρ η := by
    simpa [hA] using valid_of_union_left I A B hValidA ρ hρ η hh
  have hxy : (x.equal y).eval I ρ hρ η := by
    simpa [hB] using valid_of_union_right I A B hValidB ρ hρ η hh
  change (f.eval I ρ hρ η) (x.eval I ρ hρ η) = (g.eval I ρ hρ η) (y.eval I ρ hρ η)
  exact congrArg₂ (fun u v ↦ u v) hfg hxy

theorem valid_abs_closed
    (I : ConstVal S) (s t : Term S (a :: Γ) b)
    (hValid : Valid I { hyps := [], concl := s.equal t }) :
    Valid I { hyps := [], concl := (Term.lam s).equal (Term.lam t) } := by
  intro ρ hρ η _
  funext x
  exact hValid ρ hρ (Env.extend η x) (by simp)

theorem valid_beta
    (I : ConstVal S) (s : Term S (a :: Γ) b) (x : Term S Γ a) :
    Valid I { hyps := [], concl := (Term.lam s).app x |>.equal (s.substitute (Sub.single x)) } := by
  intro ρ hρ η _
  exact Term.eval_beta I ρ hρ η s x

def termSubstSequent (σ : Sub S Γ Δ) (s : Sequent S Γ) : Sequent S Δ :=
  { hyps := s.hyps.map (fun h ↦ h.substitute σ)
  , concl := s.concl.substitute σ }

theorem valid_inst_term
    (I : ConstVal S) (σ : Sub S Γ Δ) (s : Sequent S Γ)
    (hValid : Valid I s) :
    Valid I (termSubstSequent σ s) := by
  intro ρ hρ η hh
  change (s.concl.substitute σ).eval I ρ hρ η
  rw [Term.eval_substitute]
  apply hValid ρ hρ (Sub.evalSubst σ I ρ hρ η)
  intro h hh'
  simpa [Term.eval_substitute] using hh (h.substitute σ)
    (List.mem_map.mpr ⟨h, hh', rfl⟩)

theorem valid_eqMp
    (I : ConstVal S) (A B : Sequent S Γ) (p q : Term S Γ .bool)
    (hA : A.concl = p.equal q) (hB : B.concl = p)
    (hValidA : Valid I A) (hValidB : Valid I B) :
    Valid I { hyps := union A.hyps B.hyps, concl := q } := by
  intro ρ hρ η hh
  have hpq : (p.equal q).eval I ρ hρ η := by
    simpa [hA] using valid_of_union_left I A B hValidA ρ hρ η hh
  have hp : p.eval I ρ hρ η := by
    simpa [hB] using valid_of_union_right I A B hValidB ρ hρ η hh
  change p.eval I ρ hρ η = q.eval I ρ hρ η at hpq
  exact hpq.mp hp

theorem valid_deduct
    (I : ConstVal S) (A B : Sequent S Γ)
    (hValidA : Valid I A) (hValidB : Valid I B) :
    Valid I
      { hyps := union (remove A.hyps B.concl) (remove B.hyps A.concl)
      , concl := A.concl.equal B.concl } := by
  classical
  intro ρ hρ η hh
  apply propext
  constructor
  · intro hp
    have hB' := hValidB ρ hρ η (by
      intro h hhB
      by_cases he : h = A.concl
      · simpa [he] using hp
      · exact hh h (List.mem_append_right _ (mem_remove_of_mem_ne hhB he)))
    exact hB'
  · intro hq
    have hA' := hValidA ρ hρ η (by
      intro h hhA
      by_cases he : h = B.concl
      · simpa [he] using hq
      · exact hh h (List.mem_append_left _ (mem_remove_of_mem_ne hhA he)))
    exact hA'

end QEDFV.HOL
