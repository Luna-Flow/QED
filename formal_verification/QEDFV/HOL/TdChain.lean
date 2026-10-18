import QEDFV.HOL.TdBelow
import QEDFV.HOL.UnfoldChain

/-! Conservativity of a parameter-free type definition above older parameter-free type
definitions. The translation of a derivation targets the full old history; a rule instance
of an older type definition is a clean ground sequent, so its translation is itself, lifted
from the older step to the full history by `weaken`. -/
namespace QEDFV.HOL

variable {S : Signature}

theorem HistoryDerivation.lift_pre {Γ : List Ty} {s : Sequent S Γ} :
    ∀ {pre h : List (ModelExtension S)}, (∀ e, e ∈ pre → e.oldLanguage s) →
      HistoryDerivation S h s → HistoryDerivation S (pre ++ h) s
  | [], h, _, d => d
  | e :: pre, h, hold, d =>
      .weaken e (HistoryDerivation.lift_pre (fun e' he' ↦ hold e' (List.mem_cons_of_mem _ he')) d)
        (hold e (List.mem_cons_self ..))

theorem up_transport {es : List (ModelExtension S)} {Γ1 Γ : List Ty} (e : Γ1 = Γ)
    (s1 : Sequent S Γ1) (s : Sequent S Γ) (hconcl : HEq s1.concl s.concl)
    (hback : ∀ h0, h0 ∈ s.hyps → ∃ h, h ∈ s1.hyps ∧ HEq h h0)
    (d : HistoryDerivation S es s) : HistoryDerivation S es s1 := by
  subst e
  have hc := eq_of_heq hconcl
  have hL : ∀ h0, h0 ∈ s.hyps → h0 ∈ s1.hyps := fun h0 hm ↦ by
    obtain ⟨h, hm', hh⟩ := hback h0 hm
    rw [← eq_of_heq hh]; exact hm'
  have d2 := HistoryDerivation.weakenHyps s1.hyps hL d
  obtain ⟨h1, c1⟩ := s1
  simp only at hc d2
  rw [hc]
  exact d2

namespace TypeDefGate

variable (G : TypeDefGate S)

theorem ctx_tr_ground (N : G.Oracle) (θ : TypeSub) :
    ∀ (Γ : List Ty), (∀ b, b ∈ Γ → G.k ∉ b.tyCons ∧ b.typeVars = ∅) →
      (Γ.map (Ty.subst θ)).map G.tr = Γ
  | [], _ => rfl
  | b :: Γ, hΓ => by
      have hb := hΓ b (List.mem_cons_self ..)
      simp only [List.map_cons]
      rw [G.tr_ground N hb.1 hb.2 θ,
        ctx_tr_ground N θ Γ (fun b' hb' ↦ hΓ b' (List.mem_cons_of_mem _ hb'))]

/-- A clean ground sequent derivable at a history is derivable, as its translation, at the
same history. -/
theorem transSeq_clean (N : G.Oracle) {Γ : List Ty} (θ : TypeSub)
    (hΓ : ∀ b, b ∈ Γ → G.k ∉ b.tyCons ∧ b.typeVars = ∅) {s : Sequent S Γ}
    (hh : ∀ h, h ∈ s.hyps → G.k ∉ h.tyCons ∧ h.annotVars = ∅)
    (hc : G.k ∉ s.concl.tyCons ∧ s.concl.annotVars = ∅)
    {es : List (ModelExtension S)} (d : HistoryDerivation S es s) :
    HistoryDerivation S es (G.transSeq N (typeSubstSequent θ s)) := by
  have e := G.ctx_tr_ground N θ Γ hΓ
  refine up_transport e _ s ?_ ?_ d
  · exact Term.erase_inj_heq' _ _ e rfl (G.erase_trans_inst N _ hc.1 hc.2 θ)
  · intro h0 hm
    refine ⟨G.trans N (h0.instType θ), ?_, ?_⟩
    · simp only [transSeq, typeSubstSequent, List.mem_append, List.mem_map]
      exact Or.inr ⟨h0.instType θ, ⟨h0, hm, rfl⟩, rfl⟩
    · exact Term.erase_inj_heq' _ _ e rfl (G.erase_trans_inst N _ (hh h0 hm).1 (hh h0 hm).2 θ)


end TypeDefGate

/-- `Gi` is newer than `Gj` and its symbols do not occur in the laws of `Gj`. -/
def Older {S : Signature} (Gi Gj : TypeDefGate S) : Prop :=
  ∀ l : TypeDefLaw, (ModelExtension.typeDefinition Gi).oldLanguage (l.sequent Gj)

namespace TypeDefGate

variable (G : TypeDefGate S)

/-- The older type definition `G0` as seen from the newer gate `G`. -/
structure Scoped (G0 : TypeDefGate S) : Prop where
  n_zero : G0.n = 0
  law : ∀ l : TypeDefLaw, (ModelExtension.typeDefinition G).oldLanguage (l.sequent G0)
  newTy_free : G.k ∉ G0.newTy.tyCons
  repTy_free : G.k ∉ G0.repTy.tyCons

/-- Transport of a derivation along a context equality, discharging reflexive hypotheses. -/
theorem final_transport' {Γ1 Γ : List Ty} (e : Γ1 = Γ) (s1 : Sequent S Γ1) (s : Sequent S Γ)
    (hconcl : HEq s1.concl s.concl)
    (hhyps : ∀ h, h ∈ s1.hyps → (∃ h0, h0 ∈ s.hyps ∧ HEq h h0) ∨
      ∃ (a : Ty) (x : Term S Γ1 a), h = x.equal x)
    (hback : ∀ h0, h0 ∈ s.hyps → ∃ h, h ∈ s1.hyps ∧ HEq h h0)
    {es : List (ModelExtension S)} (d : HistoryDerivation S es s1) :
    HistoryDerivation S es s := by
  subst e
  have hc := eq_of_heq hconcl
  have d2 : HistoryDerivation S es
      { hyps := s.hyps, concl := s1.concl } := by
    refine HistoryDerivation.cutAll (H := s1.hyps) (fun h hh ↦ ?_) d
    rcases hhyps h hh with ⟨h0, h0m, hh0⟩ | ⟨a, x, rfl⟩
    · rw [eq_of_heq hh0]; exact HistoryDerivation.assume' _ h0m
    · exact HistoryDerivation.refl' x
  rw [hc] at d2
  exact d2

section Main

variable (N : G.Oracle) (gs : List (TypeDefGate S))
  (hsc : ∀ G0, G0 ∈ gs → G.Scoped G0)
  (hpair : List.Pairwise (Older (S := S)) gs)
  (hI : G.Idem N (gs.map ModelExtension.typeDefinition))
include hsc hpair hI

/-- The history is the new history `G :: T` or a suffix of the old history `T`. -/
def HistOkC (h : List (ModelExtension S)) : Prop :=
  h = ModelExtension.typeDefinition G :: gs.map ModelExtension.typeDefinition ∨
    ∃ pre, pre ++ h = gs.map ModelExtension.typeDefinition

omit hsc hpair hI in
theorem mem_T_td {e : ModelExtension S} (he : e ∈ gs.map ModelExtension.typeDefinition) :
    ∃ G0, G0 ∈ gs ∧ e = ModelExtension.typeDefinition G0 := by
  simp only [List.mem_map] at he
  obtain ⟨G0, hG0, rfl⟩ := he
  exact ⟨G0, hG0, rfl⟩

end Main

/-! ### Ground and clean laws of a parameter-free type definition -/

theorem newTy_typeVars_empty (G0 : TypeDefGate S) (hn : G0.n = 0) : G0.newTy.typeVars = ∅ := by
  ext i
  constructor
  · intro hi
    have := G0.newTy_typeVars_lt i hi
    omega
  · intro hi; exact absurd hi (by simp)

theorem repTy_typeVars_empty (G0 : TypeDefGate S) (hn : G0.n = 0) : G0.repTy.typeVars = ∅ := by
  ext i
  constructor
  · intro hi
    have := G0.repTy_typeVars_lt i hi
    omega
  · intro hi; exact absurd hi (by simp)

theorem pred_annotVars_empty (G0 : TypeDefGate S) (hn : G0.n = 0) : G0.pred.annotVars = ∅ := by
  ext i
  constructor
  · intro hi
    have := G0.closed i hi
    omega
  · intro hi; exact absurd hi (by simp)

theorem law_ground (G0 : TypeDefGate S) (hn : G0.n = 0) (l : TypeDefLaw) :
    (∀ h, h ∈ (l.sequent G0).hyps → h.annotVars = ∅) ∧ (l.sequent G0).concl.annotVars = ∅ := by
  have h1 := newTy_typeVars_empty G0 hn
  have h2 := repTy_typeVars_empty G0 hn
  have h3 := pred_annotVars_empty G0 hn
  cases l with
  | absRep =>
      refine ⟨fun h hh ↦ by simp [TypeDefLaw.sequent, absRepSequent] at hh, ?_⟩
      simp [TypeDefLaw.sequent, absRepSequent, Term.equal, Term.annotVars, repTerm, absTerm,
        Ty.typeVars, h1, h2]
  | repRange =>
      refine ⟨fun h hh ↦ by simp [TypeDefLaw.sequent, repRangeSequent] at hh, ?_⟩
      simp [TypeDefLaw.sequent, repRangeSequent, Term.annotVars, repTerm, predIn,
        Term.annotVars_rename, Ty.typeVars, h1, h2, h3]
  | repAbs =>
      refine ⟨fun h hh ↦ ?_, ?_⟩
      · simp only [TypeDefLaw.sequent, repAbsSequent, List.mem_singleton] at hh
        subst hh
        simp [Term.annotVars, predIn, Term.annotVars_rename, Ty.typeVars, h2, h3]
      · simp [TypeDefLaw.sequent, repAbsSequent, Term.equal, Term.annotVars, repTerm, absTerm,
          Ty.typeVars, h1, h2]


section Trans

variable (N : G.Oracle) (gs : List (TypeDefGate S))
  (hsc : ∀ G0, G0 ∈ gs → G.Scoped G0)
  (hpair : List.Pairwise (Older (S := S)) gs)
  (hI : G.Idem N (gs.map ModelExtension.typeDefinition))
include hsc hpair hI

/-- A rule instance of an older type definition translates to itself. -/
theorem old_law_trans {G0 : TypeDefGate S} (hG0 : G0 ∈ gs)
    {pre es : List (ModelExtension S)}
    (hpre : pre ++ ModelExtension.typeDefinition G0 :: es = gs.map ModelExtension.typeDefinition)
    (l : TypeDefLaw) {w0 : Term S [] G0.repTy}
    (hk : G0.k ∉ modelHistoryTyCons es) (hrep : G0.rep ∉ modelHistoryIds es)
    (habs : G0.abs ∉ modelHistoryIds es)
    (d0 : HistoryDerivation S es { hyps := [], concl := G0.pred.app w0 }) (θ : TypeSub) :
    HistoryDerivation S (gs.map ModelExtension.typeDefinition)
      (G.transSeq N (typeSubstSequent θ (l.sequent G0))) := by
  have hsc0 := hsc G0 hG0
  have drule : HistoryDerivation S (ModelExtension.typeDefinition G0 :: es) (l.sequent G0) :=
    .typedef G0 l hk hrep habs w0 d0
  have hold : ∀ e, e ∈ pre → e.oldLanguage (l.sequent G0) := by
    intro e he
    have hp : List.Pairwise (fun e1 e2 : ModelExtension S ↦ ∀ G1,
        e2 = ModelExtension.typeDefinition G1 → ∀ l : TypeDefLaw,
        e1.oldLanguage (l.sequent G1)) (gs.map ModelExtension.typeDefinition) :=
      List.pairwise_map.2 (hpair.imp fun {a b} h G1 heq l ↦ by cases heq; exact h l)
    rw [← hpre] at hp
    exact (List.pairwise_append.1 hp).2.2 e he _ (List.mem_cons_self ..) G0 rfl l
  have dl := HistoryDerivation.lift_pre hold drule
  rw [hpre] at dl
  have hg := law_ground G0 hsc0.n_zero l
  have hkf := (hsc0.law l).1
  refine G.transSeq_clean N θ ?_ ?_ ?_ dl
  · intro b hb
    have h1 := newTy_typeVars_empty G0 hsc0.n_zero
    have h2 := repTy_typeVars_empty G0 hsc0.n_zero
    cases l <;> simp only [TypeDefLaw.ctx, List.mem_singleton] at hb <;> subst hb
    · exact ⟨hsc0.newTy_free, h1⟩
    · exact ⟨hsc0.newTy_free, h1⟩
    · exact ⟨hsc0.repTy_free, h2⟩
  · intro h hh
    exact ⟨fun hm ↦ hkf (Sequent.tyCons_hyp hh hm), hg.1 h hh⟩
  · exact ⟨fun hm ↦ hkf (Sequent.tyCons_concl _ hm), hg.2⟩

omit hI in
theorem not_def_in_T {D : DefinitionGate S} {pre es : List (ModelExtension S)}
    (hpre : pre ++ ModelExtension.definition D :: es = gs.map ModelExtension.typeDefinition) :
    False := by
  have : ModelExtension.definition D ∈ gs.map ModelExtension.typeDefinition := by
    rw [← hpre]; simp
  obtain ⟨G0, _, h⟩ := mem_T_td gs this
  cases h

omit hI in
theorem not_spec_in_T {E : SpecificationExtension S} {pre es : List (ModelExtension S)}
    (hpre : pre ++ ModelExtension.specification E :: es = gs.map ModelExtension.typeDefinition) :
    False := by
  have : ModelExtension.specification E ∈ gs.map ModelExtension.typeDefinition := by
    rw [← hpre]; simp
  obtain ⟨G0, _, h⟩ := mem_T_td gs this
  cases h

omit hsc hpair hI in
theorem not_new_of_suffix {h : List (ModelExtension S)}
    (hh : ∃ pre, pre ++ h = gs.map ModelExtension.typeDefinition) :
    h ≠ ModelExtension.typeDefinition G :: gs.map ModelExtension.typeDefinition := by
  obtain ⟨pre, hpre⟩ := hh
  intro heq
  have := congrArg List.length hpre
  rw [heq] at this
  simp at this
  omega

theorem ext_trans_chain {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : ExtensionDerivation S h s) (hh : G.HistOkC gs h)
    (hLh : h = ModelExtension.typeDefinition G :: gs.map ModelExtension.typeDefinition →
      ∀ args, G.LawData N (gs.map ModelExtension.typeDefinition) args) (θ : TypeSub) :
    HistoryDerivation S (gs.map ModelExtension.typeDefinition)
      (G.transSeq N (typeSubstSequent θ s)) := by
  revert hh hLh θ
  induction d with
  | core d => exact fun _ _ θ ↦ G.core_trans N hI d θ
  | @weaken es' Γ s e d hOld ih =>
      intro hh hLh θ
      rcases hh with hh | ⟨pre, hpre⟩
      · obtain ⟨_, rfl⟩ := List.cons.inj hh
        exact ih (Or.inr ⟨[], rfl⟩) (fun heq ↦ absurd heq (G.not_new_of_suffix gs ⟨[], rfl⟩)) θ
      · exact ih (Or.inr ⟨pre ++ [e], by simpa using hpre⟩)
          (fun heq ↦ absurd heq (G.not_new_of_suffix gs ⟨pre ++ [e], by simpa using hpre⟩)) θ
  | definition D hFresh =>
      intro hh hLh θ
      rcases hh with hh | ⟨pre, hpre⟩
      · cases (List.cons.inj hh).1
      · exact (G.not_def_in_T gs hsc hpair hpre).elim
  | specification E hFresh d ih =>
      intro hh hLh θ
      rcases hh with hh | ⟨pre, hpre⟩
      · cases (List.cons.inj hh).1
      · exact (G.not_spec_in_T gs hsc hpair hpre).elim
  | typedef G' l hk hrep habs w' d' ih =>
      intro hh hLh θ
      rcases hh with hh | ⟨pre, hpre⟩
      · obtain ⟨hG, _⟩ := List.cons.inj hh
        cases hG
        cases l with
        | absRep => exact G.trans_law1 N hI θ (hLh hh (G.θa θ))
        | repRange => exact G.trans_law2 N hI θ (hLh hh (G.θa θ))
        | repAbs => exact G.trans_law3 N hI θ (hLh hh (G.θa θ))
      · have hmem : ModelExtension.typeDefinition G' ∈ gs.map ModelExtension.typeDefinition := by
          rw [← hpre]; simp
        obtain ⟨G0, hG0, hG'⟩ := mem_T_td gs hmem
        cases hG'
        exact G.old_law_trans N gs hsc hpair hI hG0 hpre l hk hrep habs
          (.extension d') θ

theorem hd_trans_chain {h : List (ModelExtension S)} {Γ : List Ty} {s : Sequent S Γ}
    (d : HistoryDerivation S h s) (hh : G.HistOkC gs h)
    (hLh : h = ModelExtension.typeDefinition G :: gs.map ModelExtension.typeDefinition →
      ∀ args, G.LawData N (gs.map ModelExtension.typeDefinition) args) (θ : TypeSub) :
    HistoryDerivation S (gs.map ModelExtension.typeDefinition)
      (G.transSeq N (typeSubstSequent θ s)) := by
  revert hh hLh θ
  induction d with
  | core d => exact fun _ _ θ ↦ G.core_trans N hI d θ
  | extension d => exact fun hh hLh θ ↦ G.ext_trans_chain N gs hsc hpair hI d hh hLh θ
  | @weaken es' Γ s e d hOld ih =>
      intro hh hLh θ
      rcases hh with hh | ⟨pre, hpre⟩
      · obtain ⟨_, rfl⟩ := List.cons.inj hh
        exact ih (Or.inr ⟨[], rfl⟩) (fun heq ↦ absurd heq (G.not_new_of_suffix gs ⟨[], rfl⟩)) θ
      · exact ih (Or.inr ⟨pre ++ [e], by simpa using hpre⟩)
          (fun heq ↦ absurd heq (G.not_new_of_suffix gs ⟨pre ++ [e], by simpa using hpre⟩)) θ
  | definition D hFresh =>
      intro hh hLh θ
      rcases hh with hh | ⟨pre, hpre⟩
      · cases (List.cons.inj hh).1
      · exact (G.not_def_in_T gs hsc hpair hpre).elim
  | specification E hFresh d ih =>
      intro hh hLh θ
      rcases hh with hh | ⟨pre, hpre⟩
      · cases (List.cons.inj hh).1
      · exact (G.not_spec_in_T gs hsc hpair hpre).elim
  | typedef G' l hk hrep habs w' d' ih =>
      intro hh hLh θ
      rcases hh with hh | ⟨pre, hpre⟩
      · obtain ⟨hG, _⟩ := List.cons.inj hh
        cases hG
        cases l with
        | absRep => exact G.trans_law1 N hI θ (hLh hh (G.θa θ))
        | repRange => exact G.trans_law2 N hI θ (hLh hh (G.θa θ))
        | repAbs => exact G.trans_law3 N hI θ (hLh hh (G.θa θ))
      · have hmem : ModelExtension.typeDefinition G' ∈ gs.map ModelExtension.typeDefinition := by
          rw [← hpre]; simp
        obtain ⟨G0, hG0, hG'⟩ := mem_T_td gs hmem
        cases hG'
        exact G.old_law_trans N gs hsc hpair hI hG0 hpre l hk hrep habs d' θ
  | @weakenHyps es' Γ A L hL d ih =>
      intro hh hLh θ
      refine G.transSeq_mono N ?_ ?_ (ih hh hLh θ)
      · rfl
      · intro x hx
        simp only [typeSubstSequent, List.mem_map] at hx ⊢
        obtain ⟨u, hu, rfl⟩ := hx
        exact ⟨u, hL u hu, rfl⟩
  | addAssum p d ih =>
      intro hh hLh θ
      exact G.step_addAssum N hI (p.instType θ) (ih hh hLh θ)
  | @trans es' Γ a A B x y z hA hB dA dB ihA ihB =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl = (x.instType θ).equal (y.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = (y.instType θ).equal (z.instType θ) := by
        simp only [typeSubstSequent]; rw [hB]; rfl
      have step := G.step_trans N hI hA' hB' (ihA hh hLh θ) (ihB hh hLh θ)
      refine G.transSeq_mono N ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @mkComb es' Γ a b A B f g x y hA hB dA dB ihA ihB =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl = (f.instType θ).equal (g.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = (x.instType θ).equal (y.instType θ) := by
        simp only [typeSubstSequent]; rw [hB]; rfl
      have step := G.step_mkComb N hI hA' hB' (ihA hh hLh θ) (ihB hh hLh θ)
      refine G.transSeq_mono N ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @abs es' Γ a b A s t d ih =>
      intro hh hLh θ
      have e : typeSubstSequent θ (⟨(weakenSequent (b := a) A).hyps, s.equal t⟩ :
          Sequent S (a :: Γ)) = ⟨(weakenSequent (b := a.subst θ) (typeSubstSequent θ A)).hyps,
            (s.instType θ).equal (t.instType θ)⟩ := by
        simp only [typeSubstSequent]
        congr 1
        exact weaken_inst A θ
      exact G.step_abs N hI (G.transSeq_of_eq N e (ih hh hLh θ))
  | @eqMp es' Γ A B p q hA hB dA dB ihA ihB =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl = (p.instType θ).equal (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = p.instType θ := by
        simp only [typeSubstSequent]; rw [hB]
      have step := G.step_eqMp N hI hA' hB' (ihA hh hLh θ) (ihB hh hLh θ)
      refine G.transSeq_mono N ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @deduct es' Γ A B dA dB ihA ihB =>
      intro hh hLh θ
      have step := G.step_deduct N hI (ihA hh hLh θ) (ihB hh hLh θ)
      refine G.transSeq_mono N ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        rcases hh with hh | hh
        · exact Or.inl (remove_map_sub (fun h ↦ h.instType θ) A.hyps B.concl h hh)
        · exact Or.inr (remove_map_sub (fun h ↦ h.instType θ) B.hyps A.concl h hh)
  | @instType es' Γ A θ' d ih =>
      intro hh hLh θ
      exact G.transSeq_heq N (ctx_map_comp Γ θ' θ).symm
        (typeSubstSequent_comp A θ' θ).symm (ih hh hLh (θ.comp θ'))
  | @instTerm es' Γ Δ A σ d ih =>
      intro hh hLh θ
      have step := G.step_instTerm N hI (Sub.mapTypes θ σ) (ih hh hLh θ)
      refine G.transSeq_of_eq N ?_ step
      simp only [termSubstSequent, typeSubstSequent, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro h _
        exact (Term.substitute_instType h σ θ).symm
      · exact (Term.substitute_instType _ σ θ).symm
  | @chooseWitness es' Γ a p w d ih =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ (⟨[], p.substitute (Sub.single w)⟩ : Sequent S Γ)).concl
          = (p.instType θ).substitute (Sub.single (w.instType θ)) := by
        simp only [typeSubstSequent]; rw [Term.instType_single]
      have step := G.step_chooseHyp N hI (p.instType θ) (w.instType θ) hA' (ih hh hLh θ)
      refine G.transSeq_of_eq N ?_ step
      simp only [typeSubstSequent, List.map_nil]
      congr 1
      rw [Term.instType_single]
      rfl
  | truthIntro =>
      intro hh hLh θ
      exact G.step_truthIntro N hI
  | @falsityElim es' Γ A q hA d ih =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl = Term.falsity := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_falsityElim N hI (q.instType θ) hA' (ih hh hLh θ)
  | @conjIntro es' Γ A B p q hA hB dA dB ihA ihB =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl = p.instType θ := by
        simp only [typeSubstSequent]; rw [hA]
      have hB' : (typeSubstSequent θ B).concl = q.instType θ := by
        simp only [typeSubstSequent]; rw [hB]
      have step := G.step_conjIntro N hI hA' hB' (ihA hh hLh θ) (ihB hh hLh θ)
      refine G.transSeq_mono N ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @conjElimLeft es' Γ A p q hA d ih =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl = Term.conj (p.instType θ) (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_conjElimLeft N hI hA' (ih hh hLh θ)
  | @conjElimRight es' Γ A p q hA d ih =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl = Term.conj (p.instType θ) (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_conjElimRight N hI hA' (ih hh hLh θ)
  | @impIntro es' Γ A p d ih =>
      intro hh hLh θ
      have step := G.step_impIntro N hI (p.instType θ) (ih hh hLh θ)
      refine G.transSeq_mono N ?_ ?_ step
      · rfl
      · intro h hh
        simp only [typeSubstSequent] at hh ⊢
        exact remove_map_sub (fun h ↦ h.instType θ) A.hyps p h hh
  | @impElim es' Γ A B p q hA hB dA dB ihA ihB =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl = Term.imp (p.instType θ) (q.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have hB' : (typeSubstSequent θ B).concl = p.instType θ := by
        simp only [typeSubstSequent]; rw [hB]
      have step := G.step_impElim N hI hA' hB' (ihA hh hLh θ) (ihB hh hLh θ)
      refine G.transSeq_mono N ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @allIntro es' Γ a A φ d ih =>
      intro hh hLh θ
      have e : typeSubstSequent θ (⟨(weakenSequent (b := a) A).hyps, φ⟩ :
          Sequent S (a :: Γ)) = ⟨(weakenSequent (b := a.subst θ) (typeSubstSequent θ A)).hyps,
            φ.instType θ⟩ := by
        simp only [typeSubstSequent]
        congr 1
        exact weaken_inst A θ
      exact G.step_allIntro N hI (G.transSeq_of_eq N e (ih hh hLh θ))
  | @allElim es' Γ a A φ t hA d ih =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl = Term.all (φ.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have step := G.step_allElim N hI (t.instType θ) hA' (ih hh hLh θ)
      refine G.transSeq_of_eq N ?_ step
      simp only [typeSubstSequent]
      rw [Term.instType_single]
  | @exIntro es' Γ a A φ t hA d ih =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl
          = (φ.instType θ).substitute (Sub.single (t.instType θ)) := by
        simp only [typeSubstSequent]; rw [hA, Term.instType_single]
      exact G.step_exIntro N hI (t.instType θ) hA' (ih hh hLh θ)
  | @exElim es' Γ a A B φ hA dA dB ihA ihB =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl = Term.ex (φ.instType θ) := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      have e : typeSubstSequent θ (⟨φ :: (weakenSequent (b := a) B).hyps, weakenTerm B.concl⟩ :
          Sequent S (a :: Γ)) = ⟨φ.instType θ :: (weakenSequent (b := a.subst θ)
            (typeSubstSequent θ B)).hyps, weakenTerm (b := a.subst θ) (B.concl.instType θ)⟩ := by
        simp only [typeSubstSequent, List.map_cons]
        congr 1
        · congr 1
          exact weaken_inst B θ
        · exact weakenTerm_inst B.concl θ
      have step := G.step_exElim N hI hA' (ihA hh hLh θ) (G.transSeq_of_eq N e (ihB hh hLh θ))
      refine G.transSeq_mono N ?_ ?_ step
      · rfl
      · intro h hh
        simp only [union, List.mem_append, typeSubstSequent, List.map_append] at hh ⊢
        exact hh
  | @classical es' Γ A p hA d ih =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl
          = Term.imp (Term.imp (p.instType θ) Term.falsity) Term.falsity := by
        simp only [typeSubstSequent]; rw [hA]; rfl
      exact G.step_classical N hI hA' (ih hh hLh θ)
  | @chooseHyp es' Γ a A p w hA d ih =>
      intro hh hLh θ
      have hA' : (typeSubstSequent θ A).concl
          = (p.instType θ).substitute (Sub.single (w.instType θ)) := by
        simp only [typeSubstSequent]; rw [hA, Term.instType_single]
      have step := G.step_chooseHyp N hI (p.instType θ) (w.instType θ) hA' (ih hh hLh θ)
      refine G.transSeq_of_eq N ?_ step
      simp only [typeSubstSequent]
      congr 1
      rw [Term.instType_single]
      rfl

end Trans


theorem typedef_conservative_chain (N : G.Oracle) (gs : List (TypeDefGate S))
    (hsc : ∀ G0, G0 ∈ gs → G.Scoped G0)
    (hpair : List.Pairwise (Older (S := S)) gs)
    (hI : G.Idem N (gs.map ModelExtension.typeDefinition))
    (hL : ∀ args, G.LawData N (gs.map ModelExtension.typeDefinition) args)
    {Γ : List Ty} {s : Sequent S Γ}
    (hΓ : ∀ b, b ∈ Γ → G.k ∉ b.tyCons) (hclean : s.Clean G.k)
    (d : HistoryDerivation S (ModelExtension.typeDefinition G ::
      gs.map ModelExtension.typeDefinition) s) :
    HistoryDerivation S (gs.map ModelExtension.typeDefinition) s := by
  have d1 := G.hd_trans_chain N gs hsc hpair hI d (Or.inl rfl) (fun _ ↦ hL) Ty.var
  have e := G.ctx_tr_var Γ hΓ
  refine final_transport' e _ s ?_ ?_ ?_ d1
  · exact G.trans_inst_var_heq N s.concl hclean.2 e rfl
  · intro h hh
    simp only [transSeq, typeSubstSequent, List.mem_append, List.mem_map] at hh
    rcases hh with hh | ⟨u, ⟨h0, hh0, rfl⟩, rfl⟩
    · right
      obtain ⟨a, v, rfl⟩ := G.ctxFix_elem N h hh
      have ha : G.k ∉ a.tyCons := by
        have hm := Var.mem v
        simp only [List.mem_map] at hm
        obtain ⟨b, hb, rfl⟩ := hm
        rw [Ty.subst_id]; exact hΓ b hb
      refine ⟨G.tr a, Term.var (Var.mapTy G.tr v), ?_⟩
      rw [G.nrmTy_of_not_mem N a ha]
    · left
      exact ⟨h0, hh0, G.trans_inst_var_heq N h0 (hclean.1 h0 hh0) e rfl⟩
  · intro h0 hh0
    refine ⟨G.trans N (h0.instType Ty.var), ?_,
      G.trans_inst_var_heq N h0 (hclean.1 h0 hh0) e rfl⟩
    simp only [transSeq, typeSubstSequent, List.mem_append, List.mem_map]
    exact Or.inr ⟨h0.instType Ty.var, ⟨h0, hh0, rfl⟩, rfl⟩

end TypeDefGate

end QEDFV.HOL
