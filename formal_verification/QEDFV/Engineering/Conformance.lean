import QEDFV.Conservativity.GlobalConservativity

namespace QEDFV

structure Realization where
  kernel : KernelState
  accepts : Sequent -> Prop
  replayDerivation : Sequent -> DerivationObj
  replayCertificates : Sequent -> List (GateKind × String)

def ruleFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s -> Derivable r.kernel s

def replayFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s -> Derives r.kernel (r.replayDerivation s) s

def boundaryFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s -> OldLang r.kernel.T s

def scopeFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s -> ScopedWF r.kernel.S

def gateCertificateWellFormed (_t : TheoryState) (_kind : GateKind) (cert : String) : Prop :=
  cert ≠ ""

mutual

def gateChecked (t : TheoryState) : DerivationObj -> Prop
  | .leaf _ => True
  | .rule _ ds _ => gateCheckedList t ds
  | .gate kind cert d _ => gateCertificateWellFormed t kind cert ∧ gateChecked t d

def gateCheckedList (t : TheoryState) : List DerivationObj -> Prop
  | [] => True
  | d :: ds => gateChecked t d ∧ gateCheckedList t ds

end

def gateFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s ->
    gateChecked r.kernel.T (r.replayDerivation s) ∧
    (∀ gc, gc ∈ r.replayCertificates s ->
      gateCertificateWellFormed r.kernel.T gc.fst gc.snd)

mutual

def stripGateCertificates : DerivationObj -> DerivationObj
  | .leaf s => .leaf s
  | .rule r ds s => .rule r (stripGateCertificatesList ds) s
  | .gate kind _ d s => .gate kind "" (stripGateCertificates d) s

def stripGateCertificatesList : List DerivationObj -> List DerivationObj
  | [] => []
  | d :: ds => stripGateCertificates d :: stripGateCertificatesList ds

end

theorem stripGateCertificatesList_mem :
    ∀ ds d', d' ∈ stripGateCertificatesList ds ->
      ∃ d0, d0 ∈ ds ∧ stripGateCertificates d0 = d'
  | [], d', hMem => by
      cases hMem
  | d :: ds, d', hMem => by
      simp [stripGateCertificatesList] at hMem
      rcases hMem with hHead | hTail
      · exact ⟨d, by simp, hHead.symm⟩
      · rcases stripGateCertificatesList_mem ds d' hTail with ⟨d0, hd0, hEq⟩
        exact ⟨d0, by simp [hd0], hEq⟩

theorem stripGateCertificates_preserves_derives_aux
    (k : KernelState) :
    ∀ d s, Derives k d s -> Derives k (stripGateCertificates d) s
  | .leaf _, s, h => by
      simpa [stripGateCertificates] using h
  | .rule r ds seq, s, h => by
      simp [Derives, stripGateCertificates] at h ⊢
      rcases h with ⟨hTarget, hDer, hChildren⟩
      refine ⟨hTarget, hDer, ?_⟩
      intro d' hd'
      rcases stripGateCertificatesList_mem ds d' hd' with ⟨d0, hd0in, hd0eq⟩
      rcases hChildren d0 hd0in with ⟨sp, hDer0⟩
      refine ⟨sp, ?_⟩
      simpa [hd0eq] using stripGateCertificates_preserves_derives_aux k d0 sp hDer0
  | .gate kind cert d _, s, h => by
      simp [Derives] at h
      rcases h with ⟨hTarget, hChild⟩
      subst hTarget
      simp [stripGateCertificates, Derives]
      exact stripGateCertificates_preserves_derives_aux k d s hChild

theorem stripGateCertificates_preserves_derives
    (k : KernelState)
    (d : DerivationObj)
    (s : Sequent)
    (hDerives : Derives k d s) :
    Derives k (stripGateCertificates d) s := by
  exact stripGateCertificates_preserves_derives_aux k d s hDerives

def certificateNonAuthority (r : Realization) : Prop :=
  ∀ s, r.accepts s ->
    Derives r.kernel (stripGateCertificates (r.replayDerivation s)) s

theorem certificate_non_authority_from_replay
    (r : Realization)
    (hReplay : replayFidelity r) :
    certificateNonAuthority r := by
  intro s hAccept
  exact stripGateCertificates_preserves_derives r.kernel (r.replayDerivation s) s
    (hReplay s hAccept)

structure FaithfulRealization (r : Realization) : Prop where
  rule : ruleFidelity r
  replay : replayFidelity r
  boundary : boundaryFidelity r
  scope : scopeFidelity r
  gate : gateFidelity r
  cert : certificateNonAuthority r

theorem implementation_to_logic_transfer
    (r : Realization)
    (hFaithful : FaithfulRealization r)
    (s : Sequent)
    (hAccept : r.accepts s) :
    ∃ k, Derivable k s := by
  refine ⟨r.kernel, ?_⟩
  exact derives_implies_derivable r.kernel
    (stripGateCertificates (r.replayDerivation s))
    s
    (hFaithful.cert s hAccept)

end QEDFV
