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

def gateChecked (t : TheoryState) : DerivationObj -> Prop
  | .leaf _ => True
  | .rule _ _ _ => True
  | .gate kind cert d _ => gateCertificateWellFormed t kind cert ∧ gateChecked t d

def gateFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s ->
    gateChecked r.kernel.T (r.replayDerivation s) ∧
    (∀ gc, gc ∈ r.replayCertificates s ->
      gateCertificateWellFormed r.kernel.T gc.fst gc.snd)

def stripGateCertificates : DerivationObj -> DerivationObj
  | .gate kind _ d s => .gate kind "" (stripGateCertificates d) s
  | d => d

theorem stripGateCertificates_preserves_derives_aux
    (k : KernelState) :
    ∀ d s, Derives k d s -> Derives k (stripGateCertificates d) s
  | .leaf _, s, h => by
      simpa [stripGateCertificates] using h
  | .rule _ _ _, s, h => by
      simpa [stripGateCertificates] using h
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
  exact ⟨r.kernel, hFaithful.rule s hAccept⟩

end QEDFV
