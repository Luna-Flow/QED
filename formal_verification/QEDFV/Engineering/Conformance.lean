import QEDFV.Conservativity.GlobalConservativity
import QEDFV.Engineering.RuleMapping

namespace QEDFV

structure PrimitiveInstance where
  ruleName : String
  target : Sequent
deriving Repr

structure Realization where
  kernel : KernelState
  accepts : Sequent -> Prop
  replayDerivation : Sequent -> DerivationObj
  replayPrimitiveInstances : Sequent -> List PrimitiveInstance
  replayPrimitiveTrace : Sequent -> List String
  replayExtensionSteps : Sequent -> List ExtensionStep
  replayCertificates : Sequent -> List (GateKind × String)

def ruleFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s -> Derivable r.kernel s

def replayFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s -> Derives r.kernel (r.replayDerivation s) s

def boundaryFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s -> OldLang r.kernel.T s

def scopeFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s -> ScopedWF r.kernel.S

mutual

def derivationRuleTrace : DerivationObj -> List String
  | .leaf _ => []
  | .rule r ds _ => r :: derivationRuleTraceList ds
  | .gate _ _ d _ => derivationRuleTrace d

def derivationRuleTraceList : List DerivationObj -> List String
  | [] => []
  | d :: ds => derivationRuleTrace d ++ derivationRuleTraceList ds

end

mutual

def derivationPrimitiveInstances : DerivationObj -> List PrimitiveInstance
  | .leaf _ => []
  | .rule r ds s =>
      { ruleName := r, target := s } :: derivationPrimitiveInstancesList ds
  | .gate _ _ d _ => derivationPrimitiveInstances d

def derivationPrimitiveInstancesList : List DerivationObj -> List PrimitiveInstance
  | [] => []
  | d :: ds =>
      derivationPrimitiveInstances d ++ derivationPrimitiveInstancesList ds

end

def primitiveInstanceNames (trace : List PrimitiveInstance) : List String :=
  trace.map (fun inst => inst.ruleName)

theorem primitiveInstanceNames_append
    (xs ys : List PrimitiveInstance) :
    primitiveInstanceNames (xs ++ ys) =
      primitiveInstanceNames xs ++ primitiveInstanceNames ys := by
  simp [primitiveInstanceNames, List.map_append]

mutual

theorem derivationRuleTrace_eq_instanceNames :
    ∀ d,
      derivationRuleTrace d =
        primitiveInstanceNames (derivationPrimitiveInstances d)
  | .leaf _ => by
      simp [derivationRuleTrace, derivationPrimitiveInstances, primitiveInstanceNames]
  | .rule r ds s => by
      simp [derivationRuleTrace, derivationPrimitiveInstances,
        derivationRuleTraceList_eq_instanceNamesList, primitiveInstanceNames]
  | .gate g cert d s => by
      simpa [derivationRuleTrace, derivationPrimitiveInstances] using
        derivationRuleTrace_eq_instanceNames d

theorem derivationRuleTraceList_eq_instanceNamesList :
    ∀ ds,
      derivationRuleTraceList ds =
        primitiveInstanceNames (derivationPrimitiveInstancesList ds)
  | [] => by
      simp [derivationRuleTraceList, derivationPrimitiveInstancesList, primitiveInstanceNames]
  | d :: ds => by
      simp [derivationRuleTraceList, derivationPrimitiveInstancesList,
        derivationRuleTrace_eq_instanceNames, derivationRuleTraceList_eq_instanceNamesList,
        primitiveInstanceNames_append]

end

def primitiveRuleName (name : String) : Prop :=
  ∃ entry, entry ∈ ruleToImplementationMapping ∧ entry.ruleName = name

def primitiveInstanceTrace (trace : List PrimitiveInstance) : Prop :=
  ∀ inst, inst ∈ trace -> primitiveRuleName inst.ruleName

def replayTraceFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s ->
    derivationPrimitiveInstances (r.replayDerivation s) = r.replayPrimitiveInstances s ∧
    primitiveInstanceNames (r.replayPrimitiveInstances s) = r.replayPrimitiveTrace s ∧
    primitiveInstanceTrace (r.replayPrimitiveInstances s)

def gateCertificateWellFormed (_t : TheoryState) (_kind : GateKind) (cert : String) : Prop :=
  cert ≠ ""

mutual

def derivationGateTrace : DerivationObj -> List (GateKind × String)
  | .leaf _ => []
  | .rule _ ds _ => derivationGateTraceList ds
  | .gate kind cert d _ => (kind, cert) :: derivationGateTrace d

def derivationGateTraceList : List DerivationObj -> List (GateKind × String)
  | [] => []
  | d :: ds => derivationGateTrace d ++ derivationGateTraceList ds

end

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
    derivationGateTrace (r.replayDerivation s) = r.replayCertificates s

mutual

theorem gateChecked_trace_wf
    (t : TheoryState) :
    ∀ d gc, gateChecked t d -> gc ∈ derivationGateTrace d ->
      gateCertificateWellFormed t gc.fst gc.snd
  | .leaf _, gc, _hCheck, hMem => by
      cases hMem
  | .rule _ ds _, gc, hCheck, hMem => by
      exact gateCheckedList_trace_wf t ds gc hCheck hMem
  | .gate kind cert d _, gc, hCheck, hMem => by
      rcases hCheck with ⟨hCert, hChild⟩
      simp [derivationGateTrace] at hMem
      rcases hMem with hHead | hTail
      · cases hHead
        exact hCert
      · exact gateChecked_trace_wf t d gc hChild hTail

theorem gateCheckedList_trace_wf
    (t : TheoryState) :
    ∀ ds gc, gateCheckedList t ds -> gc ∈ derivationGateTraceList ds ->
      gateCertificateWellFormed t gc.fst gc.snd
  | [], gc, hCheck, hMem => by
      cases hMem
  | d :: ds, gc, hCheck, hMem => by
      rcases hCheck with ⟨hHead, hTail⟩
      simp [derivationGateTraceList] at hMem
      rcases hMem with hHeadMem | hTailMem
      · exact gateChecked_trace_wf t d gc hHead hHeadMem
      · exact gateCheckedList_trace_wf t ds gc hTail hTailMem

end

theorem gateFidelity_replay_certificate_wf
    (r : Realization)
    (hGate : gateFidelity r) :
    ∀ s gc, r.accepts s -> gc ∈ r.replayCertificates s ->
      gateCertificateWellFormed r.kernel.T gc.fst gc.snd := by
  intro s gc hAccept hMem
  rcases hGate s hAccept with ⟨hChecked, hTraceEq⟩
  have hMemTrace : gc ∈ derivationGateTrace (r.replayDerivation s) := by
    simpa [hTraceEq] using hMem
  exact gateChecked_trace_wf r.kernel.T (r.replayDerivation s) gc hChecked hMemTrace

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

def conservativeReplayFidelity (r : Realization) : Prop :=
  ∀ s, r.accepts s ->
    Derives r.kernel (eraseSequence (r.replayExtensionSteps s) (r.replayDerivation s)) s

theorem certificate_non_authority_from_replay
    (r : Realization)
    (hReplay : replayFidelity r) :
    certificateNonAuthority r := by
  intro s hAccept
  exact stripGateCertificates_preserves_derives r.kernel (r.replayDerivation s) s
    (hReplay s hAccept)

theorem conservative_replay_from_replay_boundary
    (r : Realization)
    (hReplay : replayFidelity r)
    (hBoundary : boundaryFidelity r) :
    conservativeReplayFidelity r := by
  intro s hAccept
  exact global_conservativity_finite_step
    r.kernel
    r.kernel.T
    (r.replayExtensionSteps s)
    (r.replayDerivation s)
    s
    (hReplay s hAccept)
    (hBoundary s hAccept)

structure FaithfulRealization (r : Realization) : Prop where
  rule : ruleFidelity r
  replay : replayFidelity r
  boundary : boundaryFidelity r
  scope : scopeFidelity r
  trace : replayTraceFidelity r
  gate : gateFidelity r
  cert : certificateNonAuthority r

theorem faithful_realization_conservative_replay
    (r : Realization)
    (hFaithful : FaithfulRealization r) :
    conservativeReplayFidelity r := by
  exact conservative_replay_from_replay_boundary r hFaithful.replay hFaithful.boundary

theorem implementation_to_logic_transfer_with_trace
    (r : Realization)
    (hFaithful : FaithfulRealization r)
    (s : Sequent)
    (hAccept : r.accepts s) :
    ∃ k, Derivable k s ∧
      derivationPrimitiveInstances (r.replayDerivation s) = r.replayPrimitiveInstances s ∧
      primitiveInstanceNames (r.replayPrimitiveInstances s) = r.replayPrimitiveTrace s ∧
      primitiveInstanceTrace (r.replayPrimitiveInstances s) := by
  rcases hFaithful.trace s hAccept with ⟨hInstEq, hNameEq, hPrimTrace⟩
  have hCert : certificateNonAuthority r := by
    exact certificate_non_authority_from_replay r hFaithful.replay
  refine ⟨r.kernel, ?_, hInstEq, hNameEq, hPrimTrace⟩
  exact derives_implies_derivable r.kernel
    (stripGateCertificates (r.replayDerivation s))
    s
    (hCert s hAccept)

theorem implementation_to_logic_transfer_with_rule_trace
    (r : Realization)
    (hFaithful : FaithfulRealization r)
    (s : Sequent)
    (hAccept : r.accepts s) :
    ∃ k, Derivable k s ∧
      derivationRuleTrace (r.replayDerivation s) = r.replayPrimitiveTrace s ∧
      primitiveInstanceTrace (r.replayPrimitiveInstances s) := by
  rcases implementation_to_logic_transfer_with_trace r hFaithful s hAccept with
    ⟨k, hDerivable, hInstEq, hNameEq, hPrimInst⟩
  have hRuleTraceEq : derivationRuleTrace (r.replayDerivation s) = r.replayPrimitiveTrace s := by
    calc
      derivationRuleTrace (r.replayDerivation s)
          = primitiveInstanceNames (derivationPrimitiveInstances (r.replayDerivation s)) := by
              simpa using derivationRuleTrace_eq_instanceNames (r.replayDerivation s)
      _ = primitiveInstanceNames (r.replayPrimitiveInstances s) := by
            simp [hInstEq]
      _ = r.replayPrimitiveTrace s := hNameEq
  exact ⟨k, hDerivable, hRuleTraceEq, hPrimInst⟩

theorem implementation_to_logic_transfer
    (r : Realization)
    (hFaithful : FaithfulRealization r)
    (s : Sequent)
    (hAccept : r.accepts s) :
    ∃ k, Derivable k s := by
  rcases implementation_to_logic_transfer_with_trace r hFaithful s hAccept with
    ⟨k, hDerivable, _hInstEq, _hNameEq, _hTrace⟩
  exact ⟨k, hDerivable⟩

end QEDFV
