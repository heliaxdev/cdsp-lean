import CDSP.StateMachine

/-!
# CDSP — Cross-domain state preservation (homomorphism)

Port of the Isabelle `state_preservation` and `symmetric_state_preservation`
locales (`State_Preservation.thy:110-254`).

`state_preservation` connects two state machines by a `(state_map, action_map)`
homomorphism satisfying **naturality**: synchronizing after a local transition
equals transitioning after synchronization. `sequential_preservation` lifts this
to whole action sequences — the structural guarantee underpinning cross-domain
sync.

`symmetric_state_preservation` adds inverse maps with roundtrip laws, giving
injectivity of `state_map` (no information loss under synchronization).
-/

namespace CDSP

variable {S A T B : Type*}

/-- Port of Isabelle locale `state_preservation` (`State_Preservation.thy:110`).
Two state machines connected by `stateMap`/`actionMap`; the `assumes` become
proof fields. -/
structure StatePreservation (S A T B : Type*) where
  source : StateMachine S A
  target : StateMachine T B
  stateMap : S → T
  actionMap : A → B
  state_map_well_defined : ∀ {s}, s ∈ source.states → stateMap s ∈ target.states
  action_map_well_defined : ∀ {a}, a ∈ source.actions → actionMap a ∈ target.actions
  terminal_preservation : ∀ {s}, s ∈ source.terminal → stateMap s ∈ target.terminal
  /-- The naturality / homomorphism condition. -/
  naturality : ∀ {s a s'}, s ∈ source.states → a ∈ source.actions →
    source.transition s a = some s' →
    target.transition (stateMap s) (actionMap a) = some (stateMap s')
  naturality_none : ∀ {s a}, s ∈ source.states → a ∈ source.actions →
    source.transition s a = none →
    target.transition (stateMap s) (actionMap a) = none

namespace StatePreservation

variable (P : StatePreservation S A T B)

/-- Isabelle `sequential_preservation` (`State_Preservation.thy:139`): preservation
extends from single actions to whole sequences. -/
theorem sequential_preservation {s s' : S} {as : List A}
    (hs : s ∈ P.source.states)
    (ha : ∀ a ∈ as, a ∈ P.source.actions)
    (h : P.source.applyActions s as = some s') :
    P.target.applyActions (P.stateMap s) (as.map P.actionMap) = some (P.stateMap s') := by
  induction as generalizing s with
  | nil =>
    simp only [StateMachine.applyActions, Option.some.injEq] at h
    subst h
    simp [StateMachine.applyActions]
  | cons a as ih =>
    simp only [StateMachine.applyActions] at h
    split at h
    · simp at h
    · next s_mid hstep =>
      have mapped : P.target.transition (P.stateMap s) (P.actionMap a)
          = some (P.stateMap s_mid) := P.naturality hs (ha a (by simp)) hstep
      have hmid : s_mid ∈ P.source.states :=
        P.source.transition_closed hs (ha a (by simp)) hstep
      simp only [List.map_cons, StateMachine.applyActions, mapped]
      exact ih hmid (fun b hb => ha b (List.mem_cons_of_mem a hb)) h

/-- Isabelle `sequential_preservation_none` (`State_Preservation.thy:165`). -/
theorem sequential_preservation_none {s : S} {as : List A}
    (hs : s ∈ P.source.states)
    (ha : ∀ a ∈ as, a ∈ P.source.actions)
    (h : P.source.applyActions s as = none) :
    P.target.applyActions (P.stateMap s) (as.map P.actionMap) = none := by
  induction as generalizing s with
  | nil => simp [StateMachine.applyActions] at h
  | cons a as ih =>
    simp only [StateMachine.applyActions] at h
    simp only [List.map_cons, StateMachine.applyActions]
    cases hstep : P.source.transition s a with
    | none =>
      have hnone : P.target.transition (P.stateMap s) (P.actionMap a) = none :=
        P.naturality_none hs (ha a (by simp)) hstep
      simp [hnone]
    | some s_mid =>
      have mapped : P.target.transition (P.stateMap s) (P.actionMap a)
          = some (P.stateMap s_mid) := P.naturality hs (ha a (by simp)) hstep
      have hmid : s_mid ∈ P.source.states :=
        P.source.transition_closed hs (ha a (by simp)) hstep
      simp only [hstep] at h
      simp only [mapped]
      exact ih hmid (fun b hb => ha b (List.mem_cons_of_mem a hb)) h

/-- Isabelle `terminal_image_absorbing` (`State_Preservation.thy:198`). -/
theorem terminal_image_absorbing {s : S} {a : A}
    (hs : s ∈ P.source.terminal) (ha : a ∈ P.source.actions) :
    P.target.transition (P.stateMap s) (P.actionMap a) = none :=
  P.naturality_none (P.source.terminal_subset hs) ha (P.source.terminal_absorbing hs ha)

end StatePreservation

/-- Port of Isabelle locale `symmetric_state_preservation`
(`State_Preservation.thy:221`). We keep the meaningful content: the forward
preservation plus inverse maps with roundtrip laws (giving `state_map`
injectivity). The backward direction's own naturality — a second
`state_preservation` instance in Isabelle — is omitted as no theorem in the
locale uses it. -/
structure SymmetricStatePreservation (S A T B : Type*) where
  forward : StatePreservation S A T B
  stateMapInv : T → S
  actionMapInv : B → A
  roundtrip_state_src : ∀ {s}, s ∈ forward.source.states →
    stateMapInv (forward.stateMap s) = s
  roundtrip_state_tgt : ∀ {t}, t ∈ forward.target.states →
    forward.stateMap (stateMapInv t) = t
  roundtrip_action_src : ∀ {a}, a ∈ forward.source.actions →
    actionMapInv (forward.actionMap a) = a
  roundtrip_action_tgt : ∀ {b}, b ∈ forward.target.actions →
    forward.actionMap (actionMapInv b) = b

namespace SymmetricStatePreservation

variable (P : SymmetricStatePreservation S A T B)

/-- Isabelle `state_map_injective` (`State_Preservation.thy:250`): under roundtrip
maps, `state_map` is injective on the source state set (no information loss). -/
theorem state_map_injective {s₁ s₂ : S}
    (h₁ : s₁ ∈ P.forward.source.states) (h₂ : s₂ ∈ P.forward.source.states)
    (heq : P.forward.stateMap s₁ = P.forward.stateMap s₂) : s₁ = s₂ := by
  have e₁ := P.roundtrip_state_src h₁
  have e₂ := P.roundtrip_state_src h₂
  rw [← e₁, ← e₂, heq]

end SymmetricStatePreservation

end CDSP
