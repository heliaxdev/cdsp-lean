import mlda.Section4

/-!
# CDSP — Cross-Domain State Preservation, ported to Lean 4

This library is the bridge between the Oraclizer cross-domain atomicity model
(Isabelle/HOL, `Oraclizer/formal-verification`,
`Cross_Domain_State_Preservation/State_Preservation.thy`) and Gabbay's
heterogeneous reliable-broadcast theory as mechanized in `mlda` (Section 4,
Bracha broadcast: validity / consistency / integrity / **totality**).

The bridge target is Oraclizer's *unproven* atomic-sync assumption
("lock → update → unlock is atomic", `FORMAL_MODEL_MAPPING.md:174`). mlda's
Totality `◇[deliver,v] → □[deliver,v]` (`mlda.Section4`,
`Proposition_4_2_14.t`) is the all-or-nothing skeleton that discharges it under
Byzantine faults.

This file ports the Isabelle `state_machine` locale
(`State_Preservation.thy:44-83`) — the carrier on which the multi-domain
synchronization and the broadcast correspondence are stated. Bridge-minimal
scope: `state_machine` + (later) `multi_domain_preservation`.

`mlda/` itself is left untouched; everything new lives under `CDSP/`.
-/

namespace CDSP

universe u v

/-- Port of Isabelle locale `state_machine` (`State_Preservation.thy:44`).

The locale's `fixes` become structure fields and its `assumes` become
proof-field obligations. Determinism is inherent (the transition is a
function, not a relation), exactly as in the Isabelle comment at line 57. -/
structure StateMachine (S : Type u) (A : Type v) where
  states : Set S
  actions : Set A
  /-- Partial transition: `none` = abort / undefined (Isabelle `'s option`). -/
  transition : S → A → Option S
  terminal : Set S
  finite_states : states.Finite
  finite_actions : actions.Finite
  terminal_subset : terminal ⊆ states
  terminal_absorbing : ∀ {s a}, s ∈ terminal → a ∈ actions → transition s a = none
  transition_closed :
    ∀ {s a s'}, s ∈ states → a ∈ actions → transition s a = some s' → s' ∈ states
  transition_domain : ∀ {s a}, s ∉ states → transition s a = none

namespace StateMachine

variable {S : Type u} {A : Type v}

/-- Isabelle `transition_deterministic` (`State_Preservation.thy:59`). -/
theorem transition_deterministic (m : StateMachine S A) {s a s₁ s₂}
    (h₁ : m.transition s a = some s₁) (h₂ : m.transition s a = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-- Sequential composition of actions, partial, `none` on first failure.
Isabelle `apply_actions` (`State_Preservation.thy:65`). -/
def applyActions (m : StateMachine S A) (s : S) : List A → Option S
  | [] => some s
  | a :: as =>
    match m.transition s a with
    | none => none
    | some s' => m.applyActions s' as

/-- Isabelle `apply_actions_closed` (`State_Preservation.thy:71`).
First real port target — discharge before moving to `state_preservation`. -/
theorem applyActions_closed (m : StateMachine S A) {s s' : S} {as : List A}
    (hs : s ∈ m.states) (ha : ∀ a ∈ as, a ∈ m.actions)
    (h : m.applyActions s as = some s') : s' ∈ m.states := by
  induction as generalizing s with
  | nil =>
    simp only [applyActions, Option.some.injEq] at h
    exact h ▸ hs
  | cons a as ih =>
    simp only [applyActions] at h
    split at h
    · exact absurd h (by simp)
    · next s'' hta =>
      exact ih (m.transition_closed hs (ha a (by simp)) hta)
               (fun b hb => ha b (List.mem_cons_of_mem a hb)) h

end StateMachine

end CDSP
