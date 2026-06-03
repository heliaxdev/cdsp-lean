import CDSP.StateMachine

/-!
# CDSP — Multi-domain state preservation

Port of the Isabelle `multi_domain_preservation` locale
(`State_Preservation.thy:274-368`): N domains sharing one abstract state
machine, with the all-or-nothing `sync_all` and its two correctness theorems
(`cross_domain_consistency`, `sync_isolation`).

This is the layer where the bridge claim lives: `sync_all` is atomic *by
construction* (decide once at the source, propagate or no-op everywhere), and
`consistent_init` forces all domains to pre-agree on asset state — which is why
the partial transition `δ` never produces a Byzantine split, and why the bridge
primitive is mlda **Section 4 (reliable broadcast)** rather than Crusader.
-/

attribute [local instance] Classical.propDecidable

namespace CDSP

variable {D S A I : Type*}

/-- Port of Isabelle locale `multi_domain_preservation`
(`State_Preservation.thy:274`). The locale's `sm` assumption (there is a
`state_machine` on `states/actions/transition/terminal`) is captured by
bundling a `StateMachine S A`. -/
structure MultiDomain (D S A I : Type*) where
  domains : Set D
  sm : StateMachine S A
  /-- Current state of asset `aid` in domain `d`; `none` = domain does not hold it. -/
  domainState : D → I → Option S
  fin_domains : domains.Finite
  /-- All domains holding an asset agree on its state (`consistent_init`). -/
  consistent_init : ∀ {d₁ d₂ : D} {aid : I} {s₁ s₂ : S},
    d₁ ∈ domains → d₂ ∈ domains →
    domainState d₁ aid = some s₁ → domainState d₂ aid = some s₂ → s₁ = s₂

namespace MultiDomain

variable (M : MultiDomain D S A I)

/-- Which domains hold a given asset (`connected_domains`). -/
def connectedDomains (aid : I) : Set D :=
  {d ∈ M.domains | M.domainState d aid ≠ none}

/-- The global consensus state of an asset, well-defined by `consistent_init`
(`consensus_state`). -/
noncomputable def consensusState (aid : I) : Option S :=
  if h : (M.connectedDomains aid).Nonempty then M.domainState h.some aid else none

/-- Synchronize an action on an asset across all connected domains (`sync_all`):
decide once at the `source`, then either propagate the new state to every
connected domain or no-op everywhere. -/
noncomputable def syncAll (source : D) (action : A) (aid : I)
    (ds : D → I → Option S) : Option (D → I → Option S) :=
  match ds source aid with
  | none => none
  | some s =>
    match M.sm.transition s action with
    | none => none
    | some s' =>
      some fun d aid' =>
        if aid' = aid ∧ d ∈ M.connectedDomains aid then some s' else ds d aid'

/-- After `sync_all`, every connected domain reflects the new state
(`cross_domain_consistency`, `State_Preservation.thy:328`). -/
theorem cross_domain_consistency
    {source : D} {aid : I} {s s' : S} {action : A} {d : D}
    {ds' : D → I → Option S}
    (hstate : M.domainState source aid = some s)
    (htrans : M.sm.transition s action = some s')
    (hsync : M.syncAll source action aid M.domainState = some ds')
    (hd : d ∈ M.connectedDomains aid) :
    ds' d aid = some s' := by
  simp only [syncAll, hstate, htrans, Option.some.injEq] at hsync
  subst hsync
  simp [hd]

/-- `sync_all` does not affect other assets
(`sync_isolation`, `State_Preservation.thy:351`). -/
theorem sync_isolation
    {source : D} {aid aid' : I} {action : A} {d : D}
    {ds' : D → I → Option S}
    (hsync : M.syncAll source action aid M.domainState = some ds')
    (hne : aid' ≠ aid) :
    ds' d aid' = M.domainState d aid' := by
  simp only [syncAll] at hsync
  split at hsync
  · simp at hsync
  · split at hsync
    · simp at hsync
    · simp only [Option.some.injEq] at hsync
      subst hsync
      simp [hne]

end MultiDomain

end CDSP
