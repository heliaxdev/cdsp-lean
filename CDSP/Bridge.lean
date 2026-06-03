import CDSP.MultiDomain
import mlda.Section4

/-!
# CDSP — The bridge: reliable-broadcast totality discharges atomic cross-domain sync

This is the payoff of the port. Oraclizer's cross-domain model (now in
`CDSP/`) carries one **unproven** assumption: that `lock → update → unlock` is
atomic across all connected domains (`FORMAL_MODEL_MAPPING.md:174`). The claim
of this work is that this assumption is *not* an axiom one must take on faith —
it is exactly the **Totality** guarantee of a heterogeneous reliable-broadcast
protocol under Byzantine faults, which mlda proves as
`Proposition_4_2_14.t : ⊨[μ] (◇ₑ [deliver, v]ₑ →ₑ □ₑ [deliver, v]ₑ)`.

## What is and isn't mechanized here

The two formalisms live in different worlds:

* mlda Section 4 is **semitopological** and **three-valued** (`𝐭 / 𝐟 / 𝐛`),
  with modalities `◇ₑ` ("somewhere": at some point of the semitopology) and
  `□ₑ` ("everywhere"). Faults are first-class (`𝐛`).
* Oraclizer/CDSP is a **deterministic partial-`δ`** state machine replicated
  over a finite domain set, with no fault values.

So the correspondence is a *paper-level* projection rendered in Lean, not a
mechanical import of one proof into the other. The honest way to encode this is:

1. Abstract the broadcast modalities to their CDSP projection over the set of
   domains holding an asset: `◇` ↦ "∃ a connected domain", `□` ↦ "∀ connected
   domains". (`Diamond` / `Box` below.)
2. State Totality at that projected level as `TotalityHolds` — the interface
   the broadcast layer is *assumed to supply* (and which mlda's
   `Proposition_4_2_14.t` discharges in its own model).
3. Prove, with **no new assumptions**, that
   (a) Totality lifts a single-domain delivery to all domains
       (`broadcast_discharges_atomic_sync`), and
   (b) the CDSP `syncAll` primitive actually *realizes* the `Box`
       (all-domains-agree) conclusion, via the ported
       `cross_domain_consistency` (`syncAll_realizes_box`).

Step (3) is genuine Lean. The seam between `TotalityHolds` and mlda's modal
`Proposition_4_2_14.t` (step 1–2) is the documented cross-formalism interface;
`#check` at the bottom witnesses that the mlda theorem it abstracts is real and
in scope.
-/

namespace CDSP

namespace Bridge

variable {D S A I : Type*}

/-- Asset `aid` has been delivered/synchronized to state `s'` in domain `d`
under post-state `post`. The CDSP analogue of mlda's atomic proposition
`[deliver, v]ₑ` localized at a point. -/
def Delivered (post : D → I → Option S) (aid : I) (s' : S) (d : D) : Prop :=
  post d aid = some s'

/-- CDSP projection of mlda's `◇ₑ` ("somewhere"): the predicate holds at *some*
domain connected to `aid`. -/
def Diamond (M : MultiDomain D S A I) (aid : I) (P : D → Prop) : Prop :=
  ∃ d ∈ M.connectedDomains aid, P d

/-- CDSP projection of mlda's `□ₑ` ("everywhere"): the predicate holds at *every*
domain connected to `aid`. -/
def Box (M : MultiDomain D S A I) (aid : I) (P : D → Prop) : Prop :=
  ∀ d ∈ M.connectedDomains aid, P d

/-- The **Totality interface**, projected to CDSP: `◇ → □`. This is the exact
shape of mlda's `Proposition_4_2_14.t` (`◇ₑ [deliver,v]ₑ →ₑ □ₑ [deliver,v]ₑ`)
once its modalities are read over the domain set. The bridge *assumes the
broadcast layer supplies this* — and mlda is what proves it can. -/
def TotalityHolds (M : MultiDomain D S A I) (aid : I) (P : D → Prop) : Prop :=
  Diamond M aid P → Box M aid P

/-- **The bridge, abstract half.** Given Totality (from reliable broadcast) and
a single witnessing connected domain where the asset is delivered, *every*
connected domain has it delivered. This is the all-or-nothing atomicity that
Oraclizer assumes — here derived, not postulated. -/
theorem broadcast_discharges_atomic_sync
    {M : MultiDomain D S A I} {aid : I} {P : D → Prop}
    (tot : TotalityHolds M aid P)
    (witness : Diamond M aid P) :
    Box M aid P :=
  tot witness

/-- **The bridge, concrete half.** The CDSP `syncAll` primitive *itself* realizes
the `Box` conclusion: after an atomic sync, every connected domain reflects the
new state. This is the ported `cross_domain_consistency` repackaged as the
`Box`/everywhere modality — showing CDSP's own machinery already produces what
Totality promises. -/
theorem syncAll_realizes_box
    {M : MultiDomain D S A I}
    {source : D} {aid : I} {s s' : S} {action : A}
    {ds' : D → I → Option S}
    (hstate : M.domainState source aid = some s)
    (htrans : M.sm.transition s action = some s')
    (hsync : M.syncAll source action aid M.domainState = some ds') :
    Box M aid (Delivered ds' aid s') :=
  fun _d hd => M.cross_domain_consistency hstate htrans hsync hd

-- Smoke test: the mlda theorem this bridge abstracts is real and in scope —
-- heterogeneous reliable-broadcast **Totality**, `◇ₑ [deliver,v]ₑ → □ₑ [deliver,v]ₑ`.
-- `TotalityHolds` above is its CDSP projection over the domain set.
#check @Proposition_4_2_14.t

end Bridge

end CDSP
