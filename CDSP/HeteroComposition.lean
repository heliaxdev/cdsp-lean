import CDSP.MldaInstance
import mlda.Section4

/-!
# CDSP — Composition of heterogeneous consensus regimes (ethresearch Q2)

The ethresearch post "Mechanized proofs for atomic cross-domain state
synchronization" lists as open question **Q2**: *composition of heterogeneous
consensus regimes* — how to guarantee a cross-domain synchronization when
different domains run **different** consensus mechanisms.

mlda already supplies heterogeneity *within* one broadcast: a
`Model BBSig Pnt V` carries a semitopology `μ.S` (heterogeneous quorums =
heterogeneous trust), and Bracha correctness needs only that model's own
`Twined3` (3-way quorum intersection). This file lifts that to **composition
across domains**: a family of broadcast models, **one per domain, each with its
own semitopology**, glued into a single CDSP `MultiDomain`.

## What is mechanized

`HeteroBroadcast Dom Pnt V` bundles, per domain `d : Dom`, an independent mlda
model `model d` with its own `ThyBB (model d)` and `Twined3 (model d).S`.
Different `d` ⇒ different semitopology ⇒ different trust/consensus regime.

`hetero_composition`: if **each** domain reaches a genuine (strictly-true) local
delivery of `v`, then the composed multi-domain synchronizes everywhere
(`connectedDomains () = univ`). The proof discharges each domain with **its own**
`totality_projected` instance — i.e. each heterogeneous regime self-certifies.

## The Q2 payoff, and what stays open

The decisive point is visible in the **types**: `composed` / `hetero_composition`
require only the *per-domain* `Twined3 (model d).S`. There is **no global
`Twined3`**, no shared quorum across the union of all participants. That is
exactly what "composition of heterogeneous consensus regimes" needs: domains
agree internally under their own trust assumptions, and the cross-domain glue
imposes no common trust model.

What is **not** here: the inter-domain *coupling* that makes one domain's
delivery trigger the others (so that a single source event synchronizes all).
That coupling is Oraclizer's `syncAll` / the ported `cross_domain_consistency`
(state is decided once and copied), or a real network — `hetero_composition`
instead takes a per-domain trigger as hypothesis and shows the regimes compose
*given* each fires. Wiring the source trigger through `syncAll` is the next step.
-/

open Three
open scoped Three.Atom
open scoped Three.Function
open scoped FinSemitopology
open FinSemitopology
open scoped Definition_3_1_1
open Definition_3_1_1
open scoped Notation
open Notation
open scoped Denotation
open Denotation

attribute [local instance] Classical.propDecidable

namespace CDSP
namespace HeteroComposition

variable
  {Dom Pnt V : Type}
  [Fintype Pnt] [DecidableEq Pnt] [Inhabited Pnt]
  [Fintype V] [DecidableEq V]

/-- A family of mlda Bracha-broadcast models indexed by domain. Each domain `d`
carries its **own** model — hence its own semitopology `(model d).S`, i.e. its
own heterogeneous trust/consensus regime — together with that model's broadcast
theory and 3-way quorum-intersection property. -/
structure HeteroBroadcast (Dom Pnt V : Type)
    [Fintype Pnt] [DecidableEq Pnt] [Inhabited Pnt] [Fintype V] [DecidableEq V] where
  model : Dom → Model BBSig Pnt V
  thy : (d : Dom) → ThyBB (model d)
  twined : (d : Dom) → Twined3 (model d).S

/-- Domain `d` has (validly) delivered `v` everywhere within its own broadcast. -/
def locallyDelivered (H : HeteroBroadcast Dom Pnt V) (v : V) (d : Dom) : Prop :=
  ∀ q, 𝐛 ≤ (H.model d).ς deliver q v

/-- Each domain self-certifies: a genuine (strictly-true) local delivery, run
through **that domain's own** totality, yields local agreement. Heterogeneous —
`d` and `d'` use different models, hence different semitopologies. -/
theorem local_totality (H : HeteroBroadcast Dom Pnt V) (v : V) (d : Dom)
    (h : ∃ p, (H.model d).ς deliver p v = 𝐭) : locallyDelivered H v d := by
  haveI := H.thy d
  haveI := H.twined d
  exact MldaInstance.totality_projected (H.model d) v h

/-- The composed cross-domain structure: domains are the index set, the lone
asset is the broadcast instance, and a domain holds it iff it locally delivered
`v`. Only the single value `v` is ever stored, so `consistent_init` is immediate.
The carrier state machine is degenerate — the broadcast lives in `domainState`. -/
noncomputable def composed [Fintype Dom]
    (H : HeteroBroadcast Dom Pnt V) (v : V) : MultiDomain Dom V Unit Unit where
  domains := Set.univ
  sm := MldaInstance.carrier
  domainState := fun d _ => if locallyDelivered H v d then some v else none
  fin_domains := Set.finite_univ
  consistent_init := by
    intro d₁ d₂ aid s₁ s₂ _ _ h1 h2
    have e1 : s₁ = v := by split at h1 <;> simp_all
    have e2 : s₂ = v := by split at h2 <;> simp_all
    rw [e1, e2]

/-- **Q2 payoff.** If every (heterogeneous) domain reaches a genuine local
delivery of `v`, the composition synchronizes everywhere: `connectedDomains`
saturates to the full domain set. Each domain is discharged by its **own**
`totality_projected`; the statement requires only per-domain `Twined3`, never a
global quorum across domains. -/
theorem hetero_composition [Fintype Dom]
    (H : HeteroBroadcast Dom Pnt V) (v : V)
    (trigger : ∀ d, ∃ p, (H.model d).ς deliver p v = 𝐭) :
    (composed H v).connectedDomains () = Set.univ := by
  ext d
  simp only [Set.mem_univ, iff_true]
  refine ⟨Set.mem_univ d, ?_⟩
  show (composed H v).domainState d () ≠ none
  have hd : locallyDelivered H v d := local_totality H v d (trigger d)
  simp only [composed, if_pos hd]
  exact Option.some_ne_none v

/-! ## Coupling the source trigger through `syncAll`

`hetero_composition` assumes *every* domain independently triggers. The atomic
cross-domain story is stronger: **one** source event should propagate to all
domains. That coupling is exactly Oraclizer's `syncAll` (decide once at the
source, copy everywhere) — already ported as `MultiDomain.cross_domain_consistency`.

The degenerate `carrier` cannot host `syncAll` (its transition is always
`none`). `overwriteMD` is the non-degenerate carrier for the sync scenario: the
asset is already shared across all domains (every domain holds it at `s₀`, so
`connectedDomains = univ`), and the transition overwrites the asset to the
action's value. -/

/-- The asset is shared across all domains at initial value `s₀`; the sync action
carries the new value and the transition overwrites to it. -/
def overwriteMD (Dom V : Type) [Fintype Dom] [Fintype V] [DecidableEq V] (s₀ : V) :
    MultiDomain Dom V V Unit where
  domains := Set.univ
  sm :=
    { states := Set.univ
      actions := Set.univ
      transition := fun _ a => some a
      terminal := ∅
      finite_states := Set.finite_univ
      finite_actions := Set.finite_univ
      terminal_subset := fun x _ => Set.mem_univ x
      terminal_absorbing := by intro s a hs _; simp at hs
      transition_closed := fun _ _ _ => Set.mem_univ _
      transition_domain := by intro s a hs; simp at hs }
  domainState := fun _ _ => some s₀
  fin_domains := Set.finite_univ
  consistent_init := by
    intro d₁ d₂ aid s₁ s₂ _ _ h1 h2
    have e1 : s₁ = s₀ := by simpa using h1.symm
    have e2 : s₂ = s₀ := by simpa using h2.symm
    rw [e1, e2]

/-- Every domain holds the shared asset in `overwriteMD`. -/
theorem overwriteMD_connected [Fintype Dom] (s₀ : V) (d : Dom) :
    d ∈ (overwriteMD Dom V s₀).connectedDomains () :=
  ⟨Set.mem_univ d, Option.some_ne_none s₀⟩

/-- **End-to-end atomic cross-domain sync, from one source event.** The source
domain's *own* heterogeneous broadcast certifies value `v` (left conjunct, via
`totality_projected` — `v` is genuinely delivered, not Byzantine); a single
`syncAll` initiated at that source then atomically propagates `v` to **every**
domain (right conjunct, via the ported `cross_domain_consistency`). One genuine
source event ⟹ all domains hold the certified value. -/
theorem source_broadcast_drives_sync [Fintype Dom]
    (H : HeteroBroadcast Dom Pnt V) (s₀ v : V) (source : Dom)
    (trigger : ∃ p, (H.model source).ς deliver p v = 𝐭)
    {ds' : Dom → Unit → Option V}
    (hsync : (overwriteMD Dom V s₀).syncAll source v ()
      (overwriteMD Dom V s₀).domainState = some ds') :
    locallyDelivered H v source ∧ ∀ d, ds' d () = some v := by
  refine ⟨local_totality H v source trigger, fun d => ?_⟩
  have hstate : (overwriteMD Dom V s₀).domainState source () = some s₀ := rfl
  have htrans : (overwriteMD Dom V s₀).sm.transition s₀ v = some v := rfl
  exact (overwriteMD Dom V s₀).cross_domain_consistency hstate htrans hsync
    (overwriteMD_connected s₀ d)

end HeteroComposition
end CDSP
