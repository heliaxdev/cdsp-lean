import CDSP.MultiDomain
import mlda.Section4

/-!
# CDSP — Instantiating `MultiDomain` from an actual mlda broadcast run

`CDSP/Bridge.lean` states the totality correspondence *abstractly*: it defines a
`TotalityHolds` interface and assumes the broadcast layer supplies it. This file
closes part of that seam by **constructing a concrete `MultiDomain` out of a real
mlda Bracha-broadcast model** `μ : Model BBSig Pnt V` and deriving the
all-or-nothing property from mlda's *proven* totality
(`Proposition_4_2_14.t`) — no new assumptions, no `sorry`.

## The honest shape (Byzantine three-valued logic)

mlda's totality is `⊨[μ] (◇ₑ [deliver,v]ₑ →ₑ □ₑ [deliver,v]ₑ)`. Two facts about
the three-valued semantics make the projection asymmetric, and we keep that
asymmetry rather than papering over it:

* `valid` means `𝐛 ≤ ⟦·⟧` (true-or-Byzantine), but mlda's implication `→ₑ`
  fires only on a *strictly true* antecedent (`Lemmas.valid_impl`: the premise
  is `⟦φ⟧ = 𝐭`). So the usable hypothesis is "delivery is **strictly true**
  somewhere", i.e. `∃ p, μ.ς deliver p v = 𝐭`.
* The conclusion `□ₑ` then only gives validity (`𝐛 ≤ ⟦deliver⟧`) everywhere.

`totality_projected` below is exactly that meta-level implication, extracted
from `Proposition_4_2_14.t`. The asymmetry is meaningful: a *Byzantine-only*
delivery does not force global delivery — only a genuine (true) delivery does.

## The instance

`mldaMultiDomain μ v` models one broadcast of value `v` as a CDSP multi-domain:
participants are domains (`D := Pnt`), the single asset is the broadcast
instance (`I := Unit`), and a domain "holds" the asset iff it has delivered `v`
(`domainState p () = some v` iff `𝐛 ≤ μ.ς deliver p v`). Because only the one
value `v` is ever stored, `consistent_init` is immediate (no appeal to mlda's
consistency theorem is needed for a single fixed value). The state machine is
the degenerate carrier (no actions) — broadcast lives in `domainState`, not in a
`δ`-transition, consistent with the "reliable broadcast, not a state machine"
caveat.

`mldaMultiDomain_connected_eq_univ` is the payoff: once `v` is genuinely
delivered *somewhere*, **every** domain holds it — `connectedDomains` saturates
to all domains. That is the atomic all-or-nothing sync, now a theorem about a
concrete mlda-derived structure rather than an assumed interface.
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

namespace CDSP
namespace MldaInstance

variable
  {Pnt V : Type}
  [Fintype Pnt] [DecidableEq Pnt] [Inhabited Pnt]
  [Fintype V] [DecidableEq V]

/-- **The seam, closed.** mlda's proven totality (`Proposition_4_2_14.t`),
projected to the point set: if value `v` is delivered with strict truth at *some*
participant, then *every* participant delivers it (at least validly). This is a
real Lean proof that consumes the mlda theorem — the all-or-nothing skeleton the
Oraclizer model leaves as an assumption. -/
theorem totality_projected
    (μ : Model BBSig Pnt V) [ThyBB μ] [Twined3 μ.S] (v : V)
    (h : ∃ p, μ.ς deliver p v = 𝐭) :
    ∀ q, 𝐛 ≤ μ.ς deliver q v := by
  have tot := Proposition_4_2_14.t (μ := μ) (v := v) (default : Pnt)
  rw [Lemmas.valid_impl] at tot
  have hdia : ⟦◇ₑ [deliver, v]ₑ⟧ᵈ μ (default : Pnt) = 𝐭 := by
    rw [Lemmas.denotation_somewhere, somewhere_true]
    obtain ⟨q, hq⟩ := h
    exact ⟨q, by rw [Lemmas.denotation_atom]; exact hq⟩
  have hbox := tot hdia
  rw [← valid_iff_everywhere] at hbox
  intro q
  have hq := hbox q
  simpa [Lemmas.denotation_atom] using hq

/-- The degenerate carrier state machine: states are all values, no actions, no
terminals. The broadcast content lives in `domainState`, not here. -/
def carrier : StateMachine V Unit where
  states := Set.univ
  actions := ∅
  transition := fun _ _ => none
  terminal := ∅
  finite_states := Set.finite_univ
  finite_actions := Set.finite_empty
  terminal_subset := fun x _ => Set.mem_univ x
  terminal_absorbing := fun _ _ => rfl
  transition_closed := by intro s a s' _ _ h; simp at h
  transition_domain := fun _ => rfl

/-- A single mlda broadcast of value `v`, viewed as a CDSP multi-domain:
participants are domains, the broadcast instance is the lone asset, and a domain
holds it exactly when it has (validly) delivered `v`. -/
noncomputable def mldaMultiDomain
    (μ : Model BBSig Pnt V) (v : V) : MultiDomain Pnt V Unit Unit where
  domains := Set.univ
  sm := carrier
  domainState := fun p _ => if 𝐛 ≤ μ.ς deliver p v then some v else none
  fin_domains := Set.finite_univ
  consistent_init := by
    intro d₁ d₂ aid s₁ s₂ _ _ h1 h2
    have e1 : s₁ = v := by split at h1 <;> simp_all
    have e2 : s₂ = v := by split at h2 <;> simp_all
    rw [e1, e2]

/-- **Payoff.** For the concrete mlda-derived multi-domain, a single genuine
(strictly-true) delivery of `v` forces every domain to hold the asset:
`connectedDomains` saturates to the full domain set. Atomic all-or-nothing sync,
derived from mlda totality via `totality_projected`. -/
theorem mldaMultiDomain_connected_eq_univ
    (μ : Model BBSig Pnt V) [ThyBB μ] [Twined3 μ.S] (v : V)
    (h : ∃ p, μ.ς deliver p v = 𝐭) :
    (mldaMultiDomain μ v).connectedDomains () = Set.univ := by
  have hall := totality_projected μ v h
  ext p
  simp only [Set.mem_univ, iff_true]
  refine ⟨Set.mem_univ p, ?_⟩
  show (mldaMultiDomain μ v).domainState p () ≠ none
  simp only [mldaMultiDomain, if_pos (hall p)]
  exact Option.some_ne_none v

end MldaInstance
end CDSP
