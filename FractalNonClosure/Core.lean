import Std

/-!
# Fractal non-closure, abstract core

This file deliberately avoids measure theory and fractal geometry at the first
pass. It formalizes only the structural distinction the essay needs:

* terminal closure: an orbit settles to one element;
* cyclical closure: an orbit eventually repeats with a positive period;
* open instance: neither terminal nor cyclical closure occurs at the instance
  level;
* law closure: the observed orbit closes or converges to an invariant law
  state in a factor system one level up;
* nondegeneracy: the factor supplies the collapse condition that keeps
  law-level closure informative for the intended domain.

The intended later bridge is to instantiate the base system with scenery or
renormalization dynamics and the factor system with a measure-theoretic law
space. In that instantiation, `Degenerate` should become something substantive
such as "Dirac measure." At this abstract level, nondegeneracy is supplied as
structure and can be fixed by declaration; the file marks that deferral rather
than pretending the measure-theoretic content is already present. Finite
terminal closure remains available as `EventuallyConstantTo`, but law closure
is not restricted to that case.

The abstract layer is bracketed from both sides. `TerminalReading.onePointCalibration`
shows the target shape can be satisfied by the one-point reading. `LatchReading`
shows it is also satisfiable with retained distinction: a non-terminal reading law-closes
an open orbit while separating the initial state from every later state.
-/

namespace FractalNonClosure

/-- A system with one distinguished operation, read as one step of zoom,
renormalization, probing, or any other operation whose closure behavior is at
issue. -/
structure RenormSystem where
  State : Type
  step : State -> State

namespace RenormSystem

variable (R : RenormSystem)

/-- The forward orbit under repeated application of the operation. -/
def orbit (x : R.State) : Nat -> R.State
  | 0 => x
  | n + 1 => R.step (orbit x n)

/-- Orbit addition: running `m + n` steps is running `m`, then `n`. -/
theorem orbit_add (x : R.State) :
    forall m n, R.orbit x (m + n) = R.orbit (R.orbit x m) n
  | m, 0 => by
    simp [orbit]
  | m, n + 1 => by
    simp [orbit, orbit_add x m n]

/-- Data witnessing that the orbit has closed to one element after some finite
stage. -/
structure ElementClosure (x : R.State) where
  N : Nat
  closed : forall n, N <= n -> R.orbit x n = R.orbit x N

/-- The orbit has closed to one element after some finite stage. -/
def ElementClosed (x : R.State) : Prop :=
  Nonempty (R.ElementClosure x)

/-- Finite-stage terminal closure to a named limiting state. This is one
possible closure relation that a factor can use as its `ClosesTo` relation. -/
def EventuallyConstantTo (x y : R.State) : Prop :=
  exists c : R.ElementClosure x, R.orbit x c.N = y

/-- A finite-stage terminal limit is invariant under the step operation. -/
theorem eventuallyConstantTo_invariant {x y : R.State}
    (h : R.EventuallyConstantTo x y) : R.step y = y := by
  rcases h with ⟨c, hy⟩
  calc
    R.step y = R.step (R.orbit x c.N) := by rw [← hy]
    _ = R.orbit x (c.N + 1) := by simp [orbit]
    _ = R.orbit x c.N := c.closed (c.N + 1) (by omega)
    _ = y := hy

/-- Eventual positive-period recurrence. -/
def PeriodicFrom (x : R.State) (p : Nat) : Prop :=
  0 < p /\ exists N, forall n, N <= n -> R.orbit x (n + p) = R.orbit x n

/-- The orbit has closed as a finite return pattern. -/
def OrbitClosed (x : R.State) : Prop :=
  exists p, R.PeriodicFrom x p

/-- The instance remains open under the operation: it neither settles to an
element nor to a finite return pattern. This is not yet fractal-like; pure
escape to infinity satisfies this predicate too. -/
def InstanceOpen (x : R.State) : Prop :=
  Not (R.ElementClosed x) /\ Not (R.OrbitClosed x)

/-- Element closure is a special case of orbit closure, with period 1. -/
theorem elementClosed_orbitClosed {x : R.State} :
    R.ElementClosed x -> R.OrbitClosed x := by
  intro h
  rcases h with ⟨c⟩
  refine ⟨1, ?_⟩
  constructor
  · omega
  refine ⟨c.N, ?_⟩
  intro n hn
  calc
    R.orbit x (n + 1) = R.orbit x c.N := c.closed (n + 1) (by omega)
    _ = R.orbit x n := (c.closed n hn).symm

/-- If a deterministic orbit ever repeats a state, it is eventually periodic. -/
theorem repeat_orbitClosed {x : R.State}
    (h : exists m n, m < n /\ R.orbit x m = R.orbit x n) :
    R.OrbitClosed x := by
  rcases h with ⟨m, n, hmn, heq⟩
  let p := n - m
  have hp : 0 < p := by omega
  have hn : n = m + p := by omega
  refine ⟨p, ?_⟩
  constructor
  · exact hp
  refine ⟨m, ?_⟩
  intro k hk
  let t := k - m
  have hk_eq : k = m + t := by omega
  have hkp_eq : k + p = n + t := by omega
  calc
    R.orbit x (k + p) = R.orbit x (n + t) := by rw [hkp_eq]
    _ = R.orbit (R.orbit x n) t := R.orbit_add x n t
    _ = R.orbit (R.orbit x m) t := by rw [← heq]
    _ = R.orbit x (m + t) := (R.orbit_add x m t).symm
    _ = R.orbit x k := by rw [hk_eq]

/-- An instance-open orbit has no repeated state. Finite state spaces supply a
repeat by pigeonhole, so the omitted finite-space corollary is exactly that
standard step. -/
theorem instanceOpen_no_repeat {x : R.State} :
    R.InstanceOpen x ->
      Not (exists m n, m < n /\ R.orbit x m = R.orbit x n) := by
  intro h hopen
  exact h.2 (R.repeat_orbitClosed hopen)

end RenormSystem

/-- A factor system records a second level at which the base dynamics can be
observed. `commute` says observation respects the chosen operation.

`ClosesTo` is deliberately supplied by the factor. It is the factor's
law-level closure or convergence relation: eventual constancy, metric
convergence, distributional convergence, or whatever the domain can defend. It
is therefore also a deferral point: if a factor uses the universal relation as
its closure relation, law closure becomes automatic once an invariant
nondegenerate law state is available.

`Degenerate` is also supplied by the factor. In the later scenery-flow
instantiation it should be mathematical, e.g. Dirac-ness of a limiting measure.
At this abstract level, one-point factors or declared-nondegenerate factors are possible;
that is a deferral point, not content already proved. -/
structure Factor (R : RenormSystem) where
  law : RenormSystem
  obs : R.State -> law.State
  commute : forall x, obs (R.step x) = law.step (obs x)
  ClosesTo : law.State -> law.State -> Prop
  Degenerate : law.State -> Prop

namespace Factor

variable {R : RenormSystem} (F : Factor R)

/-- Observation commutes with the full forward orbit. -/
theorem obs_orbit (x : R.State) :
    forall n, F.obs (R.orbit x n) = F.law.orbit (F.obs x) n
  | 0 => rfl
  | n + 1 => by
    simp [RenormSystem.orbit, F.commute, obs_orbit x n]

/-- Law-level closure: the observed orbit closes or converges, according to
the factor's own closure relation, to an invariant law state that is not
degenerate. This is "closure changes level" made literal: the base instance may
stay open while its image closes one level up. -/
structure LawClosure (x : R.State) where
  limit : F.law.State
  closes : F.ClosesTo (F.obs x) limit
  invariant : F.law.step limit = limit
  nondegenerate : Not (F.Degenerate limit)

/-- The base orbit admits a nondegenerate invariant limit in the factor. -/
def LawClosed (x : R.State) : Prop :=
  Nonempty (F.LawClosure x)

/-- Law closure supplies an invariant, nondegenerate law state reached according
to the factor's closure relation. -/
theorem lawClosed_limit {x : R.State} :
    F.LawClosed x ->
      exists y : F.law.State,
        F.ClosesTo (F.obs x) y /\
          F.law.step y = y /\
            Not (F.Degenerate y) := by
  intro h
  rcases h with ⟨c⟩
  exact ⟨c.limit, c.closes, c.invariant, c.nondegenerate⟩

/-- Universal-closure calibration: if the factor's closure relation relates
every law state to every law state, then any invariant nondegenerate law state
law-closes every observed base state. This names the second declaration point:
`ClosesTo` has to be supplied by the domain just as `Degenerate` does. -/
theorem lawClosed_of_universal_closesTo
    (hclose : forall a b : F.law.State, F.ClosesTo a b)
    {y : F.law.State}
    (hinv : F.law.step y = y)
    (hnon : Not (F.Degenerate y))
    (x : R.State) :
    F.LawClosed x := by
  exact ⟨{
    limit := y
    closes := hclose (F.obs x) y
    invariant := hinv
    nondegenerate := hnon
  }⟩

/-- A local collapse witness: two distinct base states are identified by the
reading. This names what a factor loses, without treating readings as ordered by
a generic preservation grade. -/
def CollapsesPair (a b : R.State) : Prop :=
  a ≠ b /\ F.obs a = F.obs b

/-- The abstract target shape: the base instance is open, but an observed
nondegenerate law closes one level up. This is intentionally broader than
fractal geometry. It packages the three tasks from the paper: base closure is
not attained, a law-level closure relation supplies an invariant limit, and
the supplied collapse condition is not crossed. -/
structure OpenWithLawClosure (x : R.State) : Prop where
  instance_open : R.InstanceOpen x
  law_closed : F.LawClosed x

/-- An `OpenWithLawClosure` point is not terminally closed at the base level. -/
theorem openWithLawClosure_not_elementClosed {x : R.State} :
    F.OpenWithLawClosure x -> Not (R.ElementClosed x) := by
  intro h
  exact h.instance_open.1

/-- An `OpenWithLawClosure` point is not cyclically closed at the base level. -/
theorem openWithLawClosure_not_orbitClosed {x : R.State} :
    F.OpenWithLawClosure x -> Not (R.OrbitClosed x) := by
  intro h
  exact h.instance_open.2

/-- An `OpenWithLawClosure` point is law-closed one level up. -/
theorem openWithLawClosure_lawClosed {x : R.State} :
    F.OpenWithLawClosure x -> F.LawClosed x := by
  intro h
  exact h.law_closed

/-- An `OpenWithLawClosure` point supplies the paper's three formal tasks:
unattained base closure, witnessed law-level closure, and nondegeneracy of the
closed law state. -/
theorem openWithLawClosure_three_tasks {x : R.State} :
    F.OpenWithLawClosure x ->
      Not (R.ElementClosed x) /\
        Not (R.OrbitClosed x) /\
          exists y : F.law.State,
            F.ClosesTo (F.obs x) y /\
              F.law.step y = y /\
                Not (F.Degenerate y) := by
  intro h
  rcases h.law_closed with ⟨lc⟩
  refine ⟨h.instance_open.1, ?_⟩
  refine ⟨h.instance_open.2, ?_⟩
  exact ⟨lc.limit, lc.closes, lc.invariant, lc.nondegenerate⟩

end Factor

/-! ## One-point calibration -/

/-- The one-point target for the terminal reading. -/
inductive One where
  | star

/-- The one-point dynamics. Every state has already closed here. -/
abbrev OnePointSystem : RenormSystem where
  State := One
  step := fun _ => One.star

namespace TerminalReading

/-- The terminal factor from any system: observe every base state as the single
point. This factor commutes with every base motion because there is no
distinction left for the factor to violate. -/
def factor (R : RenormSystem) (Degenerate : One -> Prop) : Factor R where
  law := OnePointSystem
  obs := fun _ => One.star
  commute := by
    intro x
    rfl
  ClosesTo := fun _ y => y = One.star
  Degenerate := Degenerate

/-- In the bare signature, the one-point system is terminal: there is exactly
one coalgebra map into it. This is the structural source of the terminal-reading
calibration. -/
theorem unique_map_to_one (R : RenormSystem) :
    exists obs : R.State -> One,
      (forall x, obs (R.step x) = OnePointSystem.step (obs x)) /\
        forall obs' : R.State -> One,
          (forall x, obs' (R.step x) = OnePointSystem.step (obs' x)) ->
            obs' = obs := by
  refine ⟨fun _ => One.star, ?_, ?_⟩
  · intro x
    rfl
  · intro obs _
    funext x
    cases obs x
    rfl

theorem orbit_star (n : Nat) :
    OnePointSystem.orbit One.star n = One.star := by
  induction n with
  | zero => rfl
  | succ n _ =>
    simp [RenormSystem.orbit, OnePointSystem]

def elementClosure (x : One) :
    OnePointSystem.ElementClosure x := by
  refine ⟨0, ?_⟩
  intro n _
  cases x
  simp [RenormSystem.orbit, orbit_star]

/-- If the sole point is declared nondegenerate, the terminal factor law-closes
every base state. This is the calibration: commutation certifies lawfulness,
not retention of any base distinction. -/
theorem factor_lawClosed (R : RenormSystem) {Degenerate : One -> Prop}
    (hnon : Not (Degenerate One.star)) (x : R.State) :
    (factor R Degenerate).LawClosed x := by
  exact ⟨{
    limit := One.star
    closes := rfl
    invariant := rfl
    nondegenerate := hnon
  }⟩

/-- One-point calibration: every base system and every base state admits a
law-closed factor if the one-point reading is allowed and its sole point is
declared nondegenerate. -/
theorem onePointCalibration (R : RenormSystem) (x : R.State) :
    exists F : Factor R, F.LawClosed x := by
  refine ⟨factor R (fun _ => False), ?_⟩
  exact factor_lawClosed R (by intro h; cases h) x

/-- The terminal factor identifies every pair of base states. -/
theorem obs_eq (R : RenormSystem) {Degenerate : One -> Prop}
    (a b : R.State) :
    (factor R Degenerate).obs a = (factor R Degenerate).obs b := by
  rfl

/-- Whenever the base has a real distinction, the terminal factor collapses it. -/
theorem collapsesPair_of_distinct {R : RenormSystem} {Degenerate : One -> Prop}
    {a b : R.State} (h : a ≠ b) :
    (factor R Degenerate).CollapsesPair a b := by
  exact ⟨h, rfl⟩

/-- With two distinct base states, the terminal reading can be lawful,
law-closed, and still collapse the distinction between those states. -/
theorem lawful_closed_collapsing_of_distinct {R : RenormSystem}
    {a b : R.State} (h : a ≠ b) :
    exists F : Factor R,
      F.LawClosed a /\ F.LawClosed b /\ F.CollapsesPair a b := by
  refine ⟨factor R (fun _ => False), ?_, ?_, ?_⟩
  · exact factor_lawClosed R (by intro hfalse; cases hfalse) a
  · exact factor_lawClosed R (by intro hfalse; cases hfalse) b
  · exact collapsesPair_of_distinct (R := R) (Degenerate := fun _ => False) h

end TerminalReading

/-! ## Small witnesses and non-witnesses -/

/-- A constant system: terminally closed after one step. -/
abbrev ConstantSystem : RenormSystem where
  State := Bool
  step := fun _ => false

namespace Constant

theorem elementClosed (b : Bool) : ConstantSystem.ElementClosed b := by
  refine ⟨⟨1, ?_⟩⟩
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
    simp [RenormSystem.orbit, ConstantSystem]

end Constant

/-- A two-state blinker: cyclically closed but not terminally closed. -/
abbrev BlinkerSystem : RenormSystem where
  State := Bool
  step := fun b => !b

namespace Blinker

theorem succ_ne (b : Bool) (n : Nat) :
    BlinkerSystem.orbit b (n + 1) ≠ BlinkerSystem.orbit b n := by
  simp [RenormSystem.orbit, BlinkerSystem]

theorem period_two (b : Bool) :
    forall n, BlinkerSystem.orbit b (n + 2) = BlinkerSystem.orbit b n
  | 0 => by
    cases b <;> rfl
  | n + 1 => by
    change
      BlinkerSystem.step (BlinkerSystem.orbit b (n + 2)) =
        BlinkerSystem.step (BlinkerSystem.orbit b n)
    rw [period_two b n]

theorem orbitClosed (b : Bool) : BlinkerSystem.OrbitClosed b := by
  refine ⟨2, ?_⟩
  constructor
  · omega
  refine ⟨0, ?_⟩
  intro n _
  exact period_two b n

theorem not_elementClosed (b : Bool) : Not (BlinkerSystem.ElementClosed b) := by
  intro h
  rcases h with ⟨c⟩
  exact succ_ne b c.N (c.closed (c.N + 1) (by omega))

theorem cyclical_not_terminal (b : Bool) :
    BlinkerSystem.OrbitClosed b /\ Not (BlinkerSystem.ElementClosed b) :=
  ⟨orbitClosed b, not_elementClosed b⟩

end Blinker

/-- Pure escape to infinity. This is instance-open, but by itself it does not
supply a law-level reading. It is the concrete witness that the earlier
predicate-law design was insensitive to retention. -/
abbrev NatSuccSystem : RenormSystem where
  State := Nat
  step := Nat.succ

namespace NatSucc

theorem orbit_zero (n : Nat) : NatSuccSystem.orbit 0 n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [RenormSystem.orbit, NatSuccSystem, ih]

theorem not_elementClosed_zero : Not (NatSuccSystem.ElementClosed 0) := by
  intro h
  rcases h with ⟨c⟩
  have hstep := c.closed (c.N + 1) (by omega)
  rw [orbit_zero, orbit_zero] at hstep
  have hlt : c.N < c.N + 1 := by omega
  rw [hstep] at hlt
  exact Nat.lt_irrefl c.N hlt

theorem not_orbitClosed_zero : Not (NatSuccSystem.OrbitClosed 0) := by
  intro h
  rcases h with ⟨p, hp_pos, N, hper⟩
  have hperN := hper N (by omega)
  rw [orbit_zero, orbit_zero] at hperN
  have hlt : N < N + p := Nat.lt_add_of_pos_right hp_pos
  rw [hperN] at hlt
  exact Nat.lt_irrefl N hlt

theorem instanceOpen_zero : NatSuccSystem.InstanceOpen 0 :=
  ⟨not_elementClosed_zero, not_orbitClosed_zero⟩

/-- The one-point calibration witness: pure escape to infinity satisfies
`OpenWithLawClosure` if the terminal one-point factor is declared
nondegenerate. This is not a positive fractal example; it is the theorem that
the abstract core is still intentionally insufficient until a substantive
emitting/scenery instantiation supplies nondegeneracy. -/
theorem onePoint_factor_openWithLawClosure_zero :
    exists F : Factor NatSuccSystem, F.OpenWithLawClosure 0 := by
  refine ⟨TerminalReading.factor NatSuccSystem (fun _ => False), ?_⟩
  constructor
  · exact instanceOpen_zero
  · exact TerminalReading.factor_lawClosed NatSuccSystem
      (by intro h; cases h) 0

end NatSucc

/-! ## A non-terminal witness -/

/-- A two-state latch: every step lands on `true` and stays there. -/
abbrev LatchSystem : RenormSystem where
  State := Bool
  step := fun _ => true

namespace LatchReading

/-- Observe a natural number as the fact that at least one step has occurred.
This reading compresses almost everything, as a law-level reading must, but it
is not the terminal reading: it separates the initial state from every later
state. -/
def factor : Factor NatSuccSystem where
  law := LatchSystem
  obs := fun n => match n with
    | 0 => false
    | _ + 1 => true
  commute := by
    intro x
    rfl
  ClosesTo := LatchSystem.EventuallyConstantTo
  Degenerate := fun b => b = false

/-- The latch element-closes from any state after one step. -/
def elementClosure (b : Bool) : LatchSystem.ElementClosure b where
  N := 1
  closed := by
    intro n hn
    cases n with
    | zero => omega
    | succ n => simp [RenormSystem.orbit, LatchSystem]

/-- Every latch state is eventually constantly `true`. -/
theorem eventuallyConstantTo_true (b : Bool) :
    LatchSystem.EventuallyConstantTo b true := by
  refine ⟨elementClosure b, ?_⟩
  simp [elementClosure, RenormSystem.orbit, LatchSystem]

/-- The latch factor law-closes every base state: the observed orbit is
eventually constantly `true`, which is invariant and, in this reading,
nondegenerate. -/
theorem factor_lawClosed (x : Nat) : factor.LawClosed x :=
  ⟨{ limit := true
     closes := eventuallyConstantTo_true (factor.obs x)
     invariant := rfl
     nondegenerate := fun h => Bool.noConfusion h }⟩

/-- Pure escape to infinity satisfies `OpenWithLawClosure` under the latch
reading. This is still an abstract witness, not a fractal: the latch law is thin, and
nondegeneracy is still supplied by the factor. What it adds over the one-point
terminal example is that the reading is not the one-point reading, its closure
relation is genuine eventual constancy in the law system, and a base
distinction survives the compression. -/
theorem openWithLawClosure_zero : factor.OpenWithLawClosure 0 :=
  ⟨NatSucc.instanceOpen_zero, factor_lawClosed 0⟩

/-- The latch reading separates the initial state from every later state. -/
theorem not_collapsesPair_zero_succ (n : Nat) :
    Not (factor.CollapsesPair 0 (n + 1)) := by
  intro h
  exact Bool.noConfusion h.2

/-- The latch reading still compresses: all positive states are identified.
Loss is constitutive of a law-level reading; the question is which
distinctions survive. -/
theorem collapsesPair_one_two : factor.CollapsesPair 1 2 :=
  ⟨by decide, rfl⟩

/-- The counterpart of the one-point calibration theorem: the target shape is satisfiable
without the terminal reading. An instance-open base admits a lawful,
law-closed factor that retains a base distinction. -/
theorem openWithLawClosure_without_terminal_reading :
    exists F : Factor NatSuccSystem,
      F.OpenWithLawClosure 0 /\ Not (F.CollapsesPair 0 1) :=
  ⟨factor, openWithLawClosure_zero, not_collapsesPair_zero_succ 0⟩

end LatchReading

end FractalNonClosure
