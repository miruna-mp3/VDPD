Project Description — Memcache.dfy

================================================================================
PART I: DAFNY LANGUAGE & VERIFICATION REFERENCE (v4.11.0)
================================================================================

1. Core Verification Philosophy
-------------------------------
Dafny is a verification-aware programming language where specifications are
first-class citizens. The tool pipeline is: parse → resolve → verify → compile.

Key principle: Dafny is SOUND but INCOMPLETE.
  • Sound: If verification succeeds, the program meets its specification
    (modulo bugs in Dafny/Z3 itself).
  • Incomplete: A verification failure does NOT mean the program is wrong—
    it may mean Dafny lacks the information to prove correctness.

Verification is MODULAR: each method/function is verified in isolation using
only the specifications (not bodies) of callees. This enables scalable proofs
but requires complete and accurate specifications.

2. Type System
--------------
2.1 Value Types (immutable, no heap identity)
  • Numeric: int, nat (int ≥ 0), real, ORDINAL, bvN (bitvectors)
  • Boolean: bool
  • Character: char
  • Collections: set<T>, iset<T>, multiset<T>, seq<T>, map<K,V>, imap<K,V>
  • Tuples: (T1, T2, ...) with positional destructors .0, .1, ...
  • Datatypes: inductive (finite) and coinductive (potentially infinite)

2.2 Reference Types (heap-allocated, identity matters)
  • class C { ... }           — mutable objects with fields and methods
  • trait T { ... }           — abstract interface; no constructors
  • array<T>, array2<T>, ...  — fixed-size heap arrays
  • Nullable variants: T? allows null; T (non-nullable) excludes null
  • object/object? — root trait for dynamic frames pattern

2.3 Type Definitions
  • Type synonym:   type T = ExistingType
  • Abstract type:  type T                    (opaque, may have members)
  • Subset type:    type T = x: Base | P(x) witness e
  • Newtype:        newtype T = x: Base | P(x) (distinct type identity)

2.4 Type Characteristics (constraints on type parameters)
  • T(==)   — equality supported
  • T(0)    — auto-initializable (has compilable default)
  • T(00)   — nonempty type
  • T(!new) — does not contain references

3. Specifications (Contracts)
-----------------------------
3.1 Method Specifications
  requires P       — precondition; must hold at call site
  ensures Q        — postcondition; guaranteed on return
  modifies S       — frame: set of objects method may modify
  decreases E      — termination metric (lexicographic tuple)

3.2 Function/Predicate Specifications
  requires P       — precondition
  ensures Q        — postcondition (often inferred from body)
  reads S          — frame: heap locations function may read
  decreases E      — termination metric

3.3 Loop Specifications
  invariant I      — must hold on entry AND after each iteration
  decreases E      — must decrease each iteration (proves termination)
  modifies S       — (optional) restricts loop's heap modifications

3.4 Multiple Clauses
  Multiple requires/ensures/invariant clauses are conjoined in order.
  Order matters: earlier clauses establish context for later ones.

4. Framing (reads/modifies)
---------------------------
Framing is CRITICAL for modular verification. Without frames, the verifier
cannot know what changes (or doesn't) across method calls.

4.1 modifies Clause (methods)
  • Lists objects whose fields may be mutated
  • Unlisted objects are guaranteed unchanged
  • Fresh objects (allocated by method) are implicitly modifiable

4.2 reads Clause (functions/predicates)
  • Lists objects whose fields the function may depend on
  • Required because functions must be deterministic
  • If reads is missing/incomplete, verification may fail or be unsound

4.3 Frame Expressions
  • Object:          o           — all fields of o
  • Specific field:  o`f         — only field f of o
  • Set of objects:  {o1, o2}    — all fields of all objects in set
  • Empty frame:     {}          — pure (no heap access)

4.4 Dynamic Frames Pattern
  Standard idiom for object-oriented verification:
  ```dafny
  class Node {
    ghost var Repr: set<object>   // representation set
    var data: int
    var next: Node?

    ghost predicate Valid()
      reads this, Repr
    {
      this in Repr &&
      (next != null ==> next in Repr && next.Repr <= Repr && this !in next.Repr && next.Valid())
    }
  }
  ```
  The Repr set tracks all objects "owned" by this object, enabling
  recursive validity predicates with proper framing.

5. Termination (decreases)
--------------------------
Dafny requires proofs that recursion and loops terminate.

5.1 Well-Founded Orders (built-in)
  • int/nat:     x < X && 0 <= X
  • bool:        false < true
  • set<T>:      proper subset
  • seq<T>:      proper prefix or element
  • datatype:    structural inclusion (subterm)
  • reference:   null < non-null
  • tuples:      lexicographic comparison

5.2 Decreases Clauses
  • Lexicographic: decreases a, b, c compares tuples left-to-right
  • Implicit ⊤ appended: allows mutual recursion patterns
  • Wildcard: decreases * allows non-termination (methods only)

5.3 Default Inference
  Dafny guesses decreases clauses (usually the parameters). Explicit
  clauses needed for complex patterns or mutual recursion.

6. Ghost vs Compiled Code
-------------------------
6.1 Ghost Elements
  • ghost var, ghost method, ghost function — erased at compile time
  • Used for specifications, proofs, and verification-only state
  • No runtime cost

6.2 Proof-Only Constructs
  • lemma — ghost method for proving properties
  • assert — runtime check (compiled) or proof hint (ghost context)
  • assume — dangerous: assumes truth without proof (emits warning)
  • reveal — makes opaque function body visible in scope

6.3 Ghost Inference
  Dafny automatically marks code as ghost when:
  • It appears in a ghost context
  • It uses ghost variables
  • It's only needed for verification

7. Datatypes and Pattern Matching
---------------------------------
7.1 Inductive Datatypes
  datatype List<T> = Nil | Cons(head: T, tail: List<T>)
  • Finite structures (well-founded)
  • Automatic discriminators: x.Nil?, x.Cons?
  • Automatic destructors: x.head, x.tail

7.2 Coinductive Datatypes
  codatatype Stream<T> = SCons(head: T, tail: Stream<T>)
  • Potentially infinite structures
  • Greatest fixpoint semantics
  • Require coinductive proofs (greatest lemmas)

7.3 Pattern Matching
  match x {
    case Nil => ...
    case Cons(h, t) => ...
  }

8. Quantifiers and Triggers
---------------------------
8.1 Syntax
  forall x :: P(x)           — universal
  exists x :: P(x)           — existential
  forall x | R(x) :: P(x)    — bounded by range predicate

8.2 Triggers
  Triggers control when quantifiers are instantiated by the SMT solver.
  • {:trigger f(x)} — explicit trigger
  • Dafny auto-infers triggers (usually function applications)

8.3 Common Issues
  • "no triggers found" — add helper function to create valid trigger
  • "selected trigger may loop" — trigger causes infinite instantiation
  • Missing instantiation — add seemingly-redundant assert to trigger

Example fix:
  // Bad: no trigger for arithmetic
  forall x :: x + 1 > x

  // Good: introduce helper function
  function Succ(x: int): int { x + 1 }
  forall x {:trigger Succ(x)} :: Succ(x) > x

9. Lemmas and Proof Techniques
------------------------------
9.1 Lemma Declaration
  lemma L(x: T)
    requires P(x)
    ensures Q(x)
  { /* proof body */ }

9.2 Using Lemmas
  • Call like a method: L(arg);
  • Calling introduces the postcondition as a known fact
  • Lemma bodies are ghost (erased at compile time)

9.3 Proof Patterns
  • Case split: if ... { } else { }
  • Induction: recursive lemma call on smaller argument
  • Calc statement: chain of equalities/inequalities
  • Forall statement: prove property for all values in range

9.4 Calc Statement
  calc {
    A;
  ==  // or <, >, <=, >=, ==>, <==, <==>
    B;
  ==  { Lemma(); }  // hint
    C;
  }
  // Proves A == C (or appropriate relation)

9.5 Forall Statement
  forall x | P(x)
    ensures Q(x)
  {
    // Proof that Q(x) holds for each x satisfying P(x)
    Lemma(x);
  }

10. Opaque Functions and Reveal
-------------------------------
10.1 Opacity
  • {:opaque} attribute hides function body from verifier by default
  • Improves verification performance by limiting proof search
  • Selective revealing when body is needed

10.2 Reveal Statement
  reveal F();           // makes F's body visible in current scope
  reveal F;             // alternative syntax

10.3 Opaque Blocks
  opaque {
    // Function bodies hidden within this block
  }

11. Common Verification Failures and Solutions
----------------------------------------------
11.1 "postcondition might not hold"
  • Missing loop invariant that establishes postcondition
  • Incomplete frame specification
  • Need intermediate assert to guide prover

11.2 "call may violate context's modifies clause"
  • Object not in modifies clause
  • Fresh objects need ensures fresh(x) to be modifiable by caller

11.3 "insufficient reads clause"
  • Function reads heap location not in reads clause
  • Add object to reads clause

11.4 "cannot prove termination"
  • decreases expression doesn't decrease
  • Need explicit decreases clause
  • For mutual recursion, use two-component decreases

11.5 "assertion might not hold"
  • Prover lacks information
  • Add lemma call or intermediate assertions
  • Check for arithmetic overflow or division by zero

11.6 Timeout / Resource exhaustion
  • Split into smaller methods/lemmas
  • Add {:fuel} to limit function unfolding
  • Use {:opaque} and selective reveal
  • Add {:split_here} assertions

12. Attributes Reference
------------------------
Declaration attributes:
  {:axiom}           — assume postcondition without proof (DANGEROUS)
  {:extern "name"}   — bind to external code
  {:opaque}          — hide function body by default
  {:fuel n}          — limit function unfolding depth
  {:induction x, y}  — specify induction variables
  {:autocontracts}   — auto-generate Valid/Repr boilerplate

Verification control:
  {:verify false}    — skip verification (DANGEROUS)
  {:only}            — verify only this assertion
  {:focus}           — focus verification on this
  {:split_here}      — split verification batch
  {:resource_limit}  — set solver resource limit
  {:timeLimit n}     — set verification timeout

13. Best Practices
------------------
13.1 Specification Design
  • Write preconditions that make ALL expressions well-formed
  • Use subset types to encode constraints at the type level
  • Expose allocation with ensures fresh(x)
  • Keep specifications as simple as possible

13.2 Verification Strategy
  • Start with strong postconditions, weaken if needed
  • Add invariants incrementally; verify after each addition
  • Use asserts as "checkpoints" to isolate failures
  • Extract complex proofs into separate lemmas

13.3 Performance
  • Limit quantifier complexity
  • Use {:opaque} for complex functions
  • Split large methods into smaller ones
  • Avoid deep recursion in specifications

================================================================================
PART II: MEMCACHE.DFY PROJECT DOCUMENTATION
================================================================================

Overview
--------
A verified, time-aware memcache model demonstrating Dafny best practices:
  • Layered module architecture
  • Abstraction function connecting concrete and abstract state
  • Full functional specifications with frame conditions
  • Proof lemmas for modular reasoning
  • Command parsing and execution pipeline

Architecture
------------
```
┌─────────────────────────────────────────────────────────────────┐
│                           Main                                   │
│                    (Demo / Entry Point)                          │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                       Commands Module                            │
│  • Command/Response datatypes                                    │
│  • Parsing pipeline (Split, ParseInt, ParseCommand)              │
│  • Execute: applies command to cache                             │
│  • ProcessCommand: parse → execute → format                      │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      CacheImpl Module                            │
│  • class Cache with store: map<Key, Entry>                       │
│  • ghost function view(now): abstract state                      │
│  • Methods: Get, Set, Add, Replace, Delete                       │
│  • Full specs: pre/post conditions + frame conditions            │
└─────────────────────────────────────────────────────────────────┘
                              │
              ┌───────────────┴───────────────┐
              ▼                               ▼
┌──────────────────────────┐    ┌──────────────────────────┐
│    Helpers Module        │    │   Abstraction Module     │
│  • mapRemove function    │    │  • setToSeq ghost fn     │
│  • Frame preservation    │    │  • MapHelper/Map ghost   │
│    lemmas                │    │  • isInMap/notInMap      │
│                          │    │    lemmas                │
└──────────────────────────┘    └──────────────────────────┘
              │                               │
              └───────────────┬───────────────┘
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                        Types Module                              │
│  • Key, Value, Time type aliases                                 │
│  • Entry datatype with val and exp (expiration)                  │
│  • Option<T> datatype                                            │
│  • isLive, keyLive, keyDead predicates                           │
└─────────────────────────────────────────────────────────────────┘
```

Module Details
--------------

1) Types Module
   Purpose: Define fundamental types and liveness predicates.

   Types:
     type Key = int
     type Value = int
     type Time = int
     datatype Entry = Entry(val: Value, exp: Time)
     datatype Option<T> = None | Some(value: T)

   Predicates:
     isLive(e, now)      — entry not expired: e.exp > now
     keyLive(store,k,now) — key exists and is live
     keyDead(store,k,now) — key missing or expired

2) Abstraction Module
   Purpose: Define the abstraction function from concrete to logical state.

   The abstraction function Map(store, now) projects:
     Concrete: map<Key, Entry>  →  Abstract: map<Key, Value>
   by filtering to only live (non-expired) entries.

   Ghost Functions:
     setToSeq(s)           — convert set to sequence (for iteration)
     MapHelper(store,keys,now) — recursive helper
     Map(store, now)       — main abstraction function

   Lemmas (connect concrete operations to abstract view):
     isInMap      — live key appears in abstract map
     isInMapHelper — recursive helper for isInMap
     notInMap     — dead/missing key absent from abstract map
     notInMapHelper — recursive helper for notInMap
     inMapIff     — biconditional: k in Map(store,now) <==> keyLive(store,k,now)

3) Helpers Module
   Purpose: Utility functions and frame-preservation lemmas.

   Functions:
     mapRemove(m, k) — remove key from map

   Lemmas (critical for modular verification):
     updateKeyOthersIntact — updating k preserves other keys in view
     removeKeyOthersIntact — removing k preserves other keys in view
     updateKey            — updated key appears in view with correct value
     removeKey            — removed key disappears from view

4) CacheImpl Module
   Purpose: Verified cache implementation with full specifications.

   Class Cache:
     var store: map<Key, Entry>     — concrete state

     ghost function view(now): map<Key, Value>
       reads this
       = Map(store, now)            — abstraction function

   Constructor:
     ensures store == map[]
     ensures forall now :: view(now) == map[]

   Method Specifications Pattern:
   Each method specifies BOTH concrete and abstract behavior:

   Get(k, now) returns Option<Value>
     // Abstract behavior
     ensures result.Some? <==> k in view(now)
     ensures result.Some? ==> result.value == view(now)[k]
     // Concrete behavior
     ensures result.Some? ==> k in store && result.value == store[k].val
     // Frame: nothing changes
     ensures store == old(store)

   Set(k, v, ttl, now)
     requires ttl > 0
     modifies this
     // Abstract: key appears with value; others preserved
     ensures k in view(now) && view(now)[k] == v
     ensures forall other :: other != k ==> (other in view(now)) == (other in old(view(now)))
     // Concrete: entry stored; others preserved
     ensures k in store && store[k] == Entry(v, now+ttl)
     ensures forall other :: other != k ==> (other in store) == (other in old(store))

   Add(k, v, ttl, now) returns bool
     // Only succeeds if key not already live
     ensures success <==> k !in old(view(now))

   Replace(k, v, ttl, now) returns bool
     // Only succeeds if key already live
     ensures success <==> k in old(view(now))

   Delete(k, now) returns bool
     // Returns whether key was live; key removed regardless
     ensures found <==> k in old(view(now))
     ensures k !in view(now)

5) Commands Module
   Purpose: Command parsing, execution, and response formatting.

   Command Datatype:
     CmdGet(key)              — retrieve value
     CmdSet(key, value, ttl)  — store with expiration
     CmdAdd(key, value, ttl)  — store only if not exists
     CmdReplace(key,value,ttl)— update only if exists
     CmdDelete(key)           — remove entry
     CmdInvalid               — parse error

   Response Datatype:
     RespValue(value) | RespNotFound | RespStored |
     RespNotStored | RespDeleted | RespError(msg)

   Parsing Pipeline:
     Split(s)         — tokenize on spaces
     ParseInt(s)      — parse integer with sign
     ParseCommand(s)  — string → Command

   Validation:
     predicate ValidCmd(cmd) — ensures TTL > 0 where required

   Execution:
     method Execute(cache, cmd, now) returns Response
       requires ValidCmd(cmd)
       modifies cache
       ensures cmd.CmdInvalid? ==> resp.RespError?
       ensures cmd.CmdSet? ==> resp == RespStored
       ensures cmd.CmdDelete? ==> resp == RespDeleted

   Lemma:
     ParseCommandValid(input) — proves parser always returns ValidCmd

   Composition:
     ProcessCommand(cache, input, now) — parse → execute → format

6) CommandTests Module
   Purpose: Verification-time tests.

   TestExecuteCommands — exercises all command types
   TestParseValid      — verifies parser produces valid commands

7) Main Method
   Purpose: Runtime demonstration.
   Executes sample commands and prints responses.

Verification Techniques Used
----------------------------
1. Abstraction Function
   • Separates "what the cache looks like" (view) from "how it's stored" (store)
   • Enables specification in terms of logical behavior

2. Frame Conditions
   • Every method specifies exactly what changes and what's preserved
   • Uses forall quantification for "all other keys unchanged"

3. Lemma-Based Proofs
   • Lemmas factor out reusable proof steps
   • Called inline where their postconditions are needed

4. Ghost State
   • view() is a ghost function (not compiled)
   • Repr patterns could be added for more complex heap structures

5. Datatype-Based Error Handling
   • Option<T> for nullable results
   • Command/Response ADTs for type-safe command processing

Potential Extensions
--------------------
• Add TTL refresh on access (LRU behavior)
• Add capacity limits with eviction
• Add concurrent access with linearizability proofs
• Add persistence layer with crash consistency
• Add network protocol layer
