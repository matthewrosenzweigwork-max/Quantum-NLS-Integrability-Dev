# Verification and errata

- The principal dependency set comprises 192 accepted result nodes and 47 realized definitions. This count is not a count of Lean files or of separate theorems in the mathematical report.
- The recorded clean project rebuild and independent Lean kernel replay passed for 2,906 modules. Twenty-one additional sources, delivered in three supplements, were separately compiled and replayed according to the recorded supplement checks. These were not part of the 2,906 count.
- The final Lake Comparator run compared 34 selected roots from pinned challenge and solution exports, checked their allowed axioms, and passed under the default Lean kernel. The official Comparator was from Lean 4.35.0; the exports were generated with Lean 4.34.1. Its optional operating-system sandbox wrapper was disabled, and the tool emitted its corresponding trust warning. This is not a sandboxed Comparator receipt and does not claim use of an additional kernel.
- The portable configuration pins Mathlib to a Git revision rather than a local path. A new project build using that configuration passed on 25 November 2026 with Lean 4.34.1 and pinned dependency artifacts, producing all 2,927 project modules. The Lean source inventory matches the previously verified inventory; changes within those sources are confined to comments. The new build is separate from the earlier independent replay and Comparator checks.
- A targeted check against the new build confirmed the full form of the headline theorem, including the order of the schedule and occupation-gauge witnesses, and verified the transitive axioms of seven declarations: the two headline forms, the four statement-comparison lemmas, and the main specification. The only axioms reported were `propext`, `Classical.choice`, and `Quot.sound`.
- The main theorem does not assert that the limiting generator is nontrivial. Some external-input correspondence is qualified by the source conventions and classes of solutions; do not use this formalization to infer stronger uniqueness or broader scope.

## Checks embedded in the source

The main theorem module retains its executable closure guard. It checks the binders and permitted axioms of the two headline declarations, tests for required dependencies in their closure, and verifies that the existential theorem uses the named-witness proof. The module also retains the six historically recorded `#print axioms` commands. These checks are part of the source. They are distinct from the historical independent kernel replay and the 34-root Comparator run.

## Errata in the external literature

No correction to a published result is asserted here. The qualifications above describe the scope of this formalization.
