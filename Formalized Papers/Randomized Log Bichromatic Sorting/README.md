# Randomized Log Bichromatic Sorting — formalization

Lean 4 (v4.35.0, Mathlib v4.35.0) formalization of the randomized-log
paper in [`Papers/`](Papers/):

- `randomized_log_final_draft.tex` — *From Log-Cubed to Log in Bichromatic Sorting*
  (randomized `O(H log N)`, optimal competitive ratio).

This is one of two separate paper formalizations. The deterministic
polylog paper is formalized separately in
[`../Deterministic Polylog Bichromatic Sorting/`](../Deterministic%20Polylog%20Bichromatic%20Sorting/).

## Status (randomized paper complete)

The statements below are formalized and *proved*: there is no
`sorry` anywhere in this project, and the main theorems depend
only on the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

| Paper result | Lean | File |
|---|---|---|
| Cost model, benchmark `H`, competitive ratio | `pairCost`, `benchmarkH`, `competitiveRatio` | `Formalization/RandomizedLog/Definitions.lean` |
| `H ≥ N − 1` | `benchmarkH_ge` — **proved** (`pairCost_ge_one`, `adjCost_cons_ge`) | `Definitions.lean` |
| Randomized main theorem (Thm 1) | `Randomized.spliceSort_main` — **proved**: there is a sorter (SpliceSort itself, `spliceSorter`) whose expected *total* cost is at most `100 * H * log₂ N` for all `α, β > 1`; `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound` | `Statements.lean`, `TotalCost.lean` |
| Benchmark is the cheapest proof (`prop:Hlower`) | `Randomized.benchmarkH_is_cheapest_proof` — **proved**: every determining set of comparisons costs at least `H` (`determining_cost_ge`), and the adjacent pairs of the sorted order are determining and cost exactly `H` (`adjGraph`, `graphCost_adjGraph`) | `HLower.lean` |
| Competitive ratio (p.2 definition) | `competitiveRatio` is the worst case over colourings of expected cost divided by `H`; `Randomized.spliceSort_competitiveRatio` — **proved** `≤ 100 log₂ N` | `Definitions.lean`, `Statements.lean` |
| Paper's random experiment | `Randomized.spliceSorter_expectedCost_eq_redPerm` — **proved**: the average over injective ranks of all elements equals the average over the uniform red permutation of the cost of the arrival order | `RedPerm.lean` |

Execution stage (`Trace.lean`, all `sorry`-free,
axiom-checked): the `Step` relation (the four operations with their
certificates) and `TraceFrom`; `step_invariant`, `step_mono`,
`step_flatten` (element provenance `flatten σ' ~ r :: flatten σ`);
`trace_invariant` — every trace state satisfies the full bundle with
`flatten σ ~ arrivals ++ flatten σ₀`; and the paper's
`lem:ordinaryrecord` for split incidences (`split_record`), proved by
the paper's own argument (earlier reds sit in runs before/after `C`,
hence outside `[min C, max C]`). The creator and activated-merger
cases are now proved as well (`creator_record`, `merger_record`, via
the separation key `record_key_of_separation`), with blue-run
refinement along steps and traces (`step_blue_refines`,
`trace_blue_refines`) and the founder property (`founder_record`,
`merger_founder`). Pre-split domination and the binary-search bound
are proved in `ScanCost.lean` (`presplit_domination`,
`searchCost_le : searchCost q ≤ log2 q + 1`, `total_searchCost_le`).
The monochromatic counting core is now proved in
`MonoCost.lean` (all `sorry`-free, axiom-checked):
`blueCost_le` (the `lem:bluecost` MergeSort count), `ownCost_le`
(the `lem:ownred` joiner count), `expected_threshold_le` (threshold
records at an endpoint are the `lem:records` records at that
endpoint, on both sides), and `foreign_count_le` (the
`lem:foreignred` count, conditional on the geometric inclusion of
foreign testers in threshold records). The geometric core of that
inclusion is now proved at the testing step (`threshold_record`,
`threshold_record_succ` in `Trace.lean`, axiom-checked):
a foreign red splitting the blue run adjacent to the tested red
run is a threshold record for that run's endpoint. Red runs never split is now proved (`step_red_run_grows`,
`trace_red_run_grows`, `final_red_run_of`, axiom-checked): the run
tested by a foreign red grows into a single all-red final run
containing it. The endpoint passage for foreign records is proved
in assembly form (`threshold_record_at_final`,
`threshold_record_succ_at_final`, axiom-checked): the record
transfers to the final run's minimum/maximum, given that every
final-run element is an old tested-run element or exceeds the
foreign element. Formalized toward discharging that proviso:
`trace_split` (factor a trace at one arrival) and the one-step
joiner barriers `insertInto_joiner_above` /
`mergePair_joiner_above`. That proviso is now discharged
(`foreign_record_final`, `foreign_record_final_succ`,
axiom-checked), via the new no-merge machinery
(`step_same_run_old`, `trace_same_run_old`, `run_unique`:
distinct old runs never merge, since steps only adjoin the
arriving element) and the blue barrier at each joining step.
Production of steps from locate and scan is proved for the mixed
case (`scan_split_step` in `StepProduction.lean`:
every Step certificate is derived from the scan witnesses and
run-order; the other three operations are named as the production
interface `step_freshSingleton_of` / `step_mergePair_of` /
`step_insertInto_of`), and a mixed scan's incidences are charged
to records (`split_scan_charged`). The expected mixed-cost bound
is now assembled in counting form (`expected_scanCost_le` in
`Assembly.lean`: expected incidences at most
`N * (2 + 2 log N)` for any charged scan-event assignment). The
one-sided Case-A configurations are located steps
(`scan_fresh_step`, `scan_append_step`); closing a model gap found
there, the step model gained an `appendSingleton` operation (a
fresh singleton after the last run), with invariant, provenance,
refinement, growth, and no-merge cases all extended. The Case-B
and Case-C located configurations are now steps
(`scan_activation_step`, `scan_attach_below`, `scan_attach_above`
in `StepProduction.lean`), and executions exist as data
(`ExecFrom` in `Execution.lean`, with `ExecFrom.events`
extracting scan events). Charged executions now cover every ordinary scan shape:
`StepCharged` includes the split scan and the four one-sided
ordinary shapes (creator at either end, activated merger on
either side of its red run), with the mirror record lemmas
`creator_record_left` and `merger_record_succ`;
`charged_events_hrec` shows every event of a charged execution
satisfies the record hypothesis of `expected_scanCost_le`, whose
distinctness hypothesis was relaxed to the per-element form an
arrival scanning two neighbors requires. Case dispatch at a
located gap is proved: `exists_step_for_arrival_interior` (with
Case-B activation outcomes separated into `StepActivation`,
which charges through founders, not records), the two end cases
`exists_step_for_arrival_left` / `_right`, and the two
end-with-candidate cases `exists_step_for_arrival_left_candidate`
/ `_right_candidate`. The located decomposition is derived from
the run list itself: `decompose_state` (induction on the run
list, alternation excluding impossible adjacencies), and
`exists_step_for_arrival_full` threads alternation
(`AltRuns`, with `alt_replace_run` / `alt_split_run` /
`alt_fresh_left` / `alt_append_right` preservation) through
every produced step. Executions assemble along any arrival
order of distinct fresh red arrivals: `exists_execution`, with
every step classified charged-or-activation
(`ExecStepsClassified`).
Founder charging for activation scans is now proved:
`activationAt_record` (the founder is a record for every blue
element its activation scans, by separation at the activation
state), `activation_events_records`, and the distinctness half —
`activationEvents_fst_nodup`: each founder is charged for a
fixed blue element at most once across the whole execution. The
dynamic argument is forward persistence (`step_same_run_forward`,
`trace_same_run_forward`: two elements in one run, the first
red, stay in one run — produced splits only split blue runs),
combined with `ExecActivationGrows` (a produced activation step
merges the founder into a pair, and a founder already in a
multi-element run can never be a singleton founder again, by
`run_unique`); `stepCharged_not_activation` shows the ordinary
and activation classifications are disjoint.
`ordinaryEvents_fst_nodup` gives the matching distinctness for
ordinary events, and `scanCost_events_eq` splits every
execution's scan cost into the two charged parts.
The final-runs lemma is `chosenExecution_final`
(`flatten_pairwise_le` plus the provenance permutation): reading
the final runs in order gives a sorted permutation of all
arrivals and the initial blue sequence; internal sortedness of
runs is maintained through the produced steps
(`RunsInternallySorted`, `runsInternallySorted_applyOp`).
The initial state (`initialRuns`: blue elements as one run) and
the rank-ordered arrival list (`arrivalsOf`) instantiate the
execution (`exists_execution_initial`); averaging the two
charged parts over the uniform ranking gives
`expected_executionEvents_le` (at most `2 * N * (2 + 2 log N)`
expected scan incidences). The total cost of the same execution
(`totalExecCost` in `TotalCost.lean`: twice the scan cost, plus
the binary-search charge, plus the blue MergeSort charge, plus
the red own and foreign charges) assembles to
`expected_totalExecCost_le` with absolute constant `100`, using
`lem:Hbounds` to charge each part to `H`; `spliceSort_main` is
this bound for the sorter `spliceSorter`, whose `run` on each
ranking is the final state of that same execution read in order.
There is no `sorry` in this project.

Probability stage (`Records.lean`, all `sorry`-free,
axiom-checked): the symmetry lemma `card_minAt_mul` (each element of
`S` is equally likely to minimize an injective arrival rank on `S`),
the counting identity `sum_card_predRecords`, the generic expected
bound `expected_le_one_add_log_of_system` (counting identity + `1/i`
symmetry + Mathlib's `harmonic_le_one_add_log`), its predecessor and
successor instantiations, and the assembled paper bound
**`recordsExpectedBound_holds`** — `lem:records` is proved, with the
explicit constant `2 + 2 / log 2`. The five scan classes are
formalized in `Cost.lean` (`ScanClass`, `classifyScan`).

Stage iii continued — step assembly and cost (`Step.lean`,
`Cost.lean`, all proved parts `sorry`-free): `scanVerdict`
with its three verdict specifications and `exists_of_mixed`;
`insertSorted` with membership/sortedness; the four-operation step
dispatch `applyOp` (`freshSingleton`/`mergePair`/`insertInto`/
`splitRun`) with full 3-part invariant preservation per operation
(`invariant_freshSingleton`, `invariant_mergePair`,
`invariant_insertInto`, `invariant_splitRun`); records in the paper's
form (`IsPredRecord`/`IsSuccRecord`/`IsRecord`); the splice pieces as
the scan's filter partition (`below_append_above_perm`, proved); and
`RecordsExpectedBound` (the `lem:records` harmonic bound) stated as a
finite-average proposition for the probability stage.

Stage iii continued (`State.lean`, all `sorry`-free):
the location step now *produces* the separation certificates the
invariant lemmas consume — `cert_left` / `cert_right` (the paper's
`lem:location`, element form, derived from `locate` + run-order);
Case C preservation `runsOrdered_replace_run`; and the mixed-scan
split preservation `runsOrdered_splice_runs` for `splice`.
Together with Case A/B this is the paper's `lem:invariant`
(run-order part) with all three cases proved.


Stage iii continued (`State.lean`, all `sorry`-free):
the run decomposition `runsOf` with `runsOf_flatten` (flattening the
runs recovers the working sequence) and `runsOf_nonempty`; the
3-part invariant as `State` (run-order, nonempty runs, red runs of
length ≥ 2 sorted); and invariant-(i) preservation for the paper's
insertion operations — `runsOrdered_insert_singleton` (Case A) and
`runsOrdered_merge_pair` (Case B) — under exactly the separation
hypotheses the paper's binary search and scans certify.

Proved in stage iii (all `sorry`-free, checked by `#print axioms`):
`benchmarkH_ge`; the SpliceSort location step `locate` (= the paper's
`k = min {j : ρⱼ > r}`) with `getElem_lt_of_lt_locate` and
`lt_getElem_locate`; and `splice` with `splice_length`
(`q_t = q_{t-1} + 1`) and `splice_take`, in
`Formalization/RandomizedLog/Algorithm.lean`.

## Build

```bash
cd "Formalized Papers/Randomized Log Bichromatic Sorting"
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

Do not run `lake update`: Lean and Mathlib are pinned to v4.35.0 by
`lean-toolchain` and `lakefile.toml`, matching the repository root.

## Trust note

Lean checks the statements *as written here*. Whether these statements
faithfully capture the paper's mathematics is a human translation audit
(cf. the Evolution Algebras formalization in this repository). The
sorter's `expectedCost` is now the expected *total* cost of the
produced execution, with the run and the cost read off the same
execution. Two accounting points to keep in view: inside
`totalExecCost`, the scan part is the execution's own event cost
(counted), and the blue monochromatic part is the counted MergeSort
comparison count on the final blue runs; but the binary-search part
enters as the paper's per-arrival charge `(#reds) · (log₂(#blues) + 1)`
and the red own part as `(log₂ N + 3)` times the red-run excess —
the charged quantities of `lem:location`/`lem:ownred`, not a
step-by-step operational counter of those individual comparisons.
The foreign red part is the counted threshold-record charge of
`lem:foreignred` at the final red runs' endpoints.

`Definitions.lean` (the shared cost model: colours, `pairCost`,
`benchmarkH`, `instSize`) is the same file as in the deterministic
paper's project; the two copies are identical and must be kept in
step.
