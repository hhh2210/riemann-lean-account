# Reading notes

These are the working notes from which the paper was written, in the order they were made.
They are published as a record, not as a second account. **Where a note and the paper
disagree, the paper is right.**

The notes were written before the dependency cone of `riemannHypothesis` was computed
(`verify/results/`). Until then, whether a declaration belonged to the proof was judged from
the source text, and almost every file of the archive imports almost every other, so the text
cannot settle it. The cone showed that several declarations the notes treat as steps of the
proof are earlier or parallel forms that the final theorem does not use. The paper's section
"What the final theorem does not use" lists them. The ones that matter most when reading the
notes:

| The notes describe | The final theorem uses instead |
|---|---|
| `AskMainBalance`, `colour_balance`, `GrowthInequalityForm`, `HostFacts` | `ch_balance`, `ch_core`, `HostFactsS` (hosts ramified at a set of primes) |
| a copy of the gain formula in another namespace | `Formalism.MainNotions.G.gU`, `g0`, `gainP` |
| `JetsInert` | `IntInert` |
| `CongruenceNumberRankThree`, `NumberSp4` | `NumberU3U_s`, `OneCharU_s` |
| `thmBGauss`, `MeanBoundSecondForm`, `DetGain`, `DetChain`, `DetBlocks`, `BesselPeriodGGP`, `lamLow_of_classicalTheorems` | see the paper, Sections 5 to 8 |

The mathematics of the unused forms is close to that of the used ones, which is why the notes
remain useful for orientation; the statements, constants and hypotheses differ.

The files:

- `spine-first-reading.md`, `second-reading-the-analytic-step.md`,
  `third-reading-the-inputs.md`: three passes over the source, from the final theorem down.
- `literature-interface.md`: the file of the archive that collects the published theorems.
- `one-page-statement-draft.md`, `audit-of-the-one-page-draft.md`: an early one-page statement
  of the argument and the audit that found its errors.
- `slices/`: reports on bounded parts of the source, made by further instances of the model.
  They located statements; every statement in the paper was then read in the source by the
  author (the paper's Appendix A records where).
