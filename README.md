Landing-gate tooling for the committee port (Kev). Files are byte-identical to the copies used locally.
- tools/landing-greps.sh <worktree>: G7(i) via reach_outage.py --g7-elab, G7(ii), G8, G9, G10, G11, label gate. SECTION_S=<path> sets the §S list (default: lane path; pass tools/sectionS.md).
- tools/reach_outage.py: static/elaborated reach from the gate roots (ConsensusLean/ and Solution.lean). Fail-closed; --static-only for diagnostic runs without --g7-elab. --check-section-s lists §S entries whose header has no stock marker.
- tools/test_reach_outage.py: G10 fixtures (tools/fixtures/g10); run `python3 -m unittest tools/test_reach_outage.py`.
- tools/G7Check.lean: elaborated G7 check (positive control uses explicit ⟨S, stock⟩ after the coercion's removal).
- tools/ElabReach.lean: elaborated constant closure of both roots.
- tools/GateA.lean: gate (a) closure counts (size-premise binders, run-record stock, mayVote-stock, hmv, Fact-participationKind, §S) on both roots.
- tools/R2Check.lean: run-record stock / pinned-statement reach check.
- tools/sectionS.md: the §S (stock-only, scope-(ii)) declaration list.
- tools/sectionS-removed.md: per-entry evidence for the §S entries removed when their declarations were generalised; regenerate with tools/sectionS_removed.py.
