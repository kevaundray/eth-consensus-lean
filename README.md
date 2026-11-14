Landing-gate tooling for the committee port (Kev). Files are byte-identical to the copies used locally.
- tools/landing-greps.sh <worktree>: G7(i) via reach_outage.py --g7-elab, G7(ii), G8, G9, G10, G11, label gate. SECTION_S=<path> sets the §S list (default: lane path; pass tools/sectionS.md).
- tools/reach_outage.py: static/elaborated reach from the two gate roots.
- tools/G7Check.lean: elaborated G7 check (positive control uses explicit ⟨S, stock⟩ after the coercion's removal).
- tools/ElabReach.lean: elaborated constant closure of both roots.
- tools/GateA.lean (if present): gate (a) closure counts.
- tools/sectionS.md: the §S (stock-only, scope-(ii)) declaration list.
