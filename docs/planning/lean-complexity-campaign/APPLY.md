# Apply this documentation overlay

## Contents and baseline

Archive: `lean-complexity-campaign-overlay-2026-11-14.zip`.

Every member is a text file under `docs/planning/lean-complexity-campaign/`. The archive adds that directory. It contains no Git patch, binary assets, dependency changes, generated Lean, production source or changes to existing planning documents.

The inspected baseline was `4291e8bd12d693fbb0d1a6a8737ed96c5f6705e3`. The new subtree was absent there. A newer working tree is acceptable if this subtree is still absent. When another agent has already created it, compare the files instead of overwriting that work.

## Inspect and unpack

The commands below assume the downloaded ZIP is in `~/Downloads`. Change only `OVERLAY` if it is elsewhere. They stop if the target already exists.

```bash
(
    set -eu
    cd ~/code/networkx_algo_common_subtree
    OVERLAY="$HOME/Downloads/lean-complexity-campaign-overlay-2026-11-14.zip"
    test -f "$OVERLAY"
    git status --short
    unzip -l "$OVERLAY"
    if test -e docs/planning/lean-complexity-campaign; then
        printf '%s\n' 'Target already exists; compare before merging this overlay.' >&2
        exit 1
    fi
    unzip -q "$OVERLAY" -d .
    (cd docs/planning/lean-complexity-campaign && sha256sum -c SHA256SUMS)
    git status --short -- docs/planning/lean-complexity-campaign
)
```

Checksums describe the delivered files before local edits. They are delivery evidence, not an instruction to maintain a checksum gate over future documentation changes. After intentional edits, the original checksum manifest no longer validates those edited files.

## Review, stage and commit only this subtree

```bash
cd ~/code/networkx_algo_common_subtree
git add -- docs/planning/lean-complexity-campaign
git diff --cached --check -- docs/planning/lean-complexity-campaign
git diff --cached --stat -- docs/planning/lean-complexity-campaign
git diff --cached -- docs/planning/lean-complexity-campaign
```

After reviewing that diff:

```bash
git commit --only \
    -m "docs: plan reusable Lean complexity proof campaign" \
    -m "Co-authored-by: GPT-6 <noreply@openai.com>" \
    -- docs/planning/lean-complexity-campaign
```

`--only` limits the commit to this subtree even if unrelated files are staged. Do not edit the subtree between review and commit. No `git add .`, reset, checkout or global manifest update is needed.

## Starting point after application

Read `README.md`, then the gap ledger, theorem dossiers and G0/G1 execution gates. The deliverable is planning and evidence. It does not add a Lake dependency, implement an algorithm or certify any new Lean theorem. The first implementation work is W01/W02 in `13-agent-work-orders.md`.
