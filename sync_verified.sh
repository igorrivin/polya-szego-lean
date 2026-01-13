#!/bin/bash
# Sync new Aristotle-verified proofs to the repository

set -e

REPO_DIR="/home/igor/devel/heretic/polya-szego-lean"
SOURCE_DIR="/home/igor/devel/heretic/PolyaSzego"

echo "Syncing verified proofs..."

# Copy any new output files
cp -n "$SOURCE_DIR"/*-output.lean "$REPO_DIR/verified/" 2>/dev/null || true

# Update metadata
python3 << 'EOF'
import json
from pathlib import Path

progress_file = Path("/home/igor/devel/heretic/PolyaSzego/aristotle_progress.json")
metadata_file = Path("/home/igor/devel/heretic/polya-szego-lean/metadata/submissions.json")

with open(progress_file) as f:
    progress = json.load(f)

metadata = {}
for fname, info in progress.get('submitted', {}).items():
    metadata[fname] = {
        'project_id': info['project_id'],
        'submitted_at': info.get('submitted_at', ''),
        'output_file': f"{info['project_id']}-output.lean"
    }

with open(metadata_file, 'w') as f:
    json.dump(metadata, f, indent=2)

print(f"Updated metadata: {len(metadata)} submissions")
EOF

# Count files
VERIFIED=$(ls -1 "$REPO_DIR/verified/"*.lean 2>/dev/null | wc -l)
ORIGINAL=$(ls -1 "$REPO_DIR/original/"*.lean 2>/dev/null | wc -l)

echo "Repository status: $VERIFIED verified / $ORIGINAL original"

# Check for changes and commit if any
cd "$REPO_DIR"
if [[ -n $(git status --porcelain) ]]; then
    git add .
    git commit -m "Sync: $VERIFIED verified proofs ($(date +%Y-%m-%d))"
    git push
    echo "Pushed updates to GitHub"
else
    echo "No new changes to push"
fi
