#!/usr/bin/env bash
set -euo pipefail

# --- CONFIG (edit if you ever need to) ---
SRC_DIR="${1:-_out/html-multi}"             # local build output (arg1 overrides)
DEST_HOST="${DEST_HOST:-psztxa@active-websites.cs.nott.ac.uk}"
DEST_DIR="${DEST_DIR:-public_html/comp2065.25-26.ifrnotes}"

# Set DRY_RUN=1 to preview changes without uploading.
DRY_FLAG=""
if [[ "${DRY_RUN:-0}" == "1" ]]; then
  DRY_FLAG="--dry-run -vv"
  echo "[DRY RUN] Preview only; no changes will be made."
fi

# Optional: SSH options (uncomment or tweak as needed)
# SSH_OPTS='-o StrictHostKeyChecking=accept-new'
SSH_OPTS=''

# --- PRECHECKS ---
if [[ ! -d "$SRC_DIR" ]]; then
  echo "Source directory not found: $SRC_DIR" >&2
  exit 1
fi

echo "Ensuring remote directory exists: $DEST_HOST:$DEST_DIR"
ssh $SSH_OPTS "$DEST_HOST" "mkdir -p \"$DEST_DIR\""

# --- SYNC ---
echo "Syncing: $SRC_DIR/  -->  $DEST_HOST:$DEST_DIR/"
rsync -avz --delete --progress \
  --exclude '.DS_Store' \
  --chmod=Du=rwx,Dgo=rx,Fu=rw,Fgo=r \
  $DRY_FLAG \
  -e "ssh $SSH_OPTS" \
  "$SRC_DIR"/ "$DEST_HOST":"$DEST_DIR"/

echo "Deploy complete: $DEST_HOST:$DEST_DIR"
