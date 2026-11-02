#!/usr/bin/env bash
set -euo pipefail

# --- CONFIG (edit if you ever need to) ---
SRC_DIR="${1:-_out/html-multi}"             # local build output (arg1 overrides)
DEST_HOST="${DEST_HOST:-psztxa@active-websites.cs.nott.ac.uk}"
DEST_DIR="${DEST_DIR:-public_html/comp2065.26-27.ifrnotes}"
# Extra files (not produced by the build) to upload alongside the site.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EXTRA_FILES=("$SCRIPT_DIR/google08d1cb966738194d.html")   # Google site verification

# Set DRY_RUN=1 to preview changes without uploading.
DRY_FLAG=""
if [[ "${DRY_RUN:-0}" == "1" ]]; then
  DRY_FLAG="--dry-run -vv"
  echo "[DRY RUN] Preview only; no changes will be made."
fi

# Reuse a single authenticated SSH connection for both the mkdir and the
# rsync below, so you only get asked for a password once per run (instead
# of once per connection). The socket is kept alive for a bit afterwards,
# so a second run shortly after this one won't prompt at all.
mkdir -p "$HOME/.ssh/controlmasters" && chmod 700 "$HOME/.ssh/controlmasters"
SSH_OPTS="-o ControlMaster=auto -o ControlPath=$HOME/.ssh/controlmasters/%r@%h:%p -o ControlPersist=10m"

# --- PRECHECKS ---
if [[ ! -d "$SRC_DIR" ]]; then
  echo "Source directory not found: $SRC_DIR" >&2
  exit 1
fi
for f in "${EXTRA_FILES[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "Extra file not found: $f" >&2
    exit 1
  fi
done

echo "Ensuring remote directory exists: $DEST_HOST:$DEST_DIR"
ssh $SSH_OPTS "$DEST_HOST" "mkdir -p \"$DEST_DIR\""

# --- SYNC ---
echo "Syncing: $SRC_DIR/  -->  $DEST_HOST:$DEST_DIR/"
rsync -avz --delete --progress \
  --exclude '.DS_Store' \
  --chmod=Du=rwx,Dgo=rx,Fu=rw,Fgo=r \
  $DRY_FLAG \
  -e "ssh $SSH_OPTS" \
  "$SRC_DIR"/ "${EXTRA_FILES[@]}" "$DEST_HOST":"$DEST_DIR"/

echo "Deploy complete: $DEST_HOST:$DEST_DIR"
