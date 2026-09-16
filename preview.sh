#!/usr/bin/env bash
set -euo pipefail

# Builds the notes and serves them locally, opening the browser automatically.
# The server runs detached (nohup) so it keeps running even if this terminal
# is closed - use --stop to shut it down again.
#
# Usage: ./preview.sh [port]
#        ./preview.sh --stop [port]

OUT_DIR="_out/html-multi"

if [[ "${1:-}" == "--stop" ]]; then
  PORT="${2:-8000}"
  EXISTING_PID="$(lsof -ti tcp:"$PORT" 2>/dev/null || true)"
  if [[ -n "$EXISTING_PID" ]]; then
    kill "$EXISTING_PID"
    echo "Stopped server on port $PORT (pid $EXISTING_PID)"
  else
    echo "No server running on port $PORT"
  fi
  exit 0
fi

PORT="${1:-8000}"
LOG_FILE="/tmp/ifrnotes-preview-$PORT.log"

echo "Building notes (lake exe ifrnotes)..."
lake exe ifrnotes

# Stop any previous preview server still holding this port.
EXISTING_PID="$(lsof -ti tcp:"$PORT" 2>/dev/null || true)"
if [[ -n "$EXISTING_PID" ]]; then
  echo "Stopping previous server on port $PORT (pid $EXISTING_PID)"
  kill "$EXISTING_PID" 2>/dev/null || true
  sleep 0.5
fi

echo "Starting server on http://localhost:$PORT (log: $LOG_FILE)"
(cd "$OUT_DIR" && nohup python3 -m http.server "$PORT" > "$LOG_FILE" 2>&1 &)
sleep 1

open "http://localhost:$PORT/index.html"

echo "Server is running in the background and will keep running after this terminal closes."
echo "Stop it later with: ./preview.sh --stop $PORT"
