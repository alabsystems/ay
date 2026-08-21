#!/bin/zsh
# Install (or remove) the nightly corpus guard as a macOS LaunchAgent.
#
# WHY launchd AND NOT A SESSION CRON: the whole point of this guard is that it
# runs when nobody is watching. A scheduler that lives inside an editor session
# dies with the session and would have caught none of the regressions that
# motivated it.
#
#   install_nightly_guard.sh            install and load
#   install_nightly_guard.sh --uninstall  unload and remove
#   install_nightly_guard.sh --status     show whether it is loaded, and last run
#
# Fires at 03:17 local. Not 03:00 -- an off-minute keeps it clear of every other
# job on the machine that rounds to the hour.
set -u
LABEL="ai.andrewyates.ay.corpus-guard"
PLIST="$HOME/Library/LaunchAgents/$LABEL.plist"
REPO="${AY_REPO:-$HOME/ay}"
# The canonical MILP gate corpus. Was $HOME/ay-corpus, which does not exist on
# this machine and never has -- so every LaunchAgent installed from this script
# baked a dead path into its plist. See scripts/milp_gate_corpus.py.
CORPUS="${AY_CORPUS:-$HOME/ay-bench/milp-gate/instances}"

case "${1:-install}" in
  --status)
    print "label:   $LABEL"
    print "plist:   $PLIST $([[ -f $PLIST ]] && print '(present)' || print '(ABSENT)')"
    launchctl list 2>/dev/null | grep -q "$LABEL" && print "loaded:  yes" || print "loaded:  no"
    # (N) is zsh's NULL_GLOB qualifier: an unmatched glob expands to nothing
    # instead of erroring, which it does on a first run before any log exists.
    latest=$(print -rl -- "$REPO"/reports/nightly/*.log(Nom) 2>/dev/null | head -1)
    if [[ -n "${latest:-}" ]]; then
      print "last run: $latest"
      tail -6 "$latest"
    else
      print "last run: none yet"
    fi
    exit 0 ;;
  --uninstall)
    launchctl unload "$PLIST" 2>/dev/null
    rm -f "$PLIST"
    print "removed $LABEL"
    exit 0 ;;
esac

mkdir -p "$HOME/Library/LaunchAgents" "$REPO/reports/nightly"
cat > "$PLIST" <<PLISTEOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key><string>$LABEL</string>
  <key>ProgramArguments</key>
  <array>
    <string>/bin/zsh</string>
    <string>$REPO/scripts/nightly_corpus_guard.sh</string>
  </array>
  <key>EnvironmentVariables</key>
  <dict>
    <key>AY_REPO</key><string>$REPO</string>
    <key>AY_CORPUS</key><string>$CORPUS</string>
    <key>PATH</key><string>$HOME/.cargo/bin:/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin</string>
  </dict>
  <key>StartCalendarInterval</key>
  <dict><key>Hour</key><integer>3</integer><key>Minute</key><integer>17</integer></dict>
  <key>StandardOutPath</key><string>$REPO/reports/nightly/launchd.out</string>
  <key>StandardErrorPath</key><string>$REPO/reports/nightly/launchd.err</string>
  <key>RunAtLoad</key><false/>
  <key>ProcessType</key><string>Background</string>
  <key>LowPriorityIO</key><true/>
  <key>Nice</key><integer>5</integer>
</dict>
</plist>
PLISTEOF

launchctl unload "$PLIST" 2>/dev/null
launchctl load "$PLIST" 2>&1 || { print "load failed"; exit 1; }
print "installed and loaded: $LABEL  (fires 03:17 local)"
print "  plist:   $PLIST"
print "  repo:    $REPO"
print "  corpus:  $CORPUS"
print "  reports: $REPO/reports/nightly/"
print "  remove:  $0 --uninstall"
