{ stdenv, writeScriptBin, gnutar, kore-exec-prof, kore-exec-infotable, hp2pretty, eventlog2html }:

writeScriptBin "profile" ''
  #! ${stdenv.shell}
  filename=$(basename -- "$1")
  timeout="''${2:-4m}"

  mkdir -p profile
  ${gnutar}/bin/tar -xzvf "$1" -C ./profile
  cd profile
  # generate .prof and .eventlog profiles
  timeout --foreground -s INT "$timeout" env GHCRTS='-p -l-au' PATH='$PATH:${kore-exec-prof}/bin' ./kore-exec.sh
  mkdir -p ../profile-$filename
  cp kore-exec.prof ../profile-$filename/
  cp kore-exec.eventlog ../profile-$filename/prof.eventlog

  # generate a heap profile based on cost centers
  timeout --foreground -s INT "$timeout" env GHCRTS='-l -hc' PATH='$PATH:${kore-exec-prof}/bin' ./kore-exec.sh
  cp kore-exec.hp ../profile-$filename/heap-cost-centers.hp
  cp kore-exec.eventlog ../profile-$filename/heap-cost-centers.eventlog
  ${hp2pretty}/bin/hp2pretty kore-exec.hp
  ${eventlog2html}/bin/eventlog2html kore-exec.eventlog
  cp kore-exec.svg ../profile-$filename/heap-cost-centers.svg
  cp kore-exec.eventlog.html ../profile-$filename/heap-cost-centers.html

  # generate a heap profile based on infotables (GHC9)
  timeout --foreground -s INT "$timeout" env GHCRTS='-l -hi' PATH='$PATH:${kore-exec-infotable}/bin' ./kore-exec.sh
  cp kore-exec.eventlog ../profile-$filename/heap-infotables.eventlog
  ${eventlog2html}/bin/eventlog2html kore-exec.eventlog
  cp kore-exec.eventlog.html ../profile-$filename/heap-infotables.html

  cd ..
  rm -r profile
''