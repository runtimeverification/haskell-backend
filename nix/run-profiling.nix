{ stdenv, writeScriptBin, gnutar, kore-exec-prof, kore-exec-infotable, hp2pretty, hs-speedscope, eventlog2html }:

writeScriptBin "run-profiling" ''
  #! ${stdenv.shell}
  date=`date "+%Y%m%d-%H%M%S"`
  filename=$(basename -- "$1")
  out_tar="profile-$date-$filename"

  # expects a .tar.gz extension!
  out_folder="''${out_tar%.*.*}"
  timeout="''${2:-4m}"

  mkdir -p profile
  mkdir -p $out_folder/raw
  ${gnutar}/bin/tar -xzvf "$1" -C ./profile
  cd profile

  # dump version of kore-exec for posterity
  ${kore-exec-prof}/bin/kore-exec --version > ../$out_folder/kore-exec.version

  # generate .prof and .eventlog profiles
  timeout --foreground -s INT "$timeout" env GHCRTS='-p -l-au' PATH='$PATH:${kore-exec-prof}/bin' ./kore-exec.sh
  cp kore-exec.prof ../$out_folder/
  cp kore-exec.eventlog ../$out_folder/raw/prof.eventlog
  ${hs-speedscope}/bin/hs-speedscope kore-exec.eventlog
  cp kore-exec.eventlog.json ../$out_folder/prof-speedscope.json

  # generate a heap profile based on cost centers
  timeout --foreground -s INT "$timeout" env GHCRTS='-l -hc' PATH='$PATH:${kore-exec-prof}/bin' ./kore-exec.sh
  cp kore-exec.hp ../$out_folder/raw/heap-cost-centers.hp
  cp kore-exec.eventlog ../$out_folder/raw/heap-cost-centers.eventlog
  ${hp2pretty}/bin/hp2pretty kore-exec.hp
  ${eventlog2html}/bin/eventlog2html kore-exec.eventlog
  cp kore-exec.svg ../$out_folder/heap-cost-centers.svg
  cp kore-exec.eventlog.html ../$out_folder/heap-cost-centers.html

  # generate a heap profile based on infotables (GHC9)
  timeout --foreground -s INT "$timeout" env GHCRTS='-l -hi' PATH='$PATH:${kore-exec-infotable}/bin' ./kore-exec.sh
  cp kore-exec.eventlog ../$out_folder/raw/heap-infotables.eventlog
  ${eventlog2html}/bin/eventlog2html kore-exec.eventlog
  cp kore-exec.eventlog.html ../$out_folder/heap-infotables.html

  # cleanup
  cd ..
  tar -czf $out_tar $out_folder
  rm -r profile
''