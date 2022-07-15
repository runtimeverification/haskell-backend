#!/usr/bin/env bash

set -Eeuo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd -P)
current_dir=$(pwd -P)

usage() {
  cat <<EOF
Usage:
   $(basename "${BASH_SOURCE[0]}") [--help]
   $(basename "${BASH_SOURCE[0]}") [--basename NAME] [--count N] [--directory DIR] [--use-multi]

Uses 'stack repl' to generate up to 99 examples of Kore JSON files in
a directory.

By default, 20 files "sampleData/KoreJSON_[01..20].json" will be created,
the directory and name prefix can be adjusted.

IMPORTANT: The script will _overwrite_ any existing files with identical names.

Available options:

--basename  NAME  File name prefix to use (default: "KoreJSON")
--count N         How many files to create (default: 20)
--directory DIR   Target directory (default: "sampleData")
--use-multi       Include MultiOr and MultiApp (default: not included)

--help            Print this help and exit

EOF
}

die() {
    msg=${1:-"There was an error :-("}
    printf "${BASH_SOURCE[0]}: $msg\n"
    exit 1
}


# default values
target_dir="$(realpath ./sampleData)"
base_name="KoreJSON"
count=20
multi="False"

(which stack > /dev/null) || die "Unable to find stack build tool"

if [[ "$#" < 1 ]]; then
    usage
    printf "Running with defaults\n\n"
fi

# parse arguments
while [ ! -z ${1-} ]; do
    case "${1-}" in
        --help)
            usage
            exit 0
            ;;
        --basename)
            base_name=${2?"--basename: missing NAME (see --help)"}
            shift 2
            ;;
        --count)
            count=${2?"--count: missing number (see --help)"}
            shift 2
            if [[ $count -le 0 ]] || [[ $count -ge 100 ]]; then
                die "--count: must be between 1 and 99"
            fi
            ;;
        --directory)
            dir=${2?"--directory: Missing DIRNAME (see --help)"}
            shift 2
            if [ ! -d $(dirname $dir) ]; then
                die "Parent of target directory $dir does not exist"
            fi
            target_dir=$(realpath $dir)
            ;;
        --use-multi)
            multi="True"
            shift
            ;;
        -*)
            usage
            die "Option $1 not understood"
            ;;
        *)
            usage
            die "Unexpected non-option $1"
            exit 1
            ;;
    esac
done

# run the program
(cd $script_dir/.. &&
     echo "writeExamples  $multi \"$target_dir\" \"$base_name\" $count" |
         stack repl --test kore/test/Test/Kore/Syntax/Json.hs
)
