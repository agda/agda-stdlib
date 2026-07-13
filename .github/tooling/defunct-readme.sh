#!/usr/bin/env bash
set -eu
# This script searches through any READMEs which have
# been removed (or renamed) from the current branch 
# (via a diff with master) and scans for references
# for them in all files within the curretn working directory
#
# If a reference to a now deleted/renamed README is 
# found, an error is raised (exit code 1)
#
# Silas Hayes-Williams, 2026

if [[ "$1" =~ ^(-h|--help)$ ]]; then
    printf "usage: defunct-readme [-h | --help] <branch>\n\n"
    printf "Scan for all README files deleted or renamed on the
current branch (compared to <branch>) and check for references in
remaining files. An error is thrown if any reference is found.\n"
    exit
fi

echo "Searching for deleted READMEs..."

git diff --diff-filter DR --name-status $1 \
    | awk '{print $2}' \
    | grep '^doc/README/' \
    | while read -r file; do
    echo "$file was deleted, scanning for references"
   
    # remove 'doc/' and '.agda, replace / with .
    module=${file#"doc/"}
    module=${module%".agda"}
    module=${module//\//.} 
    
    # search for *any* reference to the README
    # be it an import, in a comment, or wherever 
    # else. 
    #
    # ([^\.]*)?$ says the module must be followed 
    # by *anything but* a '.' + any other text, or 
    # followed by nothing at all
    #
    # E.g. if README.A was deleted, then it would match
    #         "-- see README.A for some notes. :-)"
    #      or "-- see README.A"
    # but not "-- see README.A.Some.Sub.Module"
    grep -r -E ".*$module([^\.].*)?$" | while read -r ref; do
        echo "ERROR: file referenced: $ref" >&2
        exit 1
    done

    if [[ $? == 1 ]]; then
        exit 1
    fi
done
