#!/usr/bin/env bash

# This script searches through any READMEs which have
# been removed (or renamed) from the current branch 
# (via a diff with master) and scans for references
# for them in existing READMEs
#
# If a reference to a now deleted/renamed README is 
# found, an error is raised (exit code 1)
#
# Silas Hayes-Williams, 2026

echo "Searching for deleted READMEs..."

git diff --diff-filter DR --name-status master \
    | awk '{print $2}' \
    | grep '^doc/README/' \
    | while read file; do
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
    grep -r -E ".*$module([^\.].*)?$" | while read ref; do
        echo "ERROR: file referenced: $ref" >&2
        exit 1
    done
done

exit
