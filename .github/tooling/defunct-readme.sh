#!/usr/bin/env bash

# This script searches through any READMEs which have been removed from 
# the current branch (via a diff with master) and scans for references
# for them in existing READMEs
#
# If a reference to a now deleted README is found, an error is raised

echo "Searching for deleted READMEs..."

git diff --diff-filter D --name-only master | grep '^doc/README/' | while read file; do
    echo "$file was deleted, scanning for references"
   
    # remove 'doc/' and '.agda, replace / with .
    module=${file#"doc/"}
    module=${module%".agda"}
    module=${module//\//.} 
    
    # search for *any* reference to the README
    # be it an import, in a comment, or wherever else
    grep -r ".*$module.*" | while read ref; do
        echo "ERROR: file referenced: $ref" >&2
        exit 1
    done
done

exit
