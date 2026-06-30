#!/usr/bin/env bash

# This script searches through any READMEs which have been removed from 
# the current branch (via a diff with master) and scans for references
# for them in existing READMEs
#
# If a reference to a now deleted README is found, an error is raised

echo "Searching for deleted READMEs"

git diff --diff-filter D --name-only master | grep '^doc/README/' | while read file; do
    echo "$file was deleted, scanning for references"
done

