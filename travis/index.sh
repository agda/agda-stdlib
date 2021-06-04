set -eu
set -o pipefail
for file in $( find src -name "*.agda" | sort ); do
  if [[ ! $( head -n 10 $file | grep -m 1 "This module is DEPRECATED" ) ]]; then
    i=$( echo $file | sed 's/src\/\(.*\)\.agda/\1/' | sed 's/\//\./g' )
    echo "import $i" >> index.agda;
  fi
done
